open ParamEnv
open Lang

let rec concretise_params int_env type_env params =
  List.map (fun p ->
    match p with
    | IntParamValue _ -> p
    | TypeParamValue dtype ->
      (
        match dtype with
        | `Named (ident, []) ->
          (* this is just an identifier, might also be an int param *)
          (
            match concretise_and_get int_env (Param ident) with
            | Some n -> IntParamValue n
            | None -> TypeParamValue (concretise_dtype_params int_env type_env dtype)
          )
        | _ -> TypeParamValue (concretise_dtype_params int_env type_env dtype)
      )
  ) params
and concretise_dtype_params int_env type_env (dtype : data_type) : data_type =
  match dtype with
  | `Array (v, n) ->
    let base_type = concretise_dtype_params int_env type_env v in
    let size = match concretise int_env n with
      | Some s -> s
      | None ->
          CliOutput.error "Failed to concretise array size parameter: %s"
            (match n with
             | ParamEnv.Concrete i -> Printf.sprintf "Concrete(%d)" i
             | ParamEnv.Param p   -> Printf.sprintf "Param(%s)" p
              | ParamEnv.Expr _    -> "Expr(...)");
          failwith "Array size concretisation failed"
    in
    `Array (base_type, size)
  | `Named (ident, params) ->
    if params = [] then
      let t = Param ident in
      (
        match concretise_and_get type_env t with
        | Some v -> v
        | None -> dtype
      )
    else
      let params' = concretise_params int_env type_env params in
      `Named (ident, params')
  | `Record fields ->
    let fields' = List.map (fun (field_ident, field_dtype) ->
                        (field_ident, concretise_dtype_params int_env type_env field_dtype))
                        fields
    in
    `Record fields'
  | `Variant (dtype_opt, variants) ->
    let variants' = List.map
            (fun (var_ident, var_dtype_opt, var_val_opt) ->
              (
                var_ident,
                Option.map (concretise_dtype_params int_env type_env) var_dtype_opt,
                var_val_opt
              ))
            variants
            in
    let dtype_opt' = Option.map (concretise_dtype_params int_env type_env) dtype_opt in
    `Variant (dtype_opt', variants')
  | `Tuple elems_dtypes ->
    let elems_dtypes' = List.map (concretise_dtype_params int_env type_env) elems_dtypes in
    `Tuple elems_dtypes'
  | _ -> dtype

let build_param_envs param_values params =
  let int_env = create_env ()
  and type_env = create_env () in
  let vals_s = List.to_seq param_values
  and params_s = List.to_seq params in
  Seq.zip vals_s params_s
    |> Seq.iter
      (fun (v, p) ->
        match v, p.param_ty with
        | IntParamValue n, IntParam ->
          add_value p.param_name n int_env
        | TypeParamValue t, TypeParam ->
          add_value p.param_name t type_env
        | _ -> raise (Except.TypeError [Text ("Invalid parameter: " ^ p.param_name)])
      );
  (int_env, type_env)

let concretise_proc param_values proc =
  if proc.params = [] then
    proc
  else (
    let (int_param_env, type_param_env) = build_param_envs param_values proc.params in
    let args = List.map
      (fun ({d = a; span} : endpoint_def ast_node) ->
        let params = concretise_params int_param_env type_param_env a.channel_params in
        {d = {a with channel_params = params}; span}
      ) proc.args in
    (
      match proc.body with
      | Extern _ -> proc
      | Native body ->
        let regs = List.map
          (fun {d = r; span} -> {d = {r with d_type = concretise_dtype_params int_param_env type_param_env r.d_type}; span})
          body.regs in
        let spawns = List.map
          (fun {d = sp; span} ->
            let compile_params = concretise_params int_param_env type_param_env sp.compile_params in
            {d = {sp with compile_params}; span}
          )
          body.spawns in
        let channels = List.map
          (fun {d = ch; span} ->
            let params = concretise_params int_param_env type_param_env ch.channel_params in
            {d = {ch with channel_params = params}; span}
          )
          body.channels in
        {proc with args; body = Native {body with regs; spawns; channels}}
    )
  )

let concretise_dtype params param_values =
  let (int_param_env, type_param_env) = build_param_envs param_values params in
  concretise_dtype_params int_param_env type_param_env

let concretise_message params param_values (msg : Lang.message_def) =
  let (int_param_env, type_param_env) = build_param_envs param_values params in
  let sig_types = List.map
    (fun (stype : Lang.sig_type_chan_local) ->
      {stype with dtype = concretise_dtype_params int_param_env type_param_env stype.dtype}
    )
    msg.sig_types
  in
  {msg with sig_types}


let concretise_array_dimm params param_values (dimm : Lang.array_dimensions) : array_dimm_concrete =
  let (int_param_env, _) = build_param_envs param_values params in
  let mappings = ParamEnv.map_list (fun k v ->
    Printf.sprintf "%s : %d\n" k v
  ) int_param_env in
  let mappings = String.concat "" mappings in

  (* Evaluate a compile-time param_expr by substituting params from the environment *)
  let rec eval_param_expr (pe : ParamEnv.param_expr) : int =
    match pe with
    | ParamEnv.PE_Int n -> n
    | ParamEnv.PE_Id  id ->
        (match ParamEnv.concretise_and_get int_param_env (ParamEnv.Param id) with
         | Some v -> v
         | None   ->
             CliOutput.error "Unknown parameter '%s' in array size expression | Current Mappings = %s" id mappings;
             failwith ("Unknown parameter in array size expression: " ^ id))
    | ParamEnv.PE_Add (e1, e2) -> eval_param_expr e1 + eval_param_expr e2
    | ParamEnv.PE_Sub (e1, e2) -> eval_param_expr e1 - eval_param_expr e2
    | ParamEnv.PE_Mul (e1, e2) -> eval_param_expr e1 * eval_param_expr e2
    | ParamEnv.PE_Div (e1, e2) ->
        let d = eval_param_expr e2 in
        if d = 0 then failwith "Division by zero in array size expression"
        else eval_param_expr e1 / d
  in

  let show_param n =
    match n with
    | ParamEnv.Concrete i -> Printf.sprintf "Concrete(%d)" i
    | ParamEnv.Param    p -> Printf.sprintf "Param(%s)" p
    | ParamEnv.Expr     _ -> "Expr(...)"
  in

  let get_concrete_params n =
    match ParamEnv.get_opt n with
    | Some v -> v
    | None   -> failwith "Unreachable : Please report bug"
  in

  (* Unify resolution of Concrete, Param, and Expr into a Concrete result *)
  let resolve_dim n =
    match n with
    | ParamEnv.Expr pe ->
        ParamEnv.Concrete (eval_param_expr pe)
    | _ ->
        (match concretise_and_get int_param_env n with
         | Some v -> ParamEnv.Concrete v
         | None   ->
             CliOutput.error "Failed to concretise array dimension parameter: %s | Current Mappings = %s"
               (show_param n) mappings;
             failwith "Array dimension concretisation failed")
  in

  let rec concretise_dimm dimm =
    match dimm with
    | Lang.OneDim n ->
        Lang.OneDimmension (get_concrete_params (resolve_dim n))
    | Lang.MultiDim (n, rest) ->
        let rest' = concretise_dimm rest in
        Lang.MultiDimmension (get_concrete_params (resolve_dim n), rest')
  in
  concretise_dimm dimm