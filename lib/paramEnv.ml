(** A compile-time evaluatable integer expression, used as array dimension sizes. *)
type param_expr =
  | PE_Int of int                        (** integer constant *)
  | PE_Id  of string                     (** named macro or int parameter *)
  | PE_Add of param_expr * param_expr    (** addition *)
  | PE_Sub of param_expr * param_expr    (** subtraction *)
  | PE_Mul of param_expr * param_expr    (** multiplication *)
  | PE_Div of param_expr * param_expr    (** integer division *)

type 'a maybe_param =
  | Param    of string   (** a named compile-time parameter *)
  | Concrete of 'a       (** a concrete (known) value *)
  | Expr     of param_expr (** a compile-time arithmetic expression (only valid for int) *)

module ParamEnvTbl = Hashtbl.Make(String)

type 'a param_env = 'a ParamEnvTbl.t

let create_env () = ParamEnvTbl.create 8

let add_value s v env =
  ParamEnvTbl.add env s v

let concretise env p =
  match p with
  | Concrete _ -> Some p
  | Expr _     -> Some p   (* expressions are self-contained; evaluated elsewhere *)
  | Param param_ident ->
    ParamEnvTbl.find_opt env param_ident
      |> Option.map (fun v -> Concrete v)

let get_opt p =
  match p with
  | Concrete v -> Some v
  | Param _    -> None
  | Expr _     -> None   (* needs evaluate_param_expr from TypedefMap *)

let concretise_and_get env p =
  let n = concretise env p in
  Option.bind n get_opt

let iter f env = ParamEnvTbl.iter f env

let map_list f env = 
  let res = ref [] in
  ParamEnvTbl.iter (fun k v -> res := (f k v) :: !res) env;
  List.rev !res