open Lang


let lookup_interface (interfaces : session_def ast_node list) (intf : identifier) : session_def ast_node option =
    List.find_opt (fun (s:session_def ast_node) -> s.d.name = intf) interfaces


let rec highest_level_endpoint (session_type : session_type) : identifier list =
    
    match session_type with
    | StyAtom (AtomicAct (AtomNBMsg m)) -> [m.endpoint]
    | StyAtom (AtomicAct (AtomBMsg m)) -> [m.endpoint]
    | StyAtom (AtomDelay _) -> []
    | StySeq (s1, s2) | StyParallel (s1, s2) | StyChoice (s1, s2) -> (match highest_level_endpoint s1 with
        | [] -> highest_level_endpoint s2
        | eps1 -> eps1 @ highest_level_endpoint s2
    )
    | StyOffer ps | StyXOffer ps ->
        (
        let endpoints = List.flatten (List.map (fun oty ->
            match oty.trigger with
            | AtomicAct (AtomNBMsg m) -> [m.endpoint]
            | AtomicAct (AtomBMsg m) -> [m.endpoint]
            | AtomDelay _ -> []
            | _ -> raise (Except.TypeError [Text ("Unsupported atomic action in highest level endpoint extraction"^(string_of_atomic_action_with_gap oty.trigger))])
        ) ps) in
        let endpoints_continuation = List.flatten (List.map (fun oty ->
            match oty.continuation with
            | Some cont -> highest_level_endpoint cont
            | None -> []
        ) ps) in
        endpoints @ endpoints_continuation
        )

    | StyFuture s -> highest_level_endpoint s
    | StyTrue -> []
    | StyRec (_, ty) -> highest_level_endpoint ty
    | StyVar _ -> []
    | StyLet (_, s1, s2) -> highest_level_endpoint s1 @ highest_level_endpoint s2
    | _ -> []
    

 let lookup_channel_inst_from_pools (p : pool_inst) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
  let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = p.p_ty) p_defs in
  match pool_def_opt with
  | Some pool_def ->
      pool_def.d.pool_channels
  | None ->
    raise (Except.TypeError [Text ("Undefined interface pool " ^ p.p_id); Except.codespan_local default_span])  


  let lookup_pool_inst_from_pools (id : identifier) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
    let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = id) p_defs in
    match pool_def_opt with
    | Some pool_def ->
        pool_def
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool " ^ id); Except.codespan_local default_span])


  let lookup_pool_ty_from_id (id : identifier) (p_defs : (pool_inst ast_node) list) (default_span : code_span) =
    let pool_inst_opt = List.find_opt (fun (pi : pool_inst ast_node) -> pi.d.p_id = id) p_defs in
    match pool_inst_opt with
    | Some pool_inst ->
        pool_inst.d.p_ty
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool instance " ^ id); Except.codespan_local default_span])


  
  let get_params_from_interface_params (ip : ifc_instantiation) (p_defs : (interface_pool_def ast_node) list) (ifc_list : (pool_inst ast_node) list) (default_span : code_span) =
    let pi = lookup_pool_ty_from_id ip.pid ifc_list default_span in
    let pool_def = lookup_pool_inst_from_pools pi p_defs default_span in
    let interface_opt = List.find_opt (fun p -> p.d.inf_mem_id = ip.pifc_id) pool_def.d.interface_members in
    match interface_opt with
    | Some interface_member ->
      (
        match interface_member.d.interface_class_id with
        | Some intf_id ->
          List.map (fun param -> Lang.SingleEp param) intf_id.params
        | None ->
          raise (Except.TypeError [Text ("Currently only interface instantiation is supported in pool members, but got none for " ^ ip.pifc_id ^ " in pool " ^ ip.pid); Except.codespan_local default_span])
      )
    | None ->
      raise (Except.TypeError [Text ("Undefined interface member " ^ ip.pifc_id ^ " in pool " ^ ip.pid); Except.codespan_local default_span])
    
  let lookup_session_types_from_pool_inst (id : identifier) (p_defs : (interface_pool_def ast_node) list) (s_defs : (session_def ast_node)list) (default_span : code_span) =
    let pool_def = lookup_pool_inst_from_pools id p_defs default_span in

    let session_defs = List.map (fun im ->
      match im.d.interface_class_id with
      | Some intf_id ->
        (
          let session_opt = lookup_interface s_defs intf_id.id in
          match session_opt with
          | Some session -> (session.d.body, intf_id.id)
          | None ->
            raise (Except.TypeError [Text ("Undefined Session type " ^ intf_id.id ^ " in pool member " ^ im.d.inf_mem_id); Except.codespan_local default_span])
        )
      | None ->
        raise (Except.TypeError [Text ("Currently only interface instantiation is supported in pool members, but got none for " ^ im.d.inf_mem_id ^ " in pool " ^ id);
          Except.codespan_local default_span])

    ) pool_def.d.interface_members in
    session_defs


(* === Quantifier Expansion Functions === *)

(* Substitute a quantified variable with a concrete integer value in a session type *)
(* This function respects nested quantifier scopes - inner variables shadow outer ones *)

let subsitute_action (action : atomic_action_with_gap) var_name value  =
    (
     match action with
     | AtomicAct (AtomNBMsg msg_spec) ->
          let new_endpoint = Lang.sub_ep_index msg_spec value var_name in
          AtomicAct (AtomNBMsg new_endpoint)
     | AtomicAct (AtomBMsg msg_spec) ->
          let new_endpoint = Lang.sub_ep_index msg_spec value var_name in
          AtomicAct (AtomBMsg new_endpoint)
     | _ ->  action
     )


let rec substitute_quantified_var (var_name : identifier) (value : int) (sty : session_type) : session_type =
  match sty with
  | StySeq (s1, s2) -> 
      StySeq (substitute_quantified_var var_name value s1, 
              substitute_quantified_var var_name value s2)
  | StyChoice (s1, s2) -> 
      StyChoice (substitute_quantified_var var_name value s1, 
                 substitute_quantified_var var_name value s2)
  | StyParallel (s1, s2) -> 
      StyParallel (substitute_quantified_var var_name value s1, 
                   substitute_quantified_var var_name value s2)
  | StyFuture s -> 
      StyFuture (substitute_quantified_var var_name value s)
  | StyAtom action -> 
    StyAtom (subsitute_action action var_name value)
  | StyXOffer offerings ->
      let subst_offering (off : offering_session_type) : offering_session_type =
        {
          trigger = subsitute_action off.trigger var_name value;
          continuation = Option.map (substitute_quantified_var var_name value) off.continuation;
        }
      in
      StyXOffer (List.map subst_offering offerings)
  | StyOffer offerings ->
      let subst_offering (off : offering_session_type) : offering_session_type =
        {
          trigger = subsitute_action off.trigger var_name value;
          continuation = Option.map (substitute_quantified_var var_name value) off.continuation;
        }
      in
      StyOffer (List.map subst_offering offerings)
  | StyTrue -> StyTrue
  | StyRec (id, s) -> 
      StyRec (id, substitute_quantified_var var_name value s)
  | StyVar id -> 
      StyVar id
  | StyLet (id, s1, s2) -> 
      StyLet (id, 
              substitute_quantified_var var_name value s1, 
              substitute_quantified_var var_name value s2)
  | StyForall (op, id, qty, body, ex) ->
      if id = var_name then
        StyForall (op, id, qty, body, ex)  (* Inner shadows outer - no substitution *)
      else
        StyForall (op, id, qty, substitute_quantified_var var_name value body, ex)


(* Generate list of values from quantifier range, excluding specified members *)
let generate_quantifier_values (qty : quant_type) (exclusions : quant_member option) : int list =
  match qty with
  | QuantRange (start, end_val) ->
      let all_values = List.init (end_val - start + 1) (fun i -> start + i) in
      match exclusions with
      | None -> all_values
      | Some (QuantSingleInt excluded) ->
          List.filter (fun v -> v <> excluded) all_values
      | Some (QuantIntList excluded_list) ->
          let excluded_set = List.fold_left (fun set v -> Utils.IntSet.add v set) 
                                           Utils.IntSet.empty excluded_list in
          List.filter (fun v -> not (Utils.IntSet.mem v excluded_set)) all_values


(* Expand a single quantifier, combining instances based on operator *)
let expand_single_quantifier 
    (op : quant_operator) 
    (var_name : identifier) 
    (qty : quant_type) 
    (body : session_type) 
    (exclusions : quant_member option) : session_type =
  
  let () = match qty with
    | QuantRange (start, end_val) ->
        if start > end_val then
          raise (Except.TypeError [Text (Printf.sprintf 
            "Invalid quantifier range [%d..%d]: start must be <= end" start end_val)])
  in
  
  let values = generate_quantifier_values qty exclusions in
  
  if values = [] then
    StyTrue
  else
    let instances = List.map (fun v -> substitute_quantified_var var_name v body) values in
    

    match op with
    | QuantSum ->
        let rec unfold_sum lst =
          match lst with
          | [] -> StyTrue
          | [x] -> x
          | x::xs -> StyChoice (x, unfold_sum xs)
        in
        unfold_sum instances
    
    | QuantProduct ->
        let rec unfold_prod lst =
          match lst with
          | [] -> StyTrue
          | [x] -> x
          | x::xs -> StyParallel (x, unfold_prod xs)
        in
        unfold_prod instances
    
    | QuantOffer ->
        raise (Except.TypeError [Text 
          "Quantifier with offer operator (∧) not yet fully implemented"])
    
    | QuantXOffer ->
        raise (Except.TypeError [Text 
          "Quantifier with xoffer operator (⊕) not yet fully implemented"])


(* Recursively expand all quantifiers in a session type *)
let rec expand_quantifiers (sty : session_type) : session_type =
  match sty with
  | StySeq (s1, s2) -> 
      StySeq (expand_quantifiers s1, expand_quantifiers s2)
  | StyChoice (s1, s2) -> 
      StyChoice (expand_quantifiers s1, expand_quantifiers s2)
  | StyParallel (s1, s2) -> 
      StyParallel (expand_quantifiers s1, expand_quantifiers s2)
  | StyFuture s -> 
      StyFuture (expand_quantifiers s)
  | StyAtom _ -> 
      sty
  | StyXOffer offerings ->
      let expand_offering (off : offering_session_type) : offering_session_type =
        {
          trigger = off.trigger;
          continuation = Option.map expand_quantifiers off.continuation;
        }
      in
      StyXOffer (List.map expand_offering offerings)
  | StyOffer offerings ->
      let expand_offering (off : offering_session_type) : offering_session_type =
        {
          trigger = off.trigger;
          continuation = Option.map expand_quantifiers off.continuation;
        }
      in
      StyOffer (List.map expand_offering offerings)
  | StyTrue -> StyTrue
  | StyRec (id, s) -> 
      StyRec (id, expand_quantifiers s)
  | StyVar id -> 
      StyVar id
  | StyLet (id, s1, s2) -> 
      StyLet (id, expand_quantifiers s1, expand_quantifiers s2)
  | StyForall (op, var_name, qty, body, exclusions) ->
      (* First, recursively expand any nested quantifiers in the body *)
      let expanded_body = expand_quantifiers body in
      (* Then expand this quantifier *)
      expand_single_quantifier op var_name qty expanded_body exclusions
    

      
(* === End Quantifier Expansion Functions === *)

      

(* Preprocess session types to replace interface parameters with actual endpoint names *)
let preprocess_session_type endpoint_mapping (sty : Lang.session_type) : Lang.session_type =
  let replace_endpoint_in_msg_spec (msg_spec : Lang.message_specifier) : Lang.message_specifier =
    match Utils.StringMap.find_opt msg_spec.endpoint endpoint_mapping with
    | Some new_endpoint -> {msg_spec with endpoint = new_endpoint}
    | None -> msg_spec
  in

  let replace_in_atomic_action (action : Lang.atomic_action) : Lang.atomic_action =
    match action with
    | Lang.AtomBMsg msg_spec -> Lang.AtomBMsg (replace_endpoint_in_msg_spec msg_spec)
    | Lang.AtomNBMsg msg_spec -> Lang.AtomNBMsg (replace_endpoint_in_msg_spec msg_spec)
  in

  let rec replace_in_action_with_gap (action : Lang.atomic_action_with_gap) : Lang.atomic_action_with_gap =
    match action with
    | Lang.AtomDelay n -> Lang.AtomDelay n
    | Lang.AtomicAct atomic -> Lang.AtomicAct (replace_in_atomic_action atomic)
    | AtomTerminal sty -> AtomTerminal (preprocess_sty sty)
  
  and preprocess_sty (sty : Lang.session_type) : Lang.session_type =
    match sty with
    | Lang.StySeq (s1, s2) -> Lang.StySeq (preprocess_sty s1, preprocess_sty s2)
    | Lang.StyChoice (s1, s2) -> Lang.StyChoice (preprocess_sty s1, preprocess_sty s2)
    | Lang.StyParallel (s1, s2) -> Lang.StyParallel (preprocess_sty s1, preprocess_sty s2)
    | Lang.StyFuture s -> Lang.StyFuture (preprocess_sty s)
    | Lang.StyAtom action -> Lang.StyAtom (replace_in_action_with_gap action)
    | Lang.StyXOffer offerings ->
        let process_offering (off : Lang.offering_session_type) : Lang.offering_session_type =
          {
            trigger = replace_in_action_with_gap off.trigger;
            continuation = Option.map preprocess_sty off.continuation;
          }
        in
        Lang.StyXOffer (List.map process_offering offerings)
    | Lang.StyOffer offerings ->
        let process_offering (off : Lang.offering_session_type) : Lang.offering_session_type =
          {
            trigger = replace_in_action_with_gap off.trigger;
            continuation = Option.map preprocess_sty off.continuation;
          }
        in
        Lang.StyOffer (List.map process_offering offerings)
    | Lang.StyTrue -> Lang.StyTrue
    | Lang.StyRec (id, s) -> Lang.StyRec (id, preprocess_sty s)
    | Lang.StyVar id -> Lang.StyVar id
    | Lang.StyLet (id, s1, s2) -> Lang.StyLet (id, preprocess_sty s1, preprocess_sty s2)
    | Lang.StyForall (op, id, qty, sty_body, ex) ->
        let preprocessed_body = preprocess_sty sty_body in
        Lang.StyForall (op, id, qty, preprocessed_body, ex)
  in
  let preprocessed = preprocess_sty sty in
  (* After endpoint substitution, expand all quantifiers *)
  expand_quantifiers preprocessed

let expand_session_type_quantifiers (sty : Lang.session_type) : Lang.session_type =
  expand_quantifiers sty



let build_endpoint_mapping 
    (interface_member : interface_mem_def ast_node) 
    (pool_channels : channel_def ast_node list)
    (session_defs : session_def ast_node list)
    : identifier Utils.string_map =
  match interface_member.d.interface_class_id with
  | Some intf_inst ->
      (* Look up the interface definition to get parameter names *)
      let interface_opt = lookup_interface session_defs intf_inst.id in
      (match interface_opt with
      | Some interface_def ->
          let endpoint_param_names = List.map (fun (ep : Lang.endpoint_def ast_node) -> ep.d.name) interface_def.d.params in
          let actual_endpoints = intf_inst.params in
          

          if List.length endpoint_param_names <> List.length actual_endpoints then
            raise (Except.TypeError [
              Text (Printf.sprintf "Interface instantiation parameter mismatch: interface '%s' expects %d parameters but got %d arguments" 
                intf_inst.id 
                (List.length endpoint_param_names) 
                (List.length actual_endpoints));
              Except.codespan_local interface_member.span
            ]);
          

          let actual_endpoints_set = List.fold_left (fun set ep ->
            Utils.StringSet.add ep set
          ) Utils.StringSet.empty actual_endpoints in
          

          let relevant_unification_map = List.fold_left (fun map (chan : Lang.channel_def ast_node) ->
            let left_used = Utils.StringSet.mem chan.d.endpoint_left actual_endpoints_set in
            let right_used = Utils.StringSet.mem chan.d.endpoint_right actual_endpoints_set in
            if left_used || right_used then
              (* At least one endpoint is used - unify both to left *)
              Utils.StringMap.add chan.d.endpoint_right chan.d.endpoint_left map
            else
              map
          ) Utils.StringMap.empty pool_channels in
          
          let base_mapping = List.fold_left2 (fun map param_name actual_ep ->
            let unified_ep = match Utils.StringMap.find_opt actual_ep relevant_unification_map with
              | Some left_ep -> left_ep  (* actual_ep is a right endpoint, use left instead *)
              | None -> actual_ep        (* actual_ep is already a left endpoint or standalone *)
            in
            Utils.StringMap.add param_name unified_ep map
          ) Utils.StringMap.empty endpoint_param_names actual_endpoints in
          
          Utils.StringMap.fold Utils.StringMap.add relevant_unification_map base_mapping
      | None -> Utils.StringMap.empty)
  | None -> Utils.StringMap.empty


let preprocess_pool_for_compatibility 
    (pool_def : interface_pool_def ast_node)
    (session_defs : session_def ast_node list)
    : ((session_type ast_node) * identifier) list =

  let pool_channels = pool_def.d.pool_channels in
  
  List.filter_map (fun (intf_member : interface_mem_def ast_node) ->

    match intf_member.d.interface_def with
    | Some session_ty ->
        let endpoint_mapping = build_endpoint_mapping intf_member pool_channels session_defs in
    
        let preprocessed_sty = preprocess_session_type endpoint_mapping session_ty in
        
        Some ({d = preprocessed_sty; span = intf_member.span}, intf_member.d.inf_mem_id)
    | None ->
        (match intf_member.d.interface_class_id with
        | Some intf_inst ->
            let interface_opt = lookup_interface session_defs intf_inst.id in
            (match interface_opt with
            | Some interface_def ->
                let endpoint_mapping = build_endpoint_mapping intf_member pool_channels session_defs in
                
                let session_ty = interface_def.d.body.d in
                

                let preprocessed_sty = preprocess_session_type endpoint_mapping session_ty in
                
                Some ({d = preprocessed_sty; span = intf_member.span}, intf_member.d.inf_mem_id)
            | None ->
                raise (Except.TypeError [Text ("Undefined Session type " ^ intf_inst.id ^ " in pool member " ^ intf_member.d.inf_mem_id);
                  Except.codespan_local intf_member.span])
                )
        | None ->
            raise (Except.TypeError [Text ("Neither interface definition nor instantiation found for pool member " ^ intf_member.d.inf_mem_id);
              Except.codespan_local intf_member.span])
        )
  ) pool_def.d.interface_members
