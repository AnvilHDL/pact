open Lang
open GraphBuildContext
open EventGraph

(** Build, check, and optimise the event graph for a single thread body.

    @param config   Compilation configuration (controls lt-checks, two-round,
                    disable_lt_checks flags).
    @param ci       Compilation-unit info (typedefs, channel classes, …).
    @param shared_vars_info  Shared-variable table for the enclosing process.
    @param construct_graphIR        AST→IR traversal from {!GraphBuilder}.
    @param graph    A freshly-constructed, empty event-graph skeleton for this
                    thread (thread_id, channels, regs, messages already set).
    @param e        The thread body expression to compile. *)
let build_thread config ci shared_vars_info construct_graphIR (graph : event_graph) (e : Lang.expr_node) =
  (* Round 1: optional lifetime-check pass on a disposable graph clone *)
  let graph_opt =
    if (not config.Config.disable_lt_checks) || config.Config.two_round_graph then (
      let tmp_graph = {graph with last_event_id = -1} in
      let unrolled_e =
        GraphAnalysis.recurse_unfold_for_checks construct_graphIR ci shared_vars_info graph e
      in
      let td  = construct_graphIR tmp_graph ci
        (Typing.BuildContext.create_empty tmp_graph shared_vars_info true)
        unrolled_e in
      tmp_graph.last_event_id <- (EventGraphOps.find_last_event tmp_graph).id;
      tmp_graph.is_general_recursive <- tmp_graph.last_event_id <> td.ld.lt.live.id;
      (* Optimise before lifetime check so the check sees the simplified graph *)
      let tmp_graph = GraphOpt.optimize config true ci tmp_graph in
      if not config.Config.disable_lt_checks then
        LifetimeCheck.lifetime_check config ci tmp_graph;
      if config.Config.two_round_graph then
        Some tmp_graph
      else
        None
    ) else None
  in
  (* Round 2: codegen graph (possibly reusing Round 1 result) *)
  match graph_opt with
  | Some g -> g
  | None ->
    (* discard after type checking *)
    let ctx = Typing.BuildContext.create_empty graph shared_vars_info false in
    let td  = construct_graphIR graph ci ctx e in
    graph.last_event_id <- (EventGraphOps.find_last_event graph).id;
    graph.is_general_recursive <- graph.last_event_id <> td.ld.lt.live.id;
    let g' = GraphOpt.optimize config false ci graph in
    GraphOpt.combinational_codegen config g' ci


(* Builds the graph representation for each process To Do: Add support for commands outside loop (be executed once or continuosly)*)
let build_proc (config : Config.compile_config) sched module_name param_values
              (ci' : cunit_info) (proc : proc_def) : proc_graph =
  let proc =
    if param_values = [] then
      proc
    else
      ParamConcretise.concretise_proc param_values proc
  in
  let macro_defs_extended =
    if List.length param_values <> List.length proc.params then
      raise (Except.TypeError [Text (Printf.sprintf "Expected %d parameters but got %d in %s instantation"
        (List.length proc.params) (List.length param_values) module_name)])
    else
      List.fold_left2 (fun acc (p : Lang.param) (pval : param_value) ->
        match p.param_ty, pval with
        | IntParam, IntParamValue v ->
          {
            id = p.param_name;
            value = v;
          } :: acc
        | _ -> acc
      ) ci'.macro_defs proc.params param_values 
    in

  
  let ci = {
    file_name = ci'.file_name;
    typedefs = ci'.typedefs;
    channel_classes = ci'.channel_classes;
    macro_defs = macro_defs_extended;
    func_defs = ci'.func_defs;
    session_defs = ci'.session_defs;
    weak_typecasts = ci'.weak_typecasts;
  } in

  match proc.body with
  | Native body ->
    let msg_collection = MessageCollection.create body.channels
                                      proc.args body.spawns ci.channel_classes proc.params param_values in
    let spawns =
    List.map (fun (s : spawn_def ast_node) ->
      let module_name = BuildScheduler.add_proc_task sched ci.file_name s.span s.d.proc s.d.compile_params in
      (module_name, s)
    ) body.spawns in
    let shared_vars_info = Hashtbl.create (List.length body.shared_vars) in
    List.iter (fun sv ->
      let v = {
        w = None;
        glt = sv.d.shared_lifetime;
        gdtype = unit_dtype; (* explicitly annotate? *)
      } in
      let r = {
        assigning_thread = sv.d.assigning_thread;
        value = v;
        assigned_at = None;
      } in
        Hashtbl.add shared_vars_info sv.d.ident r
      ) body.shared_vars;
      let endpoint_collection = List.map (fun (p:endpoint_def ast_node) -> (p.d.name, p.d.channel_class)) proc.args in
      let channel_local_sty = List.map (fun p -> (match (MessageCollection.lookup_channel_class ci.channel_classes (snd p)) with Some c -> c.local_sty | None -> None))endpoint_collection in

      let protocol_list =
        List.map2 (fun (ep_name, _) (sty_opt: session_type ast_node option) ->
          match sty_opt with
          | Some sty -> Some (ep_name, sty) 
          | None -> None
        ) endpoint_collection channel_local_sty
      in
      let protocol_list_filtered = List.filter Option.is_some protocol_list |> List.map Option.get in
      (* create hash table for fast lookup of endpoint name with protocol *)
      let protocol_map = Hashtbl.create (List.length protocol_list_filtered) in
      List.iter (fun (ep_name, proto) -> Hashtbl.add protocol_map ep_name proto) protocol_list_filtered;
      if (config.verbose) then Printf.eprintf "[Info] Protocol list for process %s: %s\n" module_name (String.concat ", " (List.map(fun f -> Lang.string_of_protocol (snd f).d) protocol_list_filtered));
      
      let proc_interface_protocol = 
        match proc.interface with
        | Some intf ->
          let session = List.find_opt (fun (s : session_def ast_node) -> s.d.name = intf.d) ci.session_defs
            |> unwrap_or_err ("Undefined interface " ^ intf.d) intf.span in
          Some (session.d.body)
        | None -> None
      in
      if body.threads = [] then
        raise (Except.TypeError [Text (Printf.sprintf "Process %s must have at least one thread!" proc.name)]);

      let proc_threads = List.mapi (fun i ((e, reset_by) : expr_node * message_specifier option) ->
        let graph = {
          thread_id = i;
          events = [];
          wires = WireCollection.empty;
          channels = List.map data_of_ast_node body.channels;
          messages = msg_collection;
          spawns = body.spawns;
          regs = List.map (fun (reg : Lang.reg_def ast_node) ->
                (reg.d.name, reg.d)) body.regs |> Utils.StringMap.of_list;
          last_event_id = -1;
          is_general_recursive = false;
          thread_codespan = e.span;
          comb = false;
          protocols = protocol_map;
          interface_protocol =  proc_interface_protocol;
        } in
        let g = build_thread config ci shared_vars_info GraphBuilder.construct_graphIR graph e in
        (g, reset_by)
      ) body.threads in
      {name = module_name; extern_module = None;
        threads = proc_threads; shared_vars_info; messages = msg_collection;
        proc_body = proc.body; spawns = List.map (fun (ident, spawn) -> (ident, spawn)) spawns}
    | Extern (extern_mod, _extern_body) ->
      let msg_collection = MessageCollection.create [] proc.args [] ci.channel_classes [] [] in
      {name = module_name; extern_module = Some extern_mod; threads = [];
        shared_vars_info = Hashtbl.create 0; messages = msg_collection;
        proc_body = proc.body; spawns = []}

let build (config : Config.compile_config) sched module_name param_values (cunit : compilation_unit) =
  let macro_defs = cunit.macro_defs in
  let typedefs = TypedefMap.of_list cunit.type_defs in
  let func_defs = cunit.func_defs in
  let wty = config.weak_typecasts in
  let ci = {
    file_name = Option.get cunit.cunit_file_name;
    typedefs =typedefs;
    channel_classes = cunit.channel_classes;
    session_defs = cunit.session_defs;
    macro_defs = macro_defs;
    func_defs =func_defs;
    weak_typecasts = wty
  } in

  let add_proc_args (proc : proc_def) =
    if Option.is_some proc.interface then
      let intf = Option.get proc.interface in
      let session = SessionHelper.lookup_interface cunit.session_defs intf.d
        |> unwrap_or_err ("Undefined interface " ^ intf.d) intf.span in
      let session_params = session.d.params in
      proc.args <- session_params

    in

  List.iter add_proc_args cunit.procs;



  (* Add channel defs and correct spawn def from interface and pools *)

 let lookup_channel_inst_from_pools (p : pool_inst) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
  let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = p.p_ty) p_defs in
  match pool_def_opt with
  | Some pool_def ->
      pool_def.d.pool_channels
  | None ->
    raise (Except.TypeError [Text ("Undefined interface pool " ^ p.p_id); Except.codespan_local default_span])  
  in

  let lookup_pool_inst_from_pools (id : identifier) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
    let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = id) p_defs in
    match pool_def_opt with
    | Some pool_def ->
        pool_def
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool " ^ id); Except.codespan_local default_span])
  in

  let lookup_pool_ty_from_id (id : identifier) (p_defs : (pool_inst ast_node) list) (default_span : code_span) =
    let pool_inst_opt = List.find_opt (fun (pi : pool_inst ast_node) -> pi.d.p_id = id) p_defs in
    match pool_inst_opt with
    | Some pool_inst ->
        pool_inst.d.p_ty
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool instance " ^ id); Except.codespan_local default_span])
  in


  
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
  in
    

  List.iter (fun (proc : proc_def) ->
    match proc.body with
    | Extern _ -> ()
    | Native p ->
      List.iter (fun (ps : pool_inst ast_node) ->
        let channels = lookup_channel_inst_from_pools ps.d cunit.pools ps.span in
        p.channels <- p.channels @ channels ;

          let pool_def = lookup_pool_inst_from_pools ps.d.p_ty cunit.pools ps.span in
          let session_with_ids = SessionHelper.preprocess_pool_for_compatibility pool_def cunit.session_defs in

          if not config.disable_compat_checks then
          (
              let check, err = SessionCompatiblityv3.check_compatibility_multiparty session_with_ids ps.d.p_id config.verbose in
              let ast_spans = List.map (fun ((session : session_type ast_node),_) -> Except.codespan_local session.span) session_with_ids in
              if check then Printf.eprintf "[Info] Compatibility check passed for pool instance %s in process %s\n" ps.d.p_id module_name
              else
                raise (Except.TypeError (
                  Text ("Incompatibility detected between interfaces in pool instance " ^ ps.d.p_id ^ ": " ^ err)
                  :: ast_spans
                ))
              
                
          )
      ) p.pool_insts ;

      (* Now we add the parameters of the spawn *)
      List.iter (fun (s : spawn_def ast_node) ->
        (* let interface_params =  *)
        if Option.is_some s.d.interface_params then
          let interface_params = Option.get s.d.interface_params in
          List.iter (fun ip ->
            let params = get_params_from_interface_params ip cunit.pools  p.pool_insts s.span in
            s.d.params <- s.d.params @ params
          )interface_params
      ) p.spawns

  ) cunit.procs;

  let graphs = List.map (build_proc config sched module_name param_values ci ) cunit.procs in
  {
    event_graphs = graphs;
    typedefs;
    macro_defs;
    channel_classes = cunit.channel_classes;
    external_event_graphs = [];
  }