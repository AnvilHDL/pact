exception CompileError of Except.error_message

let raise_compile_error file_name msg =
  let open Except in
  let msg = match file_name with
  | Some file_name -> List.map (fun frag ->
      match frag with
      | Codespan (None, codespan) -> Codespan (Some file_name, codespan)
      | _ -> frag
    ) msg
  | None -> msg
  in
  raise (CompileError msg)

let canonicalise_file_name file_origin file_name =
  if Filename.is_relative file_name then
    Filename.concat (Filename.dirname file_origin) file_name
  else
    file_name

let rec parse_recursive cunits parsed_files config filename =
  if Utils.StringSet.mem filename !parsed_files |> not then (
    parsed_files := Utils.StringSet.add filename !parsed_files;
    let cunit =
      try
        In_channel.with_open_bin
          filename
          (fun in_channel ->
            let lexbuf = Lexing.from_channel in_channel in
            try Parser.cunit Lexer.read lexbuf
            with
              | Lexer.SyntaxError msg ->
                let open Except in
                [
                  (Text "Syntax error:");
                  (Text msg);
                  (Codespan (Some filename, {st = Lexing.lexeme_start_p lexbuf; ed = Lexing.lexeme_end_p lexbuf}))
                ] |> raise_compile_error (Some filename)
              | _ ->
                let open Except in
                [
                  (Text "Syntax error");
                  (Codespan (Some filename, {st = Lexing.lexeme_start_p lexbuf; ed = Lexing.lexeme_end_p lexbuf}))
                ] |> raise_compile_error (Some filename)
          )
      with
        | Sys_error msg ->
          raise_compile_error (Some filename) [Except.Text msg]
    in
    let cunit = {cunit with cunit_file_name = Some filename} in
    (
      try
        GraphBuilder.syntax_tree_precheck config cunit
      with
        | Except.TypeError msg -> raise_compile_error (Some filename) msg
    );
    cunits := (filename, cunit)::!cunits;
    List.iter (fun imp ->
      let open Lang in
      if not imp.is_extern then
        canonicalise_file_name filename imp.file_name
          |> parse_recursive cunits parsed_files config
    ) cunit.imports
  )

let rely_guarantee_debug _out config  =
  let toplevel_filename = List.hd config.Config.input_filenames in
  let cunits = ref [] in
  (
    try parse_recursive cunits (ref Utils.StringSet.empty) config toplevel_filename
    with
      | Except.TypeError msg ->
        (Except.Text "Type error:")::msg
          |> raise_compile_error None
  );
  let session_type_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.session_defs) !cunits in
    let open Lang in
    let open SessionCompatiblityv2 in
  List.iter (fun (sdef :Lang.session_def Lang.ast_node) ->

    let sty_str = string_of_protocol sdef.d.body.d in
    Printf.eprintf "Session Type %s: %s \n" sdef.d.name sty_str;
    Printf.eprintf "\nReliability %s\n\n" (string_of_rgcollections (constructReliabilityCollection sdef.d.body.d));
    Printf.eprintf "\nGuarantee %s\n\n" (string_of_rgcollections (constructGuaranteeCollection sdef.d.body.d));
  )session_type_defs;
  Printf.eprintf "\nPool Compatiblity Checks:\n\n";

  let pools = List.concat_map (fun (_, cunit) -> let open Lang in cunit.pools) !cunits in
  List.iter (fun (pool : Lang.interface_pool_def Lang.ast_node) ->
      let open Lang in
      let open SessionCompatiblityv2 in
     Printf.eprintf "Pool %s: \n" pool.d.pool_id;
      if List.length pool.d.interface_members > 1 then
        (
          let open SessionCompatiblityv2 in
        let (check, msg) = check_compatibility_multiparty pool config.verbose_max in
        Printf.eprintf "[Multiparty Compatibility]: %b \n\n" (check);
        Printf.eprintf "Message: %s \n\n" (msg);
        )
      else 
        (
        let im1 = List.nth pool.d.interface_members 0 in
        let im2 = List.nth pool.d.interface_members 1 in
        if im1.d.interface_def = None || im2.d.interface_def = None then
          raise (Failure "Unimplemented: pool interface members without interface definitions");
        let im1_sty = Option.get im1.d.interface_def in
        let im2_sty = Option.get im2.d.interface_def in
        Printf.eprintf "Interface Member 1: %s \n\n" (string_of_protocol im1_sty);
        Printf.eprintf "Interface Member 2: %s \n\n" (string_of_protocol im2_sty);
        Printf.eprintf "Reliability 1: %s \n\n" (string_of_rgcollections (constructReliabilityCollection im1_sty));
        Printf.eprintf "Guarantee 2: %s \n\n" (string_of_rgcollections (constructGuaranteeCollection im2_sty));
        Printf.eprintf "Reliability 2: %s \n\n" (string_of_rgcollections (constructReliabilityCollection im2_sty));
        Printf.eprintf "Guarantee 1: %s \n\n" (string_of_rgcollections (constructGuaranteeCollection im1_sty));
        let compatiblity = 
          compatiblity_check_binary
            {d = im1_sty; span = pool.span}
            {d = im2_sty; span = pool.span} in
        Printf.eprintf "[Compatibility]: %b \n\n" (compatiblity)
        )
  )pools;

  Printf.eprintf "\n"


let generalized_type_debug _out config =
  let toplevel_filename = List.hd config.Config.input_filenames in
  let cunits = ref [] in
  (
    try parse_recursive cunits (ref Utils.StringSet.empty) config toplevel_filename
    with
      | Except.TypeError msg ->
        (Except.Text "Type error:")::msg
          |> raise_compile_error None
  );
  let session_type_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.session_defs) !cunits in
    let open Lang in
    if config.verbose then Printf.eprintf "\nGeneralized Types:\n\n";
  if config.verbose then
    List.iter (fun (sdef :Lang.session_def Lang.ast_node) ->
      Printf.eprintf "Session Type %s: %s \n" sdef.d.name (string_of_protocol sdef.d.body.d);
    ) session_type_defs;
    

  let open SessionBuildAutomaton in
  let open SessionAutomaton in

  if config.verbose then Printf.eprintf "\nGenerating Generalized Types as DOT files...\n\n";
  List.iter(
    fun (sdef :Lang.session_def Lang.ast_node) ->
        let gen_type = build_automaton None sdef.d.body.d sdef.d.body.span in 
        let out_channel = Printf.sprintf "generalized_type_%s.dot" sdef.d.name in
        let out = open_out out_channel in
        print_automaton_dot gen_type out;
        close_out out
  )session_type_defs;

  (* check compatibility *)
  let pool_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.pools) !cunits in
  if config.verbose then Printf.eprintf "\nPool Compatiblity Checks:\n\n";
  List.iter (fun (pool : Lang.interface_pool_def Lang.ast_node) ->
if config.verbose then
    Printf.eprintf "Checking Pool %s  \n" pool.d.pool_id;
    let open SessionCompatiblityv3 in
    
    (* Preprocess the pool to get session_ids with unified endpoints *)
    let session_ids = SessionHelper.preprocess_pool_for_compatibility 
        pool session_type_defs in

      (* Printf.eprintf "Session IDs in Pool %s: \n" pool.d.pool_id;
      List.iter (fun (st_node, intf_id) ->
        Printf.eprintf "- Interface %s : %s \n" intf_id (string_of_protocol st_node.d)
      ) session_ids; *)
    
    let compat, err = try check_compatibility_multiparty session_ids pool.d.pool_id config.verbose
      with
      | Except.TypeError msg ->
        (false, List.filter_map (fun x -> match x with Except.Text msg -> Some msg | _ -> None) msg |> String.concat "; ")
      | Failure msg -> (false, msg)
    in
    Printf.eprintf "Pool %s Compatibility: %b | err_msg = %s \n" pool.d.pool_id compat err;
  ) pool_defs;
  Printf.eprintf "\n"

let profile_compatibility_checks _out config =
  let toplevel_filename = List.hd config.Config.input_filenames in
  let cunits = ref [] in
  (
    try parse_recursive cunits (ref Utils.StringSet.empty) config toplevel_filename
    with
      | Except.TypeError msg ->
        (Except.Text "Type error:")::msg
          |> raise_compile_error None
  );
  let session_type_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.session_defs) !cunits in
  let pool_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.pools) !cunits in
  
  Printf.eprintf "\n=== Profiling Compatibility Checks ===\n\n";
  
  (* CSV output - append mode to accumulate results across runs *)
  let file_base_name = toplevel_filename |> Filename.basename |> Filename.remove_extension in
  let csv_filename = file_base_name^"_compatibility_profile.csv" in
  let file_exists = Sys.file_exists csv_filename in
  
  (* Write header only if file is new/empty *)
  if not file_exists then (
    let csv_header = open_out csv_filename in
    Printf.fprintf csv_header "pool_name,num_automata,individual_sizes,theoretical_state_space,actual_state_space,visited_states,product_transitions,state_space_ratio,construction_time_ms,game_time_ms,total_time_ms,result,error_msg\n";
    close_out csv_header
  );
  
  
  List.iter (fun (pool : Lang.interface_pool_def Lang.ast_node) ->
    Printf.eprintf "Profiling Pool %s...\n" pool.d.pool_id;
    
    let session_ids = SessionHelper.preprocess_pool_for_compatibility pool session_type_defs in
    
    let start_time = Unix.gettimeofday () in
    
    let construction_start = Unix.gettimeofday () in
    let automata_ids = List.map (fun (st_node, intf_id) ->
      let open SessionAutomaton in
      let open SessionBuildAutomaton in

      let auto = build_automaton (Some intf_id) st_node.Lang.d st_node.Lang.span in
      let final_state = Hashtbl.fold (fun id s acc -> if s.accepting then id :: acc else acc) auto.states [] in
      assert (List.length final_state = 1);
      TypeAutomaton.add_transition auto (List.hd final_state) auto.start_state (LabelSet.singleton (Recurse intf_id)) false false true false;
      let final_state = List.hd final_state in
      let final_state_state = Hashtbl.find auto.states final_state in
      let first_state_state = Hashtbl.find auto.states auto.start_state in 
      final_state_state.offers_in_future <- first_state_state.offers_in_future;
      (auto, intf_id, Hashtbl.length auto.states, List.length auto.transitions)
    ) session_ids in
    
    let individual_sizes = List.map (fun (_, intf_id, states, trans) -> (intf_id, states, trans)) automata_ids in
    let theoretical_space = List.fold_left (fun acc (_, _, states, _) -> acc * states) 1 automata_ids in
    let num_automata = List.length automata_ids in
    
    let result, err, actual_states, visited_states, prod_transitions, construction_time_ms, game_time_ms = 
      try
        let prod_auto = SessionCompatiblityv3.create_product session_ids false pool.d.pool_id in
        let construction_end = Unix.gettimeofday () in
        let construction_time_ms = (construction_end -. construction_start) *. 1000.0 in
        
        Hashtbl.iter (fun state_id _ -> SessionCompatiblityv3.label_adversary_state prod_auto state_id) prod_auto.states;
        
        let game_start = Unix.gettimeofday () in
        let ids_list = List.map snd session_ids in
        let result, err = SessionGame.play_game prod_auto ids_list in
        let game_end = Unix.gettimeofday () in
        let game_time_ms = (game_end -. game_start) *. 1000.0 in
        
        let open SessionAutomaton in
        let actual_states = Hashtbl.length prod_auto.states in
        let prod_transitions = List.length prod_auto.transitions in
        
        (result, err, actual_states, actual_states, prod_transitions, construction_time_ms, game_time_ms)
      with
      | Except.TypeError msg ->
        let err_msg = List.filter_map (fun x -> match x with Except.Text msg -> Some msg | _ -> None) msg |> String.concat "; " in
        (false, err_msg, 0, 0, 0, 0.0, 0.0)
      | Failure msg -> (false, msg, 0, 0, 0, 0.0, 0.0)
    in
    
    let end_time = Unix.gettimeofday () in
    let total_time_ms = (end_time -. start_time) *. 1000.0 in
    
    let individual_sizes_str = 
      String.concat ";" (List.map (fun (id, states, trans) ->
        Printf.sprintf "%s(%d,%d)" id states trans
      ) individual_sizes) in
    
    let state_space_ratio = 
      if theoretical_space > 0 && actual_states > 0 then
        (float_of_int actual_states) /. (float_of_int theoretical_space)
      else 0.0 in
    
    let error_msg_escaped = String.map (fun c -> if c = ',' || c = '\n' then ' ' else c) err in
    
    (* Write this pool's data to CSV file immediately (append mode) *)
    let csv_out_append = open_out_gen [Open_wronly; Open_append] 0o644 csv_filename in
    Printf.fprintf csv_out_append "%s,%d,\"%s\",%d,%d,%d,%d,%.6f,%.3f,%.3f,%.3f,%b,\"%s\"\n"
      pool.d.pool_id
      num_automata
      individual_sizes_str
      theoretical_space
      actual_states
      visited_states
      prod_transitions
      state_space_ratio
      construction_time_ms
      game_time_ms
      total_time_ms
      result
      error_msg_escaped;
    close_out csv_out_append;
    
    Printf.eprintf "  Result: %b | Time: %.2f ms | States: %d/%d\n" result total_time_ms actual_states theoretical_space;
  ) pool_defs;
  
  Printf.eprintf "\nProfiling results appended to %s\n\n" csv_filename
  

let debug_types out config =
  let open Config in
  match config.debug_choice with
  | 0 -> rely_guarantee_debug out config
  | 1 -> profile_compatibility_checks out config
  | 2 -> generalized_type_debug out config
  | _ -> raise (Failure "Unknown debug choice")
      

let compile out config =
  let open Config in
  if config.debug_mode then(
    Printf.eprintf "Debug mode enabled\n";
    debug_types out config
  )
  else(
  let toplevel_filename = List.hd config.input_filenames in
  let cunits = ref [] in
  (
    try parse_recursive cunits (ref Utils.StringSet.empty) config toplevel_filename
    with
      | Except.TypeError msg ->
        (Except.Text "Type error:")::msg
          |> raise_compile_error None
  );
  (* collect all channel class and type definitions *)
  let all_channel_classes = List.concat_map (fun (_, cunit) -> let open Lang in cunit.channel_classes) !cunits in
  let all_session_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.session_defs) !cunits in

  let all_pool_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.pools) !cunits in
  let all_type_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.type_defs) !cunits in
  let all_procs = List.concat_map (fun (file_name, cunit) -> let open Lang in List.map (fun p -> (file_name, p)) cunit.procs) !cunits in
  let all_func_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.func_defs) !cunits in
  let all_macro_defs = List.concat_map (fun (_, cunit) -> let open Lang in cunit.macro_defs) !cunits in
  let proc_map = List.map (fun (file_name, proc) -> (let open Lang in (proc:proc_def).name, (proc, file_name))) all_procs
    |> Utils.StringMap.of_list in
  let sched = BuildScheduler.create () in
  (* add processes that are concrete *)
  List.iter (fun (file_name, proc) ->
    let open Lang in
    if proc.params = [] then
      let _ = BuildScheduler.add_proc_task sched file_name Lang.code_span_dummy proc.name [] in ()
  ) all_procs;
  let modules_visited = ref Utils.StringSet.empty in
  let event_graph_complete = ref false in
  let graph_collection_queue = Queue.create () in
  while not !event_graph_complete do
    match BuildScheduler.next sched with
    | None -> event_graph_complete := true
    | Some task -> (
      if Utils.StringSet.mem task.module_name !modules_visited |> not then (
        modules_visited := Utils.StringSet.add task.module_name !modules_visited;
        let proc_file_opt = Utils.StringMap.find_opt
          (let open BuildScheduler in task.proc_name)
          proc_map in
        let open Except in
        match proc_file_opt with
        | None ->
          let msg_text = Printf.sprintf "Process '%s' not found!" task.proc_name in
          raise_compile_error None
            [
              Text msg_text;
              codespan_in task.file_name task.codespan
            ]
        | Some (proc, file_name) ->
          let cunit = let open Lang in
            (* hacky *)
            {cunit_file_name = Some file_name;
            channel_classes = all_channel_classes; type_defs = all_type_defs;
            session_defs = all_session_defs; pools = all_pool_defs; procs = [proc]; imports = []; _extern_procs = [];
            func_defs = all_func_defs;
            macro_defs = all_macro_defs} in
          let graph_collection =
            match GraphBuilder.build config sched task.module_name task.param_values cunit
            with
            | res -> res
            | exception exc ->
              (
                let msg =
                  match exc with
                  | EventGraph.LifetimeCheckError msg ->
                    (Text "Borrow checking failed:")::msg
                  | Except.TypeError msg ->
                    (Text "Type error:")::msg
                  | Except.UnimplementedError msg ->
                    (Text "Unimplemented error:")::msg
                  | EventGraph.EventGraphError msg ->
                    (Text "Event graph error:")::msg
                  | Except.UnknownError msg ->
                    (Text "Unknown error:")::msg
                  | _ -> raise exc
                in
                raise_compile_error (Some file_name) msg
              )
          in
          Queue.add graph_collection graph_collection_queue
      )
    )
  done;
  if config.just_check then
    ()
  else begin
    (* generate preamble *)
    Codegen.generate_preamble out;
    (* pull code from imported external files *)
    let visited_extern_files = ref Utils.StringSet.empty in
    let open Lang in
    List.iter (fun (file_name, cunit) ->
      List.iter (fun {is_extern; file_name = imp_file_name} ->
        if is_extern then
          let imp_file_name_canonical = canonicalise_file_name file_name imp_file_name in
          if Utils.StringSet.mem imp_file_name_canonical !visited_extern_files |> not then (
            visited_extern_files := Utils.StringSet.add imp_file_name_canonical !visited_extern_files;
            try Codegen.generate_extern_import out imp_file_name_canonical
            with Sys_error msg -> raise_compile_error (Some file_name) [Except.Text msg]
          )
      ) cunit.imports
    ) !cunits;
    (* generate the code from event graphs *)
    let all_collections = Queue.to_seq graph_collection_queue |> List.of_seq in
    let all_event_graphs = List.concat_map (fun collection -> let open EventGraph in collection.event_graphs) all_collections in
    List.iter (fun graphs ->
      Codegen.generate out config
       {graphs with EventGraph.external_event_graphs = all_event_graphs}) all_collections
  end

  )