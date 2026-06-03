open CompileHelpers


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
      let preprocess = SessionHelper.expand_session_type_quantifiers sdef.d.body.d in
      Printf.eprintf "Session Type %s: %s \n" sdef.d.name (string_of_protocol preprocess);
    ) session_type_defs;
    

  let open SessionBuildAutomaton in
  let open SessionAutomaton in

  if config.verbose then Printf.eprintf "\nGenerating Generalized Types as DOT files...\n\n";
  List.iter(
    fun (sdef :Lang.session_def Lang.ast_node) ->
    try
        let gen_type = build_automaton None sdef.d.body.d sdef.d.body.span in 
        let out_channel = Printf.sprintf "generalized_type_%s.dot" sdef.d.name in
        let out = open_out out_channel in
        print_automaton_dot gen_type out;
        close_out out
    with
    | Except.TypeError msg ->
        let err_msg = List.filter_map (fun x -> match x with Except.Text msg -> Some msg | _ -> None) msg |> String.concat "; " in
        Printf.eprintf "Error generating generalized type for %s: %s\n" sdef.d.name err_msg
    | Failure msg ->
        Printf.eprintf "Error generating generalized type for %s: %s\n" sdef.d.name msg
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
  


let debug_types_custom out config =
let open Config in
match config.debug_choice with
| 0 -> generalized_type_debug out config
| 1 -> profile_compatibility_checks out config
| 2 -> generalized_type_debug out config
| _ -> raise (Failure "Unknown debug choice")