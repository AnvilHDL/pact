open Lang
open SessionAutomaton2
open SessionBuildAutomaton2
open SessionGame2

let collect_sync_messages session_ids =
  (* Closed checking synchronizes on every message mentioned by the pool. *)
  List.fold_left
    (fun acc (session_node, _) ->
      MsgSet.union acc (messages_of_session_type session_node.d))
    MsgSet.empty session_ids

let create_product
    (session_ids : ((session_type ast_node) * identifier) list)
    (verbose : bool) (pool_id : identifier) =
  (* Build member automata, then compose them with the closed product rule. *)
  let automata_with_ids =
    List.map
      (fun (session_node, intf_id) ->
        let auto =
          build_automaton (Some intf_id) session_node.d session_node.span
        in
        TypeAutomaton.accepting_states auto
        |> List.iter (fun final_state ->
               (* Each member emits its interface ID when one protocol iteration ends. *)
               TypeAutomaton.add_transition auto final_state auto.start_state
                 (Progress (StringSet.singleton intf_id))
                 any_guard);
        recompute_state_summaries auto;
        if verbose then (
          let out = open_out (intf_id ^ "_generalized_v2_automaton.dot") in
          print_automaton_dot auto out;
          close_out out);
        (auto, intf_id))
      session_ids
  in
  let sync_messages = collect_sync_messages session_ids in
  if verbose then (
    Printf.eprintf
      "Generalized Type v2 closed sync messages for pool %s: {%s}\n" pool_id
      (string_of_msgset sync_messages);
    List.iter
      (fun (auto, intf_id) ->
        Printf.eprintf
          " Generalized Type v2 automaton %s: states=%d transitions=%d\n" intf_id
          (Hashtbl.length auto.states) (List.length auto.transitions))
      automata_with_ids);
  let automata = automata_with_ids |> List.map fst |> Array.of_list in
  let ids = List.map snd automata_with_ids in
  let product = closed_product ~progress_ids:ids automata sync_messages in
  if verbose then (
    Printf.eprintf
      "Generalized Type v2 product construction completed for pool %s: states=%d transitions=%d\n"
      pool_id (Hashtbl.length product.states) (List.length product.transitions));
  product

let check_compatibility_multiparty
    (session_ids : ((session_type ast_node) * identifier) list)
    (pool_id : identifier) (verbose : bool) =
  (* Public v2 entry point mirrors the legacy multiparty checker. *)
  let product = create_product session_ids verbose pool_id in
  Hashtbl.iter
    (fun state_id _ -> TypeAutomaton.make_adversary product state_id)
    product.states;
  let ids = List.map snd session_ids in
  let result, err = play_game product ids in
  if verbose || not result then (
    let prefix = if result then "compat_" else "incompat_" in
    let out = open_out (prefix ^ "prod_auto_" ^ pool_id ^ ".dot") in
    print_automaton_dot product out;
    close_out out);
  if verbose then
    Printf.eprintf "Generalized Type v2 game analysis completed for pool %s: %b\n"
      pool_id result;
  (result, err)
