open Lang
open SessionAutomaton
open SessionGame
open SessionBuildAutomaton
open SessionUtils


let create_product (session_ids: (((session_type ast_node)*identifier) list))  (verbose : bool) (_name : identifier)  =
  let automata_ids_list = List.map (fun (st_node, intf_id) ->
    let auto = build_automaton (Some intf_id) st_node.d st_node.span in
    let final_state = Hashtbl.fold (fun id s acc -> if s.accepting then id :: acc else acc) auto.states [] in
    assert (List.length final_state = 1);
    TypeAutomaton.add_transition auto (List.hd final_state) auto.start_state (LabelSet.singleton (Recurse intf_id)) false false true false;
    let final_state = List.hd final_state in
    let final_state_state = Hashtbl.find auto.states final_state in
    let first_state_state = Hashtbl.find auto.states auto.start_state in 
    final_state_state.offers_in_future <- first_state_state.offers_in_future;
    (auto, intf_id)
  ) session_ids in

  let automata_ids = Array.of_list automata_ids_list in
  let automata_count = Array.length automata_ids in

  let outgoing_maps = Array.map (fun (auto, _) -> build_outgoing_index auto.transitions) automata_ids in
  let get_outgoing_transitions idx state_id =
    get_outgoing_from_index outgoing_maps.(idx) state_id
  in

  if verbose then (
    List.iter (fun (auto, intf_id) ->
      let out_chan = open_out (intf_id ^ "_automaton.dot") in
      print_automaton_dot auto out_chan;
      close_out out_chan;
      flush stderr;
    ) automata_ids_list
  );

  Printf.eprintf "All individual automata built. Starting product construction...\n";
  flush stderr;
  
  let state_map : (int list, int) Hashtbl.t = Hashtbl.create 10 in
  let prod_auto = TypeAutomaton.create () in

  let get_product_state (states: int list) : int =
    try Hashtbl.find state_map states
    with Not_found -> (
      let new_id = TypeAutomaton.new_state prod_auto false in
      Hashtbl.add state_map states new_id;
      new_id
    )
  in

  if verbose then
    Printf.eprintf "Information about individual automata:\n";
    Printf.eprintf "Total automata to combine: %d\n" automata_count;
    flush stderr;
    Array.iteri (fun idx (auto, intf_id) ->
      Printf.eprintf " Automaton %d (ID: %s): States = %d, Transitions = %d\n" idx intf_id (Hashtbl.length auto.states) (List.length auto.transitions);
      flush stderr
    ) automata_ids;
    

  let worklist = Queue.create () in
  Queue.add (Array.to_list (Array.map (fun (auto, _) -> auto.start_state) automata_ids)) worklist;
  let visited = ref IntListSet.empty  in
  let iter = ref 0 in
  let found_epsilon = ref false in

  let inc_iter =
    incr iter;
    if !iter mod 10000 = 0 then (
      Printf.eprintf "Product construction iteration %d, worklist size: %d, visited states: %d\n" !iter (Queue.length worklist) (IntListSet.cardinal !visited);
      flush stderr
    )
  in
  while not (Queue.is_empty worklist) do
    let current_states = Queue.take worklist in

    if not (IntListSet.mem current_states !visited) then (
      
      visited := IntListSet.add current_states !visited;
      let prod_state_id = get_product_state current_states in
      let current_states_arr = Array.of_list current_states in

      let is_all_start_state =
        let rec aux idx =
          if idx = automata_count then true
          else
            let auto, _ = automata_ids.(idx) in
            current_states_arr.(idx) = auto.start_state && aux (idx + 1)
        in
        aux 0
      in

      if is_all_start_state then TypeAutomaton.reroute_transitions prod_auto 0 prod_state_id [] ;

      let is_accepting_array =
        List.init automata_count (fun idx ->
          let auto, _ = automata_ids.(idx) in
          let state = Hashtbl.find auto.states current_states_arr.(idx) in
          state.accepting
        )
      in

      if List.for_all (fun x -> x) is_accepting_array then (
        (Hashtbl.find prod_auto.states prod_state_id).accepting <- true;
        let combined_label =
          Array.to_list (Array.map (fun (_, id) -> LabelSet.singleton (Recurse id)) automata_ids)
        in
        let combined_label = union_labelsets combined_label in
        TypeAutomaton.add_transition prod_auto prod_state_id prod_auto.start_state combined_label false false true false;
      ) 
      else (
        let current_state_info_arr =
          Array.init automata_count (fun idx ->
            let auto, _ = automata_ids.(idx) in
            Hashtbl.find auto.states current_states_arr.(idx)
          )
        in

        let transitions_list =
          List.init automata_count (fun idx ->
            get_outgoing_transitions idx current_states_arr.(idx)
          )
        in

        let current_state_offer_set_arr =
          Array.init automata_count (fun idx -> (
            let transitions = List.nth transitions_list (idx) in
            let transition_for_this_state = List.filter (fun t -> t.from_state = current_states_arr.(idx)) transitions in
            let offers = List.map( fun t -> 
                List.filter_map (function
                  | Action m -> Some m
                  | _ -> None
                ) (LabelSet.elements t.label)
            )transition_for_this_state |> List.filter (fun x -> x <> []) in
            offers
          ))
        in

        let offers_from_other_states_arr =
          Array.init automata_count (fun exc ->
            let offers = ref [] in
            for idx = 0 to automata_count - 1 do
              if idx <> exc then offers := List.flatten(current_state_offer_set_arr.(idx)) @ !offers
            done;
            !offers
          )
        in

        let group_satisfied msg_group offer_list =
          List.for_all (fun m -> List.mem m offer_list) msg_group
        in
        let check_no_complete_offer msg_groups offer_list =
          if offer_list = [] then true else
          List.for_all (fun msg_group -> not (group_satisfied msg_group offer_list)) msg_groups
        in
        let is_delay i t =
          LabelSet.exists (function
            | Delay -> true
            | OptionDelay msg_groups -> check_no_complete_offer msg_groups offers_from_other_states_arr.(i)
            | _ -> false
          ) t.label
        in

        let classified_transitions =
          List.mapi (fun i transition_set ->
            List.fold_left (fun (eps, recs, sync, cond, delay) t ->
              if t.is_epsilon || t.is_theta then
                (t :: eps, recs, sync, cond, delay)
              else if t.is_recurse then
                (eps, t :: recs, sync, cond, delay)
              else if t.is_conditional then
                (eps, recs, sync, t :: cond, delay)
              else if is_delay i t then
                (eps, recs, sync, cond, t :: delay)
              else
                (eps, recs, t :: sync, cond, delay)
            ) ([], [], [], [], []) transition_set
          ) transitions_list
        in

        let epsilon_transitions = List.map (fun (eps, _, _, _, _) -> eps) classified_transitions in
        let recurse_transitions = List.map (fun (_, recs, _, _, _) -> recs) classified_transitions in

      if List.for_all (fun ts -> ts = []) epsilon_transitions then (

          let sync_transitions = List.map (fun (_, _, sync, _, _) -> sync) classified_transitions in

          let conditional_trans = List.map (fun (_, _, _, cond, _) -> cond) classified_transitions in

          let delay_transitions = List.map (fun (_, _, _, _, delay) -> delay) classified_transitions in

          let all_has_delay = List.for_all (fun dt -> dt <> []) delay_transitions in

          let module MsgSpecSet = Set.Make(struct
            type t = Lang.message_specifier
            let compare = compare_msg_spec
          end) in

          let offers_set_arr =
            Array.init automata_count (fun idx ->
              List.fold_left (fun acc msg -> MsgSpecSet.add msg acc) MsgSpecSet.empty offers_from_other_states_arr.(idx)
            )
          in

          let create_message_specifier_set msg_list =
            List.fold_left (fun acc msg -> MsgSpecSet.add msg acc) MsgSpecSet.empty msg_list
          in
          let satisfiable_offers_arr =
            Array.init automata_count (fun i ->
              List.filter_map (fun (c : message_specifier list)->
                if MsgSpecSet.subset (create_message_specifier_set c) offers_set_arr.(i) then Some c else None
              ) current_state_offer_set_arr.(i)
            )
          in
          let satisfiable_offers = Array.to_list satisfiable_offers_arr in

          let next_states = List.mapi(fun i (off : message_specifier list list) ->
            (* empty symbolizes current state *)
            if off = [] then [(current_states_arr.(i), [])]
            else ( 
            List.map (fun o ->
              find_next_states_refined (List.nth sync_transitions i) current_states_arr.(i) o
            )off
            )
          )satisfiable_offers in

          assert (List.for_all (fun ns -> ns <> []) next_states);

          let rec cartesian_product2 lists =
              match lists with
              | [] -> [[]]
              | h :: t ->
                  let rest = cartesian_product2 t in
                  List.flatten (List.map (fun x -> List.map (fun r -> x :: r) rest) h)
          in

          let possible_next_states = cartesian_product2 next_states in
          (* Printf.eprintf "Product State %d: Possible Next States  = %s\n" prod_state_id (String.concat " | " (List.map (fun ns -> "[" ^ (String.concat "," (List.map string_of_int ns)) ^ "]") possible_next_states)); *)
          
          let found = ref false in

          let normalize_transition_combo combo =
            let selected = Array.of_list combo in
            let active = Array.make automata_count true in
            let changed = ref true in
            while !changed do
              changed := false;
              for i = 0 to automata_count - 1 do
                let _, offers_i = selected.(i) in
                if active.(i) && offers_i <> [] then (
                  let offers_from_others = ref [] in
                  for j = 0 to automata_count - 1 do
                    if j <> i && active.(j) then (
                      let _, offers_j = selected.(j) in
                      offers_from_others := offers_j @ !offers_from_others
                    )
                  done;
                  let offers_from_others = List.sort_uniq compare_msg_spec !offers_from_others in
                  let all_matched = List.for_all (fun m -> List.mem m offers_from_others) offers_i in
                  if not all_matched then (
                    active.(i) <- false;
                    changed := true
                  )
                )
              done
            done;

            let ns =
              List.init automata_count (fun i ->
                if active.(i) then
                  let st, _ = selected.(i) in
                  st
                else
                  current_states_arr.(i)
              )
            in
            let combined_actions =
              List.flatten (
                List.init automata_count (fun i ->
                  if active.(i) then
                    let _, off = selected.(i) in
                    off
                  else
                    []
                )
              )
              |> List.sort_uniq compare_msg_spec
            in
            (ns, combined_actions)
          in

          let action_set_of_list actions =
            List.fold_left (fun acc m -> MsgSpecSet.add m acc) MsgSpecSet.empty actions
          in

          let normalized_candidates =
            possible_next_states
            |> List.filter_map (fun combo ->
              let ns, combined_actions = normalize_transition_combo combo in
              if ns <> current_states && combined_actions <> [] then
                Some (ns, List.sort_uniq compare_msg_spec combined_actions)
              else
                None
            )
            |> List.sort_uniq compare
          in

          let pruned_candidates =
            List.filter (fun (ns, actions) ->
              let actions_set = action_set_of_list actions in
              not (
                List.exists (fun (ns_other, actions_other) ->
                  (ns_other <> ns || actions_other <> actions)
                  && MsgSpecSet.subset actions_set (action_set_of_list actions_other)
                  && not (MsgSpecSet.equal actions_set (action_set_of_list actions_other))
                ) normalized_candidates
              )
            ) normalized_candidates
          in

          List.iter (fun (ns, combined_actions) ->
            if ns <> current_states && combined_actions <> [] then begin
              found := true;
              inc_iter;
              let next_prod_state = get_product_state ns in
              let combined_label = List.fold_left (fun acc a -> LabelSet.add (Action a) acc) LabelSet.empty combined_actions in
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state combined_label false false false false;
              if not (IntListSet.mem ns !visited) then
                Queue.add ns worklist
            end
          ) pruned_candidates;

          if not !found then (
            found := false;
            let offers_in_future_from_others_arr =
              Array.init automata_count (fun exc ->
                let offers = ref [] in
                for idx = 0 to automata_count - 1 do
                  if idx <> exc then offers := current_state_info_arr.(idx).offers_in_future @ !offers
                done;
                !offers
              )
            in
            List.iteri(fun id tset ->
              inc_iter;
              let offers_in_future_of_this_state = offers_in_future_from_others_arr.(id) in
              List.iter (fun t -> 
                let is_compatible =
                  List.for_all (fun msg_groups ->
                    check_no_complete_offer msg_groups offers_in_future_of_this_state
                  ) (List.filter_map (function Negation msg_groups -> Some msg_groups | _ -> None) (LabelSet.elements t.label)) in

                (* Printf.eprintf "[Verdict = %s] [State %d] Considering conditional transition from automaton %d with not_acts: %s\n" (string_of_bool is_compatible) prod_state_id id (String.concat "," (List.map Lang.string_of_msg_spec t_not_acts_flat));
                Printf.eprintf "Offers in future of this state: %s\n" (String.concat "," (List.map Lang.string_of_msg_spec offers_in_future_of_this_state));
                Printf.eprintf "Others states: %s\n" (String.concat "," (List.map string_of_int current_states)); *)
                if is_compatible then (
                  found := true;
                  let next_states = List.mapi (fun idx s -> if idx = id then t.to_state else s) current_states in
                  let next_prod_state = get_product_state next_states in
                  TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
                  if not (IntListSet.mem next_states !visited) then 
                      Queue.add next_states worklist
                )
              )tset
            )conditional_trans;
          );

          if not !found then (
              found := false;
              let next_states = List.mapi(fun i t_set -> 
                if List.length t_set > 1 then raise (Failure "Unexpected: more than 1 recurse transition in set")
                else if List.length t_set = 1 then (
                  let t = List.hd t_set in
                  t.to_state
                ) else current_states_arr.(i)
              )recurse_transitions in
              let recurse_labels = List.flatten (List.map (fun t_set -> List.map (fun t -> t.label) t_set) recurse_transitions) in
              let combined_label = union_labelsets recurse_labels in

              if combined_label <> LabelSet.empty then (
                found := true;
                let next_prod_state = get_product_state next_states in
                TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state combined_label false false true false;
                if not (IntListSet.mem next_states !visited) then 
                    Queue.add next_states worklist
              )
            );
          

          if not !found && all_has_delay then (
              inc_iter;
              found := true;
                let all_delay_combinations = cartesian_product2 delay_transitions in
                List.iter( fun transition_set -> (
                    if List.length transition_set < 2 then raise (Failure "Unexpected: less than 2 transitions in combination")
                    else(
                        let next_states = List.mapi ( fun idx _->
                          let t = List.nth transition_set idx in
                          t.to_state
                        ) current_states in

                        let next_prod_state = get_product_state next_states in
                        TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state (LabelSet.singleton Delay) false false false false;
                        if not (IntListSet.mem next_states !visited) then 
                          Queue.add next_states worklist
                    )
                )
            ) all_delay_combinations;
          );

          if not !found then (
            found := false;
            let offers_for_this_state_arr_from_others =
              Array.init automata_count (fun exc ->
                let offers = ref [] in
                for idx = 0 to automata_count - 1 do
                  if idx <> exc then offers := current_state_info_arr.(idx).offers @ !offers
                done;
                !offers
              )
            in
              List.iteri (fun i t_set ->
                let offers_for_this_state = offers_for_this_state_arr_from_others.(i) in
                List.iter (fun t -> 
                  let is_compatible =
                    List.for_all (fun msg_groups ->
                      check_no_complete_offer msg_groups offers_for_this_state
                    ) (List.filter_map (function Negation msg_groups -> Some msg_groups | _ -> None) (LabelSet.elements t.label)) in 
                  
                    (* Printf.eprintf "[Verdict = %s] [State %d] Considering conditional transition with delay compatibility from automaton %d with not_acts: %s\n" (string_of_bool is_compatible) prod_state_id i (String.concat "," (List.map Lang.string_of_msg_spec t_not_acts_flat));
                  Printf.eprintf "Offers for this state from others: %s\n" (String.concat "," (List.map Lang.string_of_msg_spec offers_for_this_state));
                  Printf.eprintf "Others states: %s\n" (String.concat "," (List.map string_of_int current_states)); *)
                  if is_compatible then (
                    found := true;
                    let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
                    let next_prod_state = get_product_state next_states in
                    TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
                    if not (IntListSet.mem next_states !visited) then 
                        Queue.add next_states worklist
                  )
                )t_set
              )conditional_trans
          );
          
          if not !found && not !found_epsilon then (
            let trace = collect_dead_ends_paths prod_auto [prod_state_id] in
            let trace = Printf.sprintf "Dead-end trace leading to product state %d:\n%s\n" prod_state_id (List.hd trace|> snd) in
            let msg = Printf.sprintf "No compatible transitions found from product state %d corresponding to states %s\n%s" prod_state_id (String.concat "," (List.map string_of_int current_states)) trace in
            Printf.eprintf "State Map : Product state -> Component states\n";
            Hashtbl.iter (fun states prod_state_id ->
              Printf.eprintf "Product state %d -> Component states [%s]\n" prod_state_id (String.concat "," (List.map string_of_int states))
            ) state_map;
            Printf.eprintf "Offers of each automaton in current state: %s\n" (String.concat " | " (List.mapi (fun idx st_id ->
              let auto, _ = automata_ids.(idx) in
              let state = Hashtbl.find auto.states st_id in
              Printf.sprintf "\nAutomaton %d offers: [%s] | has delay: %b" idx (String.concat "," (List.map Lang.string_of_msg_spec state.offers)) ((List.nth delay_transitions idx) <> [])
            ) current_states));
            let out_channel = open_out ("incompat_prod_auto_"^_name^".dot") in
            print_automaton_dot prod_auto out_channel;
            close_out out_channel;
            flush stderr;
            raise (Failure msg)
          )
      )
      else
      (
          List.iteri (fun i ep_set -> 
            List.iter (fun t ->
              let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
              let next_prod_state = get_product_state next_states in
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
              if not (IntListSet.mem next_states !visited) then 
                  Queue.add next_states worklist
            ) ep_set
          )epsilon_transitions;
      )   

    )
  )
  done;

  (* Assign offers/fair/adversary flags as before... *)
  Hashtbl.iter (fun states prod_state_id ->
    let offers = List.flatten (List.mapi (fun idx st_id ->
      let auto, _ = automata_ids.(idx) in
      let state = Hashtbl.find auto.states st_id in
      state.offers
    ) states) in
    let offers = List.sort_uniq compare_msg_spec offers in
    let offers_in_future = List.flatten (List.mapi (fun idx st_id ->
      let auto, _ = automata_ids.(idx) in
      let state = Hashtbl.find auto.states st_id in
      state.offers_in_future
    ) states) in
    let offers_in_future = List.sort_uniq compare_msg_spec offers_in_future in
    let is_fair = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = automata_ids.(idx) in
      (Hashtbl.find auto.states st_id).is_fair
    ) states) in
    let is_adversary = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = automata_ids.(idx) in
      (Hashtbl.find auto.states st_id).adversary
    ) states) in

    let prod_state = Hashtbl.find prod_auto.states prod_state_id in
    prod_state.offers <- offers;
    prod_state.is_fair <- is_fair;
    prod_state.offers_in_future <- offers_in_future;
    prod_state.adversary <- is_adversary
  ) state_map;

  (* Debug output *)
  if verbose then Hashtbl.iter (fun states prod_state_id ->
      Printf.eprintf "Product state %d corresponds to states %s\n" prod_state_id (String.concat "," (List.map string_of_int states))
  ) state_map;

  prod_auto

let label_adversary_state (auto : TypeAutomaton.t) (state_id : int) =
  let state = Hashtbl.find auto.states state_id in
  (* let check_if_adversary_state =
    List.exists (fun t ->
      t.is_theta
    ) (List.filter (fun t -> t.from_state = state_id) auto.transitions)
  in
  if check_if_adversary_state then *)
    state.adversary <- true


let check_compatibility_multiparty 
    (session_ids : ((session_type ast_node) * identifier) list)
    (pool_id : identifier)
    (verbose : bool) 
    : (bool * string) =


    let prod_auto = create_product session_ids verbose pool_id in
    Printf.eprintf "Product Construction Completed. Total States: %d\n" (Hashtbl.length prod_auto.states);

    Hashtbl.iter (fun state_id _ ->
        label_adversary_state prod_auto state_id
    ) prod_auto.states;

    let ids_list = List.map snd session_ids in
    
    let result, err = play_game prod_auto ids_list in
    Printf.eprintf "Game Analysis Completed : %b\n" result;

    if verbose || (not result) then begin
    let res_prefix = if result then "compat_" else "incompat_" in
    let out = Stdlib.open_out (res_prefix^"prod_auto_"^pool_id^".dot") in
    print_automaton_dot prod_auto out;
    Stdlib.close_out out;
    flush stderr;
    end;
    (result, err)
