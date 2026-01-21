open Lang
open SessionAutomaton
open SessionGame
open SessionBuildAutomaton




let create_product (session_ids: (((session_type ast_node)*identifier) list))  (verbose : bool)  =
  let automata_ids = List.map (fun (st_node, intf_id) ->
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

  if verbose then (
    List.iter (fun (auto, intf_id) ->
      let out_chan = open_out (intf_id ^ "_automaton.dot") in
      print_automaton_dot auto out_chan;
      close_out out_chan;
      flush stderr;
    ) automata_ids
  );
  
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


  let worklist = ref [List.map(fun (auto, _) -> auto.start_state) automata_ids] in
  let visited = ref IntListSet.empty  in

  while !worklist <> [] do
    let current_states = List.hd !worklist in
    worklist := List.tl !worklist;

    if not (IntListSet.mem current_states !visited) then (
      
      visited := IntListSet.add current_states !visited;
      let prod_state_id = get_product_state current_states in

      let is_all_start_state = List.for_all2 (fun st_id (auto, _) ->
        st_id = auto.start_state
      ) current_states automata_ids in
      if is_all_start_state then TypeAutomaton.reroute_transitions prod_auto 0 prod_state_id;
      let is_accepting_array = List.map2 (fun st_id (auto, _) ->
        let state = Hashtbl.find auto.states st_id in
        state.accepting
      ) current_states automata_ids in

      if List.for_all (fun x -> x) is_accepting_array then (
        (Hashtbl.find prod_auto.states prod_state_id).accepting <- true;
        let combined_label = List.map(fun (_, id) ->
          LabelSet.singleton (Recurse id)
        )automata_ids  in
        let combined_label = union_labelsets combined_label in
        TypeAutomaton.add_transition prod_auto prod_state_id prod_auto.start_state combined_label false false true false;
      ) else (
        
        let transitions_list = List.mapi (fun idx (auto, _) ->
          let state_id = List.nth current_states idx in
          List.filter (fun t -> t.from_state = state_id) auto.transitions
        ) automata_ids in
        
        let actions_of_this_state exc = List.mapi (fun indx s -> 
          if indx = exc then [] else
          let auto, _= List.nth automata_ids indx in 
          let st = Hashtbl.find auto.states s in 
          st.offers
        ) current_states in

        let check_no_offers msg_list offer_list =
          if offer_list = [] then true else
          List.for_all (fun m ->
            not (List.mem m offer_list)
          ) msg_list
          in
        let is_delay i t = LabelSet.exists (function Delay -> true | OptionDelay m_list -> check_no_offers m_list (List.flatten (actions_of_this_state i)) | _ -> false) t.label in

        let is_delay_con t = LabelSet.exists (function Delay -> true | OptionDelay _ -> true | _ -> false) t.label in

        let epsilon_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_epsilon || t.is_theta || t.is_recurse then Some t else None
          ) transition_set
        ) transitions_list in

        let theta_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_theta then Some t else None
          ) transition_set
        ) epsilon_transitions in

        let _recurse_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_recurse then Some t else None
          ) transition_set
        ) epsilon_transitions in

        let epsilon_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_epsilon then Some t else None
          ) transition_set
        ) epsilon_transitions in

        if List.for_all (fun ts -> ts = []) theta_transitions then (
        let sync_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if not t.is_epsilon && not t.is_theta && not t.is_recurse && not (is_delay_con t) 
            then Some t 
            else None
          ) transition_set
        ) transitions_list in

        let delay_transitions = List.mapi (fun i transition_set ->
          List.filter_map (fun t -> if is_delay i t then Some t else None) transition_set
        ) transitions_list in

        let all_has_delay = List.for_all (fun dt -> dt <> []) delay_transitions in


        List.iteri (fun i ep_set -> 
          List.iter (fun t ->
            let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
            let next_prod_state = get_product_state next_states in
            TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
            if not (IntListSet.mem next_states !visited) then 
               worklist := next_states :: !worklist
          ) ep_set
        ) epsilon_transitions;


      let rec cartesian_product lists =
        match lists with
        | [] -> [[]]
        | h :: t ->
            let rest = cartesian_product t in
            let choices = (List.map (fun x -> Some x) h) @ [None] in
            
            List.flatten (List.map (fun item -> 
              List.map (fun r -> item :: r) rest
            ) choices) in

        let rec cartesian_product2 lists =
            match lists with
            | [] -> [[]]
            | h :: t ->
                let rest = cartesian_product2 t in
                List.flatten (List.map (fun x -> List.map (fun r -> x :: r) rest) h)
        in


        
        let all_transition_combinations = cartesian_product sync_transitions in

        let found = ref false in
        
        List.iteri (fun set_i transition_set ->

          let actual_transitions = List.filter_map (fun opt -> opt) transition_set in


          

          if actual_transitions <> [] then (

            let combined_actions = List.flatten (List.map (fun t -> 
              List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label)
            ) actual_transitions) in

            let combined_actions = if combined_actions = [] then union_labelsets (List.map (fun t -> t.label) actual_transitions)
            else List.fold_left (fun acc a -> LabelSet.add (Action a) acc) LabelSet.empty combined_actions in
          (* let no_delay_transitions = List.for_all(
            fun t ->
              t = []
          )delay_transitions in *)


          let is_compatible  =  (
            List.mapi( fun i t_opt ->
                match t_opt with
                | None -> (true, true,false) (* Empty slot is always compatible *)
                | Some t ->
                (
                      let t_actions = List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label) in
                      let actions = List.flatten ( List.mapi (fun idx t_opt ->
                        if idx = i then [] else
                          match t_opt with
                          | None -> []
                          | Some t -> List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label)
                      ) transition_set) in


                      let actions_of_this_state = List.mapi (fun si t_set ->
                        if si = set_i then [] else
                        List.mapi ( fun indxt t' ->
                          if indxt = i then [] else
                          (
                            match t' with
                            | None -> []
                            | Some t ->
                              (
                            let t_acts = List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label) in
                            t_acts
                              )
                          )
                        )t_set |> List.filter (fun x -> x <> []) |> List.flatten  |>  List.sort_uniq compare_msg_spec
                          
                      ) all_transition_combinations |> List.filter (fun x -> x <> [])  in
                      let offers_of_this_state = List.flatten actions_of_this_state in
                      let offers_in_future_of_this_state = List.mapi (fun indx s -> if i = indx then [] else (let auto, _= List.nth automata_ids indx in let st = Hashtbl.find auto.states s in st.offers_in_future) ) current_states in

                      let offers_in_future_of_this_state = List.flatten offers_in_future_of_this_state in

                      let t_not_acts = List.filter_map (function Negation ms -> Some ms | _ -> None) (LabelSet.elements t.label) in

                      let next_quests = List.filter_map (function Questionable m -> Some m | _ -> None) (LabelSet.elements t.label) in
                      let next_quests = List.flatten next_quests in
                      let t_not_acts_flat = List.flatten t_not_acts in
                      let combined_t_possibe_acts = t_actions @ next_quests in
                      let weak_compat = if t.is_conditional && (List.for_all( fun tna ->
                        not (List.mem tna offers_of_this_state)
                      )t_not_acts_flat) then true else false in

                     let verdict = (
                        (
                          List.for_all( fun ua ->
                            List.mem ua actions
                          )t_actions &&
                          List.for_all( fun tna ->
                            not (List.mem tna offers_in_future_of_this_state)
                          )t_not_acts_flat&&
                          ((List.is_empty next_quests) || ( not (List.exists (fun na ->
                            List.for_all(fun ps -> List.mem ps na) combined_t_possibe_acts
                          ) actions_of_this_state
                          )
                          ) )
                        ),
                        t.is_conditional,
                        weak_compat
                      ) in
                      verdict
                )
            )transition_set
          ) in 

          let is_all_conditional = List.for_all (fun (_, cond,_) -> cond) is_compatible in
          let weak_compat = List.map (fun (_, _, wc) -> wc) is_compatible in

          let is_compatible = List.for_all (fun (x, _, _) -> x) is_compatible in

          let no_recurse = List.for_all (fun ts -> ts = [] ) _recurse_transitions in



            if is_compatible then (
              found := true;
              if is_all_conditional then (
                List.iteri (fun i t_opt -> 
                  match t_opt with
                  | None -> ()
                  | Some t -> 

                    let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
                    let next_prod_state = get_product_state next_states in
                    (* let offers_in_future_of_this_state = List.mapi (fun indx s -> if i = indx then [] else (let auto, _= List.nth automata_ids indx in let st = Hashtbl.find auto.states s in st.offers_in_future) ) current_states in
                    let offers_in_future_of_this_state = List.flatten offers_in_future_of_this_state in
                    Printf.eprintf "  Transition %s from state %d to %d with offers in future \n%s\n" (string_of_transition t) prod_state_id next_prod_state (String.concat "," (List.map Lang.string_of_msg_spec offers_in_future_of_this_state)); *)
                    TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
                    if not (IntListSet.mem next_states !visited) then 
                      worklist := next_states :: !worklist
                ) transition_set
              )
            else
              let next_states = List.mapi (fun idx t_opt ->
                let current_state = List.nth current_states idx in
                match t_opt with
                | None -> current_state
                | Some t -> if  (t.is_conditional&&is_all_conditional)|| (not t.is_conditional) then t.to_state else current_state
              ) transition_set in
              let next_prod_state = get_product_state next_states in
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state combined_actions false false false (List.for_all (fun t_opt -> match t_opt with None -> true | Some t -> t.is_conditional) transition_set);
              if not (IntListSet.mem next_states !visited) then 
                worklist := next_states :: !worklist

            )
            else if no_recurse then (
              List.iteri (fun i res ->
                if res then (
                  found := true;
                  let t = List.nth transition_set i in
                  let next_states = List.mapi (fun idx s -> if idx = i then (match t with Some tr -> tr.to_state | None -> s) else s) current_states in
                  let next_prod_state = get_product_state next_states in
                  let t = Option.get t in
                  TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
                  if not (IntListSet.mem next_states !visited) then 
                    worklist := next_states :: !worklist
                )


              )weak_compat
                
            )
          )
        ) all_transition_combinations;

        if not !found then (
          List.iteri (fun i t_set -> 
            if List.length t_set > 1 then raise (Failure "Unexpected: more than 1 recurse transition in set")
            else if List.length t_set = 1 then (
              let t = List.hd t_set in
              let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
              let next_prod_state = get_product_state next_states in
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
              if not (IntListSet.mem next_states !visited) then 
                 worklist := next_states :: !worklist
            ) 
          )_recurse_transitions;
        );

        if all_has_delay then
        ( 
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
                  worklist := next_states :: !worklist
            )
          )
        ) all_delay_combinations;
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
                 worklist := next_states :: !worklist
            ) ep_set
          ) theta_transitions;
        )   

      )
    )
  done;

  (* Assign offers/fair/adversary flags as before... *)
  Hashtbl.iter (fun states prod_state_id ->
    let offers = List.flatten (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      let state = Hashtbl.find auto.states st_id in
      state.offers
    ) states) in
    let offers = List.sort_uniq compare_msg_spec offers in
    let offers_in_future = List.flatten (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      let state = Hashtbl.find auto.states st_id in
      state.offers_in_future
    ) states) in
    let offers_in_future = List.sort_uniq compare_msg_spec offers_in_future in
    let is_fair = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      (Hashtbl.find auto.states st_id).is_fair
    ) states) in
    let is_adversary = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
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


    let prod_auto = create_product session_ids verbose in

    Printf.eprintf "Product Construction Completed. Total States: %d\n" (Hashtbl.length prod_auto.states);

    Hashtbl.iter (fun state_id _ ->
        label_adversary_state prod_auto state_id
    ) prod_auto.states;

    let ids_list = List.map snd session_ids in
    
    let result, err = play_game prod_auto ids_list in
    Printf.eprintf "Game Analysis Completed.\n";

    let res_prefix = if result then "compat_" else "incompat_" in

    let out = Stdlib.open_out (res_prefix^"prod_auto_"^pool_id^".dot") in
    print_automaton_dot prod_auto out;
    Stdlib.close_out out;
    flush stderr;
    (result, err)
