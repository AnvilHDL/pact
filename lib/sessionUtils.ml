open SessionAutomaton

let compare_msg_spec m1 m2 =
  String.compare (Lang.string_of_msg_spec m1) (Lang.string_of_msg_spec m2)

let convert_to_order_spec msg_list = 
  List.sort_uniq compare_msg_spec msg_list



let get_ordered_transition_specifiers (t : transition) = 
  (
      List.filter_map (function l ->
        match l with
        | Action m -> Some m
        | _ -> None
      ) (LabelSet.elements t.label)
  ) |> List.sort_uniq compare_msg_spec

let label_subset offers l = 
  let l_offers = get_ordered_transition_specifiers l in
  let offers_spec = convert_to_order_spec offers in
  List.for_all (fun o -> List.mem o offers_spec) l_offers

let find_next_states transitions_list state_id offers = 
  let transitions = List.filter (fun t -> (t.from_state = state_id)&&(label_subset offers t)) transitions_list in

  let offer_state_pair = List.map (fun t ->
    let t_offers = get_ordered_transition_specifiers t in
    (t_offers, t.to_state)
  ) transitions in

  let compare_offer_state_pair (offers1,_state1) (offers2,_state2) = (List.length offers2) - (List.length offers1) in

  let offer_state_pair_sorted = List.sort compare_offer_state_pair offer_state_pair in

  let (next_states, remaining_offers) =
    List.fold_left (fun (acc, pending_offer) (off, stid) ->
      if pending_offer = [] then (acc, [])
      else
        let pending_offer_filtered = List.filter (fun o -> not (List.mem o off)) pending_offer in
        let offers_covered = List.filter (fun o -> List.mem o off) pending_offer in
        (acc @ [(stid, offers_covered)], pending_offer_filtered)
    ) ([], offers) offer_state_pair_sorted
  in
  assert (if(remaining_offers = []) then true else (DebugLog.line "product" "next_states.log" "Remaining offers: %s" (String.concat "," (List.map Lang.string_of_msg_spec remaining_offers)); false));
  DebugLog.line "product" "next_states.log" "State %d: Offers = [%s], Next states = [%s]" state_id (String.concat "," (List.map Lang.string_of_msg_spec offers)) (String.concat "," (List.map (fun (stid, _) -> string_of_int stid) next_states));
  next_states


let find_next_states_refined transitions_list state_id offers = 
  (* find the transition to state with exact offer matching *)
  let transitions = List.filter (fun t -> (t.from_state = state_id)&&(get_ordered_transition_specifiers t = offers)) transitions_list in
  if transitions <> [] && not (List.length transitions > 1) then
    List.hd transitions |> fun t -> (t.to_state, offers)
  else
    raise (Failure (Printf.sprintf "No transition found from state %d with offers [%s]" state_id (String.concat "," (List.map Lang.string_of_msg_spec offers))))