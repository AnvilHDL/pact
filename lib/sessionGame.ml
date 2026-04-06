open SessionAutomaton
open Lang

module IntSet = Set.Make(Int)

let find_counterexample_indexed
    (auto : TypeAutomaton.t)
    (outgoing_index : transition_outgoing_index)
    (start : int)
    (winning_set : IntSet.t)
    : string =
  let buffer = Buffer.create 256 in
  let visited = Hashtbl.create 16 in
  
  let is_deadlock u = 
    (get_outgoing_from_index outgoing_index u) = []
  in

  let rec dfs u = 
    if Hashtbl.mem visited u then 
      Printf.bprintf buffer " -> Loop at %d" u
    else (
      Hashtbl.add visited u ();
      let state = Hashtbl.find auto.states u in
      
      Printf.bprintf buffer "\nState %d\n 1. [Offers : %s]\n" u (String.concat ", " (List.map string_of_msg_spec state.offers));
      
      let is_winning = IntSet.mem u winning_set in
      if is_winning then Printf.bprintf buffer " (WIN)" else Printf.bprintf buffer " (LOSE)";

      let outgoing = get_outgoing_from_index outgoing_index u in
      
         
      let losing_transitions = 
        if is_winning then []
        else List.filter (fun t -> not (IntSet.mem t.to_state winning_set)) outgoing 
      in

      let next_opt = 
        match losing_transitions with
        | [] -> 
            None 
        | transitions ->
            match List.find_opt (fun t -> is_deadlock t.to_state) transitions with
            | Some t -> Some t
            | None ->
                match List.find_opt (fun t -> not (Hashtbl.mem visited t.to_state)) transitions with
                | Some t -> Some t
                | None ->
                    Some (List.hd transitions)
      in
      
      match next_opt with
      | Some t -> 
         Printf.bprintf buffer "\n\t --[%s]--> " (string_of_label_set t.label);
         dfs t.to_state
      | None -> 
         Printf.bprintf buffer " -> Deadlock / End of Trace"
    )
  in
  dfs start;
  Buffer.contents buffer

let find_counterexample (auto : TypeAutomaton.t) (start : int) (winning_set : IntSet.t) : string =
  let outgoing_index = build_outgoing_index auto.transitions in
  find_counterexample_indexed auto outgoing_index start winning_set

let transition_has_id (t : transition) (req_id : string) : bool =
  LabelSet.exists (fun l ->
    match l with
    | Recurse id -> id = req_id
    | _ -> false
  ) t.label

let compute_id_attractor_indexed
    (auto : TypeAutomaton.t)
    (outgoing_index : transition_outgoing_index)
    (valid_region : IntSet.t)
    (req_id : string)
    (transition_has_id_cached : transition -> string -> bool)
    : IntSet.t =
  
  let attractor = ref IntSet.empty in
  let changed = ref true in

  while !changed do
    changed := false;
    
    IntSet.iter (fun u ->
      if not (IntSet.mem u !attractor) then (
        let state = Hashtbl.find auto.states u in
        let outgoing =
          List.filter (fun t -> not (t.to_state = u)) (get_outgoing_from_index outgoing_index u)
        in
        let valid_outgoing = List.filter (fun t -> IntSet.mem t.to_state valid_region) outgoing in

        let is_added = 
          if state.is_fair then
            List.exists (fun t -> 
              let has_id = transition_has_id_cached t req_id in
              let leads_to_attr = IntSet.mem t.to_state !attractor in
              has_id || leads_to_attr
            ) valid_outgoing
          else
            (valid_outgoing <> []) &&
            List.for_all (fun t ->
              let has_id = transition_has_id_cached t req_id in
              let leads_to_attr = IntSet.mem t.to_state !attractor in
              has_id || leads_to_attr
            ) valid_outgoing
        in

        if is_added then (
          attractor := IntSet.add u !attractor;
          changed := true
        )
      )
    ) valid_region
  done;
  !attractor

let compute_id_attractor (auto : TypeAutomaton.t) (valid_region : IntSet.t) (req_id : string) : IntSet.t =
  let outgoing_index = build_outgoing_index auto.transitions in
  let transition_has_id_cached t id = transition_has_id t id in
  compute_id_attractor_indexed auto outgoing_index valid_region req_id transition_has_id_cached

let solve_game_custom_indexed
    (auto : TypeAutomaton.t)
    (outgoing_index : transition_outgoing_index)
    (req_ids : string list)
    : IntSet.t =
  
  let w = ref (Hashtbl.fold (fun id _ acc -> IntSet.add id acc) auto.states IntSet.empty) in
  let changed = ref true in
  let req_id_cache : ((transition * string), bool) Hashtbl.t = Hashtbl.create 128 in
  let transition_has_id_cached (t : transition) (req_id : string) : bool =
    let key = (t, req_id) in
    try Hashtbl.find req_id_cache key
    with Not_found ->
      let res = transition_has_id t req_id in
      Hashtbl.add req_id_cache key res;
      res
  in

  while !changed do
    let start_w = !w in
    let current_iter_w = ref start_w in

    List.iter (fun req_id ->
      if not (IntSet.is_empty !current_iter_w) then (
        let forced_nodes = compute_id_attractor_indexed auto outgoing_index !current_iter_w req_id transition_has_id_cached in
        current_iter_w := IntSet.inter !current_iter_w forced_nodes
      )
    ) req_ids;

    if IntSet.equal start_w !current_iter_w then
      changed := false
    else (
      w := !current_iter_w;
      changed := true
    )
  done;
  !w

let solve_game_custom (auto : TypeAutomaton.t) (req_ids : string list) : IntSet.t =
  let outgoing_index = build_outgoing_index auto.transitions in
  solve_game_custom_indexed auto outgoing_index req_ids

let sanity_check_indexed (auto : TypeAutomaton.t) (outgoing_index : transition_outgoing_index) : int list =
  Hashtbl.fold (fun id _st acc ->
    if (get_outgoing_from_index outgoing_index id) <> [] then acc else id :: acc
  ) auto.states []

let sanity_check (auto : TypeAutomaton.t) : int list =
  let outgoing_index = build_outgoing_index auto.transitions in
  sanity_check_indexed auto outgoing_index

let collect_dead_ends_paths_indexed
    (auto : TypeAutomaton.t)
    (outgoing_index : transition_outgoing_index)
    (st_ids : int list)
    : (int * string) list =
  List.map (fun dead_end_id ->
    let visited = Hashtbl.create 16 in
    let queue = Queue.create () in
    Hashtbl.add visited auto.start_state None;
    Queue.add auto.start_state queue;

    let rec build_path u =
      match Hashtbl.find visited u with
      | None -> []
      | Some (prev, t) -> build_path prev @ [t]
    in

    let found = ref false in
    while not !found && not (Queue.is_empty queue) do
      let u = Queue.take queue in
      if u = dead_end_id then found := true
      else
        let outgoing = get_outgoing_from_index outgoing_index u in
        List.iter (fun t ->
          if not (Hashtbl.mem visited t.to_state) then (
            Hashtbl.add visited t.to_state (Some (u, t));
            Queue.add t.to_state queue
          )
        ) outgoing
    done;

    let trace = 
      if !found then
        let path = build_path dead_end_id in
        let buffer = Buffer.create 256 in
        Printf.bprintf buffer "Trace from start state %d to dead-end state %d:\n" auto.start_state dead_end_id;
        let current_state = ref auto.start_state in
        List.iter (fun t ->
          Printf.bprintf buffer "  State %d --[%s]--> State %d\n" 
            !current_state (string_of_label_set t.label) t.to_state;
          current_state := t.to_state
        ) path;
        Printf.bprintf buffer "  State %d: DEAD END (no outgoing transitions)\n" dead_end_id;
        Buffer.contents buffer
      else
        Printf.sprintf "Dead-end state %d is not reachable from start state %d" dead_end_id auto.start_state
    in
    (dead_end_id, trace)
  ) st_ids

let collect_dead_ends_paths (auto : TypeAutomaton.t) (st_ids : int list) : (int * string) list =
  let outgoing_index = build_outgoing_index auto.transitions in
  collect_dead_ends_paths_indexed auto outgoing_index st_ids

let play_game (auto : TypeAutomaton.t) (ids : string list) : (bool * string) =

  let outgoing_index = build_outgoing_index auto.transitions in

  let dead_ends = sanity_check_indexed auto outgoing_index in
  if dead_ends <> [] then
    let dead_end_paths = collect_dead_ends_paths_indexed auto outgoing_index dead_ends in
    let dead_ends_str =
      String.concat "\n\n" (List.map (fun (_id, trace) -> trace) dead_end_paths)
    in
    (false, Printf.sprintf "Error: The automaton has dead-end states:\n %s" dead_ends_str)
  else


  let winning_set = solve_game_custom_indexed auto outgoing_index ids in
  let start_wins = IntSet.mem auto.start_state winning_set in

  Hashtbl.iter (fun id st -> st.is_winning <- IntSet.mem id winning_set) auto.states;

  if start_wins then
    (true, "Compatible: Strategy found to satisfy all IDs.")
  else
    let trace = find_counterexample_indexed auto outgoing_index auto.start_state winning_set in
    (false, Printf.sprintf "Compatibility failed. Losing Trace:\n%s" trace)