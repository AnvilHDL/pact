open SessionAutomaton
open Lang

module StringSet = Set.Make(String)

let find_counterexample (auto : TypeAutomaton.t) (start : int) (winning_set : IntSet.t) : string =
  let buffer = Buffer.create 256 in
  let visited = Hashtbl.create 16 in
  
  let rec dfs u = 
    if Hashtbl.mem visited u then 
      Printf.bprintf buffer " -> Loop at %d" u
    else (
      Hashtbl.add visited u ();
      Printf.bprintf buffer "\nState %d [Offers : %s]" u (String.concat ", " (List.map string_of_msg_spec (Hashtbl.find auto.states u).offers));
      if IntSet.mem u winning_set then 
        Printf.bprintf buffer " (WIN)"
      else 
        Printf.bprintf buffer " (LOSE)";

      let state = Hashtbl.find auto.states u in
      let outgoing = List.filter (fun t -> t.from_state = u) auto.transitions in
      
      let next_opt = 
        if state.adversary then 
           try Some (List.find (fun t -> not (IntSet.mem t.to_state winning_set)) outgoing)
           with Not_found -> None
        else 
           match outgoing with [] -> None | h::_ -> Some h
      in
      
      match next_opt with
      | Some t -> 
         Printf.bprintf buffer "\n\t --[%s]--> " (string_of_label_set t.label);
         dfs t.to_state
      | None -> Printf.bprintf buffer " -> Deadlock"
    )
  in
  dfs start;
  Buffer.contents buffer

let transform_winning_edges (auto : TypeAutomaton.t) : (int, string list) Hashtbl.t =
  let new_transitions = ref [] in
  let winning_info = Hashtbl.create 100 in
  
  List.iter (fun t ->
    let recurse_ids = LabelSet.fold (fun l acc ->
      match l with
      | Recurse id -> id :: acc
      | _ -> acc
    ) t.label [] in

    if recurse_ids <> [] then (
      let mid_state_id = TypeAutomaton.new_state auto false in 
      Hashtbl.add winning_info mid_state_id recurse_ids;
      
      let t1 = { t with 
        to_state = mid_state_id; 
        label = t.label; 
        is_epsilon = t.is_epsilon; 
        is_recurse = false
      } in
      
      let t2 = { 
        from_state = mid_state_id; 
        to_state = t.to_state; 
        label = LabelSet.empty; 
        is_epsilon = true; 
        is_recurse = false;
        is_theta = false; 
        is_conditional = false; 
        in_winning = false 
      } in
      
      new_transitions := t1 :: t2 :: !new_transitions
    ) else (
      new_transitions := t :: !new_transitions
    )
  ) auto.transitions;
  
  auto.transitions <- !new_transitions;
  winning_info


let can_reach_avoiding (auto : TypeAutomaton.t) (start_node : int) (target_node : int) (avoid_set : IntSet.t) : bool =
  if IntSet.mem start_node avoid_set then false
  else if start_node = target_node then true
  else
    let visited = Hashtbl.create 16 in
    let queue = Queue.create () in
    Queue.add start_node queue;
    Hashtbl.add visited start_node ();
    
    let found = ref false in
    while not !found && not (Queue.is_empty queue) do
      let u = Queue.take queue in
      if u = target_node then found := true
      else
        let outgoing = List.filter (fun t -> t.from_state = u) auto.transitions in
        List.iter (fun t ->
          if not (Hashtbl.mem visited t.to_state) && not (IntSet.mem t.to_state avoid_set) then (
            Hashtbl.add visited t.to_state ();
            Queue.add t.to_state queue
          )
        ) outgoing
    done;
    !found

let can_reach_hitting (auto : TypeAutomaton.t) (start_node : int) (target_node : int) (winning_nodes : IntSet.t) : bool =
  let visited = Hashtbl.create 16 in
  let queue = Queue.create () in
  
  let start_hit = IntSet.mem start_node winning_nodes in
  Queue.add (start_node, start_hit) queue;
  Hashtbl.add visited (start_node, start_hit) ();

  let found = ref false in
  while not !found && not (Queue.is_empty queue) do
    let (u, hit) = Queue.take queue in
    
    if u = target_node then (
      if hit then found := true
    ) else (
      let outgoing = List.filter (fun t -> t.from_state = u) auto.transitions in
      List.iter (fun t ->
        let new_hit = hit || IntSet.mem t.to_state winning_nodes in
        if not (Hashtbl.mem visited (t.to_state, new_hit)) then (
          Hashtbl.add visited (t.to_state, new_hit) ();
          Queue.add (t.to_state, new_hit) queue
        )
      ) outgoing
    )
  done;
  !found

type graph_maps = {
  preds : (int, int list) Hashtbl.t;
  succs : (int, int list) Hashtbl.t;
  mutable valid_states : IntSet.t; 
}

let build_maps (auto : TypeAutomaton.t) : graph_maps =
  let preds = Hashtbl.create 100 in
  let succs = Hashtbl.create 100 in
  List.iter (fun t ->
    let p = Hashtbl.find_opt preds t.to_state |> Option.value ~default:[] in
    Hashtbl.replace preds t.to_state (t.from_state :: p);
    let s = Hashtbl.find_opt succs t.from_state |> Option.value ~default:[] in
    Hashtbl.replace succs t.from_state (t.to_state :: s)
  ) auto.transitions;
  let all_s = Hashtbl.fold (fun id _ acc -> IntSet.add id acc) auto.states IntSet.empty in
  { preds; succs; valid_states = all_s }


let compute_attractor (auto : TypeAutomaton.t) (maps : graph_maps) (target : IntSet.t) : IntSet.t =
  let attractor = ref target in
  let queue = Queue.create () in
  IntSet.iter (fun x -> Queue.add x queue) target;

  let outgoing_counts = Hashtbl.create 100 in
  
  IntSet.iter (fun u -> 
    let succs_u = Hashtbl.find_opt maps.succs u |> Option.value ~default:[] in
    let valid_succs = List.filter (fun v -> IntSet.mem v maps.valid_states) succs_u in
    Hashtbl.add outgoing_counts u (List.length valid_succs)
  ) maps.valid_states;

  while not (Queue.is_empty queue) do
    let v = Queue.take queue in
    let predecessors = Hashtbl.find_opt maps.preds v |> Option.value ~default:[] in
    
    List.iter (fun u ->
      if IntSet.mem u maps.valid_states && not (IntSet.mem u !attractor) then (
        let state_u = Hashtbl.find auto.states u in
        
        if not state_u.adversary then (
          attractor := IntSet.add u !attractor;
          Queue.add u queue
        ) else (
          let current_count = Hashtbl.find outgoing_counts u in
          let new_count = current_count - 1 in
          Hashtbl.replace outgoing_counts u new_count;
          if new_count = 0 then (
            attractor := IntSet.add u !attractor;
            Queue.add u queue
          )
        )
      )
    ) predecessors
  done;
  !attractor

let find_path (auto : TypeAutomaton.t) (start : int) (target : int) : (transition list) =
  let visited = Hashtbl.create 16 in
  let queue = Queue.create () in
  Hashtbl.add visited start None;
  Queue.add start queue;

  let rec build_path u =
    match Hashtbl.find visited u with
    | None -> []
    | Some (prev, t) -> build_path prev @ [t]
  in
  let found = ref false in
  while not !found && not (Queue.is_empty queue) do
    let u = Queue.take queue in
    if u = target then found := true
    else
      let outgoing = List.filter (fun t -> t.from_state = u) auto.transitions in
      List.iter (fun t ->
        if not (Hashtbl.mem visited t.to_state) then (
          Hashtbl.add visited t.to_state (Some (u, t));
          Queue.add t.to_state queue
        )
      ) outgoing
  done;
  if !found then
    build_path target
  else
    []

let prune_fair_loops (auto : TypeAutomaton.t) (winning_nodes : IntSet.t) (verbose : bool) : unit =
  let fair_nodes = Hashtbl.fold (fun id st acc -> 
    if st.is_fair && st.adversary then id :: acc else acc
  ) auto.states [] in

  List.iter (fun u ->
    let all_outgoing = List.filter (fun t -> t.from_state = u) auto.transitions in
    
    let edges_to_keep = ref [] in

    let edges_to_discard = ref [] in
    
    List.iter (fun t ->

       let starts_bad_loop = can_reach_avoiding auto t.to_state u winning_nodes in
    
       let starts_good_loop = can_reach_hitting auto t.to_state u winning_nodes in
       
       if starts_good_loop || not starts_bad_loop then
         edges_to_keep := t :: !edges_to_keep
        else
          edges_to_discard := (find_path auto t.to_state u)@ !edges_to_discard
    ) all_outgoing;
    if !edges_to_discard <> [] && verbose then
      (
      Printf.eprintf "[Warning] Pruning %d edges from fair loop at state %d\n" (List.length !edges_to_discard) u;
      Printf.eprintf "  Edges discarded: %s\n" (String.concat "; " (List.map string_of_transition !edges_to_discard))
      );

    
    auto.transitions <- List.filter (fun t -> 
      if t.from_state = u then List.mem t !edges_to_keep
      else (
        let ts = List.mem t !edges_to_discard in
        not ts
      )
    ) auto.transitions
  ) fair_nodes

let play_game (prod_auto : TypeAutomaton.t) (ids : identifier list) (verbose : bool) : (bool * string) =
  
  let winning_info = transform_winning_edges prod_auto in
  
  let all_winning_nodes = Hashtbl.fold (fun id _ acc -> IntSet.add id acc) winning_info IntSet.empty in
  prune_fair_loops prod_auto all_winning_nodes verbose;

  let maps = build_maps prod_auto in
  let all_states = maps.valid_states in

  let f_sets = List.map (fun req_id ->
    let f_i = Hashtbl.fold (fun node_id satisfied_ids acc ->
      if List.mem req_id satisfied_ids then IntSet.add node_id acc else acc
    ) winning_info IntSet.empty in
    (req_id, f_i)
  ) ids in

  let w = ref all_states in
  let changed = ref true in

  while !changed do
    let start_w = !w in
    let current_w = ref start_w in
    
    maps.valid_states <- start_w;

    List.iter (fun (_req_id, f_i_set) ->
      let target_in_w = IntSet.inter f_i_set start_w in
      let can_reach_f_i = compute_attractor prod_auto maps target_in_w in
      current_w := IntSet.inter !current_w can_reach_f_i
    ) f_sets;

    if IntSet.equal start_w !current_w then
      changed := false
    else (
      w := !current_w;
      changed := true
    )
  done;

  let final_winning_set = !w in
  let start_wins = IntSet.mem prod_auto.start_state final_winning_set in

  List.iter (fun t ->
    if IntSet.mem t.from_state final_winning_set && IntSet.mem t.to_state final_winning_set then
      (
      t.in_winning <- true;
      Hashtbl.find prod_auto.states t.to_state |> fun s -> s.is_winning <- true
      )
    else
      (
        t.in_winning <- false;
        if Hashtbl.mem prod_auto.states t.to_state then
          Hashtbl.find prod_auto.states t.to_state |> fun s -> s.is_winning <- false
        else Printf.eprintf "State %d not found in states table for transiton %s\n" t.to_state (string_of_transition t)
      )
  ) prod_auto.transitions;

  if start_wins then
    (true, "Compatibility verified: Player has a winning strategy.")
  else (
    let trace = find_counterexample prod_auto prod_auto.start_state final_winning_set in 
    (false, Printf.sprintf "Compatibility failed. Losing Trace:\n%s" trace)
  )