open SessionAutomaton
open Lang

module IntSet = Set.Make(Int)

(* Evaluates if a specific transition emits the target req_id. *)
let transition_has_id (t : transition) (req_id : string) : bool =
  LabelSet.exists (fun l ->
    match l with
    | Recurse id -> id = req_id
    | _ -> false
  ) t.label

let get_unreachable_ids outgoing_index req_ids start_node =
  let visited = Hashtbl.create 16 in
  let queue = Queue.create () in
  let found_ids = Hashtbl.create 4 in
  
  Hashtbl.add visited start_node ();
  Queue.add start_node queue;
  
  while not (Queue.is_empty queue) do
    let curr = Queue.take queue in
    let outgoing = get_outgoing_from_index outgoing_index curr in
    List.iter (fun t ->
      (* Check if this transition contains any of our target IDs *)
      List.iter (fun req_id ->
        if transition_has_id t req_id then
          Hashtbl.replace found_ids req_id ()
      ) req_ids;
      if not (Hashtbl.mem visited t.to_state) then (
        Hashtbl.add visited t.to_state ();
        Queue.add t.to_state queue
      )
    ) outgoing
  done;
  List.filter (fun id -> not (Hashtbl.mem found_ids id)) req_ids


let find_counterexample_indexed
    (auto : TypeAutomaton.t)
    (outgoing_index : transition_outgoing_index)
    (start : int)
    (winning_set : IntSet.t)
    (req_ids : string list)
    : string =
  let buffer = Buffer.create 256 in
  let visited = Hashtbl.create 16 in
  
  let is_deadlock u = 
    (get_outgoing_from_index outgoing_index u) = []
  in

  let rec dfs u = 
    if Hashtbl.mem visited u then 
      (* Base Case 1: Reached a previously visited state (Infinite Loop / Livelock) *)
      Printf.bprintf buffer " -> Loop at %d" u
    else (
      Hashtbl.add visited u ();
      let state = Hashtbl.find auto.states u in
      
      let fairness_tag = if state.is_fair then "FAIR" else "NORMAL" in
      Printf.bprintf buffer "\nState %d [%s]\n 1. [Offers : %s]\n" 
        u fairness_tag (String.concat ", " (List.map string_of_msg_spec state.offers));
      
      let is_winning = IntSet.mem u winning_set in
      if is_winning then 
        Printf.bprintf buffer " (WIN)\n" 
      else (
        Printf.bprintf buffer " (LOSE)\n";
        
        let unreachable = get_unreachable_ids outgoing_index req_ids u in
        if unreachable <> [] then
          Printf.bprintf buffer "    [Debug] Structurally unreachable targets: %s\n" (String.concat ", " unreachable);
          
        (* 3. Print the Exact Reason for Failure *)
        let outgoing = get_outgoing_from_index outgoing_index u in
        let escape_count = List.length (List.filter (fun t -> not (IntSet.mem t.to_state winning_set)) outgoing) in
        let safe_count = List.length outgoing - escape_count in
        
        if escape_count > 0 then
          Printf.bprintf buffer "    [Debug] Safety Failure: %d outgoing path(s) escape to losing states.\n" escape_count
        else if safe_count > 0 then
          Printf.bprintf buffer "    [Debug] Liveness Failure: Trapped in a loop without reaching required targets.\n"
        else
          Printf.bprintf buffer "    [Debug] Deadlock: No outgoing transitions.\n"
      );

      let outgoing = get_outgoing_from_index outgoing_index u in
      
      (* Filter out winning branches. We only want to follow the losing trace. *)
      let losing_transitions = 
        if is_winning then []
        else List.filter (fun t -> not (IntSet.mem t.to_state winning_set)) outgoing 
      in

      let next_opt = 
        match losing_transitions with
        | [] -> None 
        | transitions ->
            match List.find_opt (fun t -> is_deadlock t.to_state) transitions with
            | Some t -> Some t (* Prioritize deadlocks to show immediate crashes *)
            | None ->
                match List.find_opt (fun t -> not (Hashtbl.mem visited t.to_state)) transitions with
                | Some t -> Some t (* Prioritize unvisited states to map out the livelock *)
                | None -> Some (List.hd transitions) (* Fallback to close the loop *)
      in
      
      match next_opt with
      | Some t -> 
         Printf.bprintf buffer "\t --[%s]--> " (string_of_label_set t.label);
         dfs t.to_state
      | None -> 
         Printf.bprintf buffer " -> Deadlock / End of Trace"
    )
  in
  dfs start;
  Buffer.contents buffer

let find_counterexample (auto : TypeAutomaton.t) (start : int) (winning_set : IntSet.t) (req_ids: string list) : string =
  let outgoing_index = build_outgoing_index auto.transitions in
  find_counterexample_indexed auto outgoing_index start winning_set req_ids

(* Computes the local fixed point for a single target ID (req_id). *)
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
        (* All paths must remain within the valid region *)
        let all_outgoing_valid = 
          (outgoing <> []) && 
          List.for_all (fun t -> IntSet.mem t.to_state valid_region) outgoing 
        in

        let is_added =
          (* Fairness permits delayed progress, not an exit into a losing region. *)
          if not all_outgoing_valid then false
          else if state.is_fair then
            (* Fair Node: Requires at least one path to make progress req_id *)
            List.exists (fun t -> 
              let has_id = transition_has_id_cached t req_id in
              let leads_to_attr = IntSet.mem t.to_state !attractor in
              has_id || leads_to_attr
            ) outgoing
          else
            (* Normal Node: Requires all paths to make progress on that req_id *)
            List.for_all (fun t ->
              let has_id = transition_has_id_cached t req_id in
              let leads_to_attr = IntSet.mem t.to_state !attractor in
              has_id || leads_to_attr
            ) outgoing
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

(* Progress-only diagnostic solver; play_game also requires recurring clocks. *)
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

(* The fast product is closed; its labels feed the same clock/progress game. *)
let play_game (auto : TypeAutomaton.t) (ids : string list) : (bool * string) =
  let module A = SessionAutomaton2 in
  let product = A.TypeAutomaton.create A.MsgSet.empty in
  Hashtbl.clear product.states;
  product.name <- auto.name;
  product.start_state <- auto.start_state;
  product.next_state_id <- auto.next_state_id;
  Hashtbl.iter (fun id state ->
    product.next_state_id <- id;
    ignore (A.TypeAutomaton.new_state product false);
    let target = Hashtbl.find product.states id in
    target.adversary <- true;
    target.is_fair <- state.is_fair) auto.states;
  product.next_state_id <- auto.next_state_id;
  List.iter (fun transition ->
    let clock = LabelSet.mem Delay transition.label in
    let action = if clock then A.Clock else
      A.Observations (LabelSet.fold (fun label observations ->
        match label with
        | Action message -> A.ObservationSet.add (A.Message message) observations
        | Recurse id -> A.ObservationSet.add (A.Progress id) observations
        | _ -> observations) transition.label A.ObservationSet.empty)
    in
    A.TypeAutomaton.add_transition product transition.from_state transition.to_state
      action { A.any_guard with require_clock = clock; forbid_clock = not clock }
      A.MsgSet.empty) auto.transitions;
  let arena = SessionGame2.build_arena auto.name product in
  let result = SessionGame2.play_arena arena ~progress_ids:ids in
  Hashtbl.iter (fun id state ->
    state.is_winning <-
      A.StringSet.mem (SessionGame2.arena_player_id id) result.winning_nodes
      || A.StringSet.mem (SessionGame2.arena_adversary_id id 0) result.winning_nodes)
    auto.states;
  let message = match result.counterexample_trace with
    | None -> result.summary
    | Some trace -> result.summary ^ "\n" ^ trace
  in
  result.compatible, message
