open SessionAutomaton2

module IntSet = Set.Make (Int)

let transition_has_id (t : transition) (req_id : string) =
  let progress_ids = progress_ids_of_action t.action in
  StringSet.mem req_id progress_ids

let indent_block prefix text =
  text
  |> String.split_on_char '\n'
  |> List.map (fun line -> prefix ^ line)
  |> String.concat "\n"

let get_unreachable_ids outgoing_index req_ids start_node =
  (* Explain liveness failures by finding progress IDs absent from the suffix. *)
  let visited = Hashtbl.create 16 in
  let found = Hashtbl.create 8 in
  let queue = Queue.create () in
  Hashtbl.add visited start_node ();
  Queue.add start_node queue;
  while not (Queue.is_empty queue) do
    let curr = Queue.take queue in
    let outgoing = get_outgoing_from_index outgoing_index curr in
    List.iter
      (fun t ->
        List.iter
          (fun req_id ->
            if transition_has_id t req_id then Hashtbl.replace found req_id ())
          req_ids;
        if not (Hashtbl.mem visited t.to_state) then (
          Hashtbl.add visited t.to_state ();
          Queue.add t.to_state queue))
      outgoing
  done;
  List.filter (fun req_id -> not (Hashtbl.mem found req_id)) req_ids

(* Reverse-edge index restricted to valid_region; drives the worklist below so only a state's predecessors are re-checked when its attractor membership changes. *)
let build_predecessor_index outgoing_index valid_region =
  let pred = Hashtbl.create 64 in
  IntSet.iter
    (fun state_id ->
      List.iter
        (fun t ->
          if IntSet.mem t.to_state valid_region then (
            let existing =
              match Hashtbl.find_opt pred t.to_state with
              | Some ps -> ps
              | None -> []
            in
            Hashtbl.replace pred t.to_state (state_id :: existing)))
        (get_outgoing_from_index outgoing_index state_id))
    valid_region;
  pred

(* Reachability attractor (least fixpoint, worklist-driven): states that can force reaching an ~is_good edge at least once — NOT sufficient for a Büchi/recurrence condition on its own, see compute_recurrence_region_indexed. *)
let compute_reach_attractor_indexed ~is_fair ~is_good outgoing_index
    valid_region =
  let pred_index = build_predecessor_index outgoing_index valid_region in
  let attractor = ref IntSet.empty in
  let queued = Hashtbl.create 64 in
  let worklist = Queue.create () in
  let enqueue state_id =
    if not (Hashtbl.mem queued state_id) then (
      Hashtbl.add queued state_id ();
      Queue.add state_id worklist)
  in
  IntSet.iter enqueue valid_region;
  let try_attract state_id =
    if not (IntSet.mem state_id !attractor) then (
      let outgoing = get_outgoing_from_index outgoing_index state_id in
      let edge_good t =
        IntSet.mem t.to_state valid_region
        && (is_good t || IntSet.mem t.to_state !attractor)
      in
      let all_outgoing_valid =
        outgoing <> []
        && List.for_all (fun t -> IntSet.mem t.to_state valid_region) outgoing
      in
      let reaches_again =
        if is_fair state_id then List.exists edge_good outgoing
        else all_outgoing_valid && List.for_all edge_good outgoing
      in
      if reaches_again then (
        attractor := IntSet.add state_id !attractor;
        match Hashtbl.find_opt pred_index state_id with
        | Some preds -> List.iter enqueue preds
        | None -> ()))
  in
  while not (Queue.is_empty worklist) do
    let state_id = Queue.take worklist in
    Hashtbl.remove queued state_id;
    try_attract state_id
  done;
  !attractor

(* Büchi recurrence: repeatedly shrink candidate region W to states that can reach ~is_good landing back inside the CURRENT W, re-seeding every outer pass, until it stabilizes. *)
let compute_recurrence_region_indexed ~is_fair ~is_good outgoing_index
    valid_region =
  let region = ref valid_region in
  let changed = ref true in
  while !changed do
    let next =
      compute_reach_attractor_indexed ~is_fair
        ~is_good:(fun t -> is_good t && IntSet.mem t.to_state !region)
        outgoing_index !region
    in
    if IntSet.equal next !region then changed := false else region := next
  done;
  !region

(* Clock recurrence holds on every path independent of fairness: no existential escape, since one recurring path and one never-ticking path still leaves a losing path. *)
let compute_clock_attractor_indexed outgoing_index valid_region =
  compute_recurrence_region_indexed ~is_fair:(fun _ -> false)
    ~is_good:transition_is_clock outgoing_index valid_region

(* Conjunction of two recurrence conditions: naively intersecting two independently-computed regions can drop a shared waypoint, so both are re-seeded into the shrinking joint region every outer pass. *)
let compute_conjoined_recurrence_indexed ~is_fair_a ~is_good_a ~is_fair_b
    ~is_good_b outgoing_index valid_region =
  let region = ref valid_region in
  let changed = ref true in
  while !changed do
    let region_a =
      compute_recurrence_region_indexed ~is_fair:is_fair_a ~is_good:is_good_a
        outgoing_index !region
    in
    let region_b =
      compute_recurrence_region_indexed ~is_fair:is_fair_b ~is_good:is_good_b
        outgoing_index !region
    in
    let next = IntSet.inter region_a region_b in
    if IntSet.equal next !region then changed := false else region := next
  done;
  !region

(* Round-robin monitor: r=|req_ids| copies of every state, `(state_id,k)` packed as `state_id*r+k` = waiting to see req_ids.(k); an edge carrying req_ids.(k) advances to (k+1) mod r. Turns r independently-intersected attractors (which could destructively drop a shared waypoint) into one recurring-set condition. *)
let monitor_pack r state_id k = (state_id * r) + k

let monitor_unpack r packed = (packed / r, packed mod r)

let solve_game_custom_indexed auto outgoing_index req_ids =
  let r = List.length req_ids in
  if r = 0 then
    (* compute_clock_attractor_indexed is already a full recurrence fixpoint, so a single call suffices when no progress markers are required. *)
    let all_states =
      Hashtbl.fold (fun id _ acc -> IntSet.add id acc) auto.states IntSet.empty
    in
    compute_clock_attractor_indexed outgoing_index all_states
  else
    let req_ids_arr = Array.of_list req_ids in
    let is_fair_of packed =
      let state_id, _k = monitor_unpack r packed in
      (Hashtbl.find auto.states state_id).is_fair
    in
    let monitor_outgoing : transition_outgoing_index = Hashtbl.create 64 in
    Hashtbl.iter
      (fun state_id _ ->
        let outgoing = get_outgoing_from_index outgoing_index state_id in
        for k = 0 to r - 1 do
          let monitor_transitions =
            List.map
              (fun t ->
                let advances = transition_has_id t req_ids_arr.(k) in
                let next_k = if advances then (k + 1) mod r else k in
                { t with
                  from_state = monitor_pack r state_id k;
                  to_state = monitor_pack r t.to_state next_k;
                })
              outgoing
          in
          Hashtbl.replace monitor_outgoing (monitor_pack r state_id k)
            monitor_transitions
        done)
      auto.states;
    let monitor_all =
      Hashtbl.fold
        (fun state_id _ acc ->
          let acc = ref acc in
          for k = 0 to r - 1 do
            acc := IntSet.add (monitor_pack r state_id k) !acc
          done;
          !acc)
        auto.states IntSet.empty
    in
    (* F_T: an edge is "good" (advances the counter) exactly when it moves
       from phase k to phase (k+1) mod r, i.e. its from/to differ in phase. *)
    let monitor_advances t =
      let _, from_k = monitor_unpack r t.from_state in
      let _, to_k = monitor_unpack r t.to_state in
      to_k <> from_k
    in
    (* Clock recurrence (always universal) and id-progress recurrence (existential for fair states) are conjoined so neither prunes a waypoint the other needs; transition_is_clock reads monitor transitions directly since t.action is untouched by relabeling. *)
    let winning =
      compute_conjoined_recurrence_indexed ~is_fair_a:(fun _ -> false)
        ~is_good_a:transition_is_clock ~is_fair_b:is_fair_of
        ~is_good_b:monitor_advances monitor_outgoing monitor_all
    in
    (* Conservative projection: a state wins only if EVERY reachable monitor phase wins — can only shrink the winning set relative to a phase-exact reading, never manufacture a false "compatible". *)
    let per_state_phase_wins = Hashtbl.create 64 in
    IntSet.iter
      (fun packed ->
        let state_id, _k = monitor_unpack r packed in
        Hashtbl.replace per_state_phase_wins state_id
          (1 + (try Hashtbl.find per_state_phase_wins state_id with Not_found -> 0)))
      winning;
    Hashtbl.fold
      (fun state_id _ acc ->
        let wins_count =
          try Hashtbl.find per_state_phase_wins state_id with Not_found -> 0
        in
        if wins_count = r then IntSet.add state_id acc else acc)
      auto.states IntSet.empty

let solve_game_custom auto req_ids =
  let outgoing_index = build_outgoing_index auto.transitions in
  solve_game_custom_indexed auto outgoing_index req_ids

let sanity_check_indexed auto outgoing_index =
  (* Dead-end states are closed-world synchronization failures. *)
  Hashtbl.fold
    (fun id _ acc ->
      if get_outgoing_from_index outgoing_index id = [] then id :: acc else acc)
    auto.states []

let collect_dead_ends_paths_indexed auto outgoing_index dead_ends =
  (* Keep counterexamples concrete by replaying one path to each dead end. *)
  List.map
    (fun dead_end ->
      let visited = Hashtbl.create 16 in
      let queue = Queue.create () in
      Hashtbl.add visited auto.start_state None;
      Queue.add auto.start_state queue;
      let found = ref false in
      while (not !found) && not (Queue.is_empty queue) do
        let curr = Queue.take queue in
        if curr = dead_end then found := true
        else
          get_outgoing_from_index outgoing_index curr
          |> List.iter (fun t ->
                 if not (Hashtbl.mem visited t.to_state) then (
                   Hashtbl.add visited t.to_state (Some (curr, t));
                   Queue.add t.to_state queue))
      done;
      let rec build_path state_id =
        match Hashtbl.find visited state_id with
        | None -> []
        | Some (prev, t) -> build_path prev @ [ t ]
      in
      let trace =
        if !found then
          let buffer = Buffer.create 256 in
          Printf.bprintf buffer "Trace from start state %d to dead-end state %d:\n"
            auto.start_state dead_end;
          let current = ref auto.start_state in
          List.iter
            (fun t ->
              Printf.bprintf buffer "  State %d --[%s]--> State %d\n" !current
                (string_of_action t.action) t.to_state;
              current := t.to_state)
            (build_path dead_end);
          Printf.bprintf buffer "  State %d: DEAD END\n" dead_end;
          let dead_state = Hashtbl.find auto.states dead_end in
          (match dead_state.debug_info with
          | Some info ->
              Printf.bprintf buffer "  Dead-end diagnostics:\n%s\n"
                (indent_block "    " info)
          | None -> ());
          Buffer.contents buffer
        else
          Printf.sprintf "Dead-end state %d is not reachable from start state %d"
            dead_end auto.start_state
      in
      (dead_end, trace))
    dead_ends

let list_drop n xs =
  let rec aux n xs =
    match n, xs with
    | n, xs when n <= 0 -> xs
    | _, [] -> []
    | n, _ :: rest -> aux (n - 1) rest
  in
  aux n xs

let reachable_parent_map outgoing_index start can_visit =
  let parent = Hashtbl.create 16 in
  let queue = Queue.create () in
  if can_visit start then (
    Hashtbl.add parent start None;
    Queue.add start queue);
  while not (Queue.is_empty queue) do
    let state_id = Queue.take queue in
    get_outgoing_from_index outgoing_index state_id
    |> List.iter (fun t ->
           if can_visit t.to_state && not (Hashtbl.mem parent t.to_state) then (
             Hashtbl.add parent t.to_state (Some (state_id, t));
             Queue.add t.to_state queue))
  done;
  parent

let path_from_parent_map parent state_id =
  let rec aux state_id =
    match Hashtbl.find_opt parent state_id with
    | None | Some None -> []
    | Some (Some (prev, t)) -> aux prev @ [ t ]
  in
  aux state_id

let find_cycle_avoiding outgoing_index reachable avoids_transition =
  let visited = Hashtbl.create 16 in
  let visiting = Hashtbl.create 16 in
  let result = ref None in
  let rec dfs state_id path =
    if Option.is_none !result then (
      Hashtbl.replace visiting state_id (List.length path);
      get_outgoing_from_index outgoing_index state_id
      |> List.filter (fun t ->
             avoids_transition t && Hashtbl.mem reachable t.to_state)
      |> List.iter (fun t ->
             if Option.is_none !result then
               match Hashtbl.find_opt visiting t.to_state with
               | Some index ->
                   result :=
                     Some
                       ( t.to_state,
                         list_drop index path @ [ t ] )
               | None ->
                   if not (Hashtbl.mem visited t.to_state) then
                     dfs t.to_state (path @ [ t ]));
      Hashtbl.remove visiting state_id;
      Hashtbl.replace visited state_id ())
  in
  let states =
    Hashtbl.fold (fun state_id _ acc -> state_id :: acc) reachable []
    |> List.sort compare
  in
  List.iter
    (fun state_id ->
      if Option.is_none !result && not (Hashtbl.mem visited state_id) then
        dfs state_id [])
    states;
  !result

let find_cycle_avoiding_id outgoing_index reachable req_id =
  find_cycle_avoiding outgoing_index reachable (fun t ->
      not (transition_has_id t req_id))

let find_cycle_avoiding_clock outgoing_index reachable =
  find_cycle_avoiding outgoing_index reachable (fun t ->
      not (transition_is_clock t))

let find_progress_avoiding_lasso outgoing_index start winning_set req_ids =
  let losing state_id = not (IntSet.mem state_id winning_set) in
  let reachable = reachable_parent_map outgoing_index start losing in
  req_ids
  |> List.find_map (fun req_id ->
         match find_cycle_avoiding_id outgoing_index reachable req_id with
         | None -> None
         | Some (cycle_start, cycle) ->
             Some
               ( req_id,
                 path_from_parent_map reachable cycle_start,
                 cycle_start,
                 cycle ))

let find_clock_avoiding_lasso outgoing_index start winning_set =
  let losing state_id = not (IntSet.mem state_id winning_set) in
  let reachable = reachable_parent_map outgoing_index start losing in
  match find_cycle_avoiding_clock outgoing_index reachable with
  | None -> None
  | Some (cycle_start, cycle) ->
      Some (path_from_parent_map reachable cycle_start, cycle_start, cycle)

let print_state_context buffer auto winning_set state_id =
  let st = Hashtbl.find auto.states state_id in
  let winning = IntSet.mem state_id winning_set in
  Printf.bprintf buffer "State %d [head={%s}, future={%s}] %s\n" state_id
    (string_of_msgset st.head) (string_of_msgset st.maybe_ready)
    (if winning then "(WIN)" else "(LOSE)");
  match st.debug_info with
  | Some info -> Printf.bprintf buffer "%s\n" (indent_block "    " info)
  | None -> ()

let print_transition_step buffer auto winning_set current t =
  print_state_context buffer auto winning_set current;
  Printf.bprintf buffer " --[%s]--> State %d\n" (string_of_action t.action)
    t.to_state;
  t.to_state

let find_counterexample_indexed auto outgoing_index start winning_set req_ids =
  (* Prefer a clock-starvation witness first — a cycle with no Clock transition at all is the more fundamental defect than one merely avoiding a progress $id. *)
  match find_clock_avoiding_lasso outgoing_index start winning_set with
  | Some (prefix, cycle_start, cycle) ->
      let buffer = Buffer.create 512 in
      Printf.bprintf buffer
        "Clock-starvation counterexample: repeat the cycle below forever without ever taking #.\n";
      let current = ref start in
      if prefix <> [] then
        Printf.bprintf buffer "\nPrefix to the avoiding cycle:\n";
      List.iter
        (fun t -> current := print_transition_step buffer auto winning_set !current t)
        prefix;
      Printf.bprintf buffer "\nCycle avoiding # starts at state %d:\n" cycle_start;
      current := cycle_start;
      List.iter
        (fun t -> current := print_transition_step buffer auto winning_set !current t)
        cycle;
      Printf.bprintf buffer "Back to state %d without taking #.\n" cycle_start;
      Buffer.contents buffer
  | None -> (
  (* Otherwise, prefer a real liveness witness: a reachable losing lasso avoiding one progress ID. *)
  match find_progress_avoiding_lasso outgoing_index start winning_set req_ids with
  | Some (req_id, prefix, cycle_start, cycle) ->
      let buffer = Buffer.create 512 in
      Printf.bprintf buffer
        "Liveness counterexample: repeat the cycle below forever to avoid progress $%s.\n"
        req_id;
      let current = ref start in
      if prefix <> [] then
        Printf.bprintf buffer "\nPrefix to the avoiding cycle:\n";
      List.iter
        (fun t -> current := print_transition_step buffer auto winning_set !current t)
        prefix;
      Printf.bprintf buffer "\nCycle avoiding $%s starts at state %d:\n" req_id
        cycle_start;
      current := cycle_start;
      List.iter
        (fun t -> current := print_transition_step buffer auto winning_set !current t)
        cycle;
      Printf.bprintf buffer "Back to state %d without taking $%s.\n" cycle_start
        req_id;
      Buffer.contents buffer
  | None ->
      let buffer = Buffer.create 256 in
      let visited = Hashtbl.create 16 in
      let rec dfs state_id =
        if Hashtbl.mem visited state_id then
          Printf.bprintf buffer " -> Loop at %d" state_id
        else (
          Hashtbl.add visited state_id ();
          Printf.bprintf buffer "\n";
          print_state_context buffer auto winning_set state_id;
          if not (IntSet.mem state_id winning_set) then (
            let unreachable =
              get_unreachable_ids outgoing_index req_ids state_id
            in
            if unreachable <> [] then
              Printf.bprintf buffer "    Structurally unreachable targets: %s\n"
                (String.concat ", " unreachable));
          let outgoing = get_outgoing_from_index outgoing_index state_id in
          let losing =
            if IntSet.mem state_id winning_set then []
            else
              List.filter
                (fun t -> not (IntSet.mem t.to_state winning_set))
                outgoing
          in
          match losing with
          | [] -> Printf.bprintf buffer " -> Deadlock / End of Trace"
          | t :: _ ->
              Printf.bprintf buffer " --[%s]--> " (string_of_action t.action);
              dfs t.to_state)
      in
      dfs start;
      Buffer.contents buffer)

let find_counterexample auto start winning_set req_ids =
  let outgoing_index = build_outgoing_index auto.transitions in
  find_counterexample_indexed auto outgoing_index start winning_set req_ids

let play_game auto ids =
  (* Closed compatibility is dead-end freedom plus progress for all interface IDs. *)
  recompute_state_summaries auto;
  let outgoing_index = build_outgoing_index auto.transitions in
  let dead_ends = sanity_check_indexed auto outgoing_index in
  if dead_ends <> [] then
    let traces = collect_dead_ends_paths_indexed auto outgoing_index dead_ends in
    let trace_text =
      traces |> List.map snd |> String.concat "\n\n"
    in
    (false, "Error: The automaton has dead-end states:\n" ^ trace_text)
  else
    let winning_set = solve_game_custom_indexed auto outgoing_index ids in
    Hashtbl.iter
      (fun id st -> st.is_winning <- IntSet.mem id winning_set)
      auto.states;
    if IntSet.mem auto.start_state winning_set then
      (true, "Compatible: Strategy found to satisfy all IDs.")
    else
      let trace =
        find_counterexample_indexed auto outgoing_index auto.start_state
          winning_set ids
      in
      (false, "Compatibility failed. Losing Trace:\n" ^ trace)
