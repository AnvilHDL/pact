open SessionAutomaton2

module IntSet = Set.Make (Int)

let transition_has_id (t : transition) (req_id : string) =
  transition_has_progress t req_id

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

let compute_id_attractor_indexed auto outgoing_index valid_region req_id =
  (* Compute states that force one required progress ID within valid_region. *)
  let attractor = ref IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    IntSet.iter
      (fun state_id ->
        if not (IntSet.mem state_id !attractor) then (
          let state = Hashtbl.find auto.states state_id in
          let outgoing = get_outgoing_from_index outgoing_index state_id in
          let all_outgoing_valid =
            outgoing <> []
            && List.for_all
                 (fun t -> IntSet.mem t.to_state valid_region)
                 outgoing
          in
          let exists_progress =
            List.exists
              (fun t ->
                IntSet.mem t.to_state valid_region
                && (transition_has_id t req_id
                   || IntSet.mem t.to_state !attractor))
              outgoing
          in
          let reaches_progress =
            (* Fair states model environment choices, so one fair-progress path suffices. *)
            if state.is_fair then exists_progress
            else
              all_outgoing_valid
              && List.for_all
                   (fun t ->
                     transition_has_id t req_id
                     || IntSet.mem t.to_state !attractor)
                   outgoing
          in
          if reaches_progress then (
            attractor := IntSet.add state_id !attractor;
            changed := true)))
      valid_region
  done;
  !attractor

let solve_game_custom_indexed auto outgoing_index req_ids =
  (* Intersect the per-ID attractors until all required IDs are forced. *)
  let winning =
    ref
      (Hashtbl.fold
         (fun id _ acc -> IntSet.add id acc)
         auto.states IntSet.empty)
  in
  let changed = ref true in
  while !changed do
    let start = !winning in
    let current = ref start in
    List.iter
      (fun req_id ->
        if not (IntSet.is_empty !current) then
          current :=
            compute_id_attractor_indexed auto outgoing_index !current req_id)
      req_ids;
    if IntSet.equal start !current then changed := false
    else winning := !current
  done;
  !winning

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

let find_cycle_avoiding_id outgoing_index reachable req_id =
  let visited = Hashtbl.create 16 in
  let visiting = Hashtbl.create 16 in
  let result = ref None in
  let rec dfs state_id path =
    if Option.is_none !result then (
      Hashtbl.replace visiting state_id (List.length path);
      get_outgoing_from_index outgoing_index state_id
      |> List.filter (fun t ->
             (not (transition_has_id t req_id))
             && Hashtbl.mem reachable t.to_state)
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
  (* Prefer a real liveness witness: a reachable losing lasso avoiding one progress ID. *)
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
      Buffer.contents buffer

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
