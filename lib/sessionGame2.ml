open SessionAutomaton2

(* The environment chooses boundary availability and clocks; the system resolves actions. *)

let format_msgset msgs = "{" ^ string_of_msgset msgs ^ "}"

let msgset_nonempty set = not (MsgSet.is_empty set)

(* be_now = U (available now), be_future = F (may still arrive this cycle), be_clock = whether the boundary chooses the clock. *)
type boundary_env = {
  be_now : MsgSet.t;
  be_future : MsgSet.t;
  be_clock : bool;
}

let empty_boundary_env =
  { be_now = MsgSet.empty; be_future = MsgSet.empty; be_clock = false }

let string_of_boundary_env env =
  Printf.sprintf "U=%s; F=%s%s" (format_msgset env.be_now)
    (format_msgset env.be_future)
    (if env.be_clock then "; #" else "")

let html_of_boundary_env env =
  "U = " ^ html_of_msgset env.be_now ^ "; F = " ^ html_of_msgset env.be_future
  ^ if env.be_clock then "; #" else ""

let boundary_env_equal lhs rhs =
  MsgSet.equal lhs.be_now rhs.be_now
  && MsgSet.equal lhs.be_future rhs.be_future
  && lhs.be_clock = rhs.be_clock

(* A boundary move is "real" when the environment chooses a boundary message OR the clock (provide # vs withhold # is a genuine environment choice). *)
let boundary_env_nonempty env =
  msgset_nonempty env.be_now || msgset_nonempty env.be_future || env.be_clock

(* ---- Typed game arena ---- *)

type arena_node_kind =
  | ArenaPlayer (* environment chooses boundary availability (existential) *)
  | ArenaAdversary (* system resolves the actual transition (universal) *)
  | ArenaFail (* the dead-end sink ⊥ *)

type arena_node = {
  arena_node_id : string;
  arena_node_label : string;
  arena_node_kind : arena_node_kind;
  arena_product_state : int option; (* back-reference to the product state *)
  arena_boundary : boundary_env option; (* the move this q_e committed to *)
  arena_is_fair : bool; (* inferred fair-branch state metadata *)
  arena_is_adversary : bool;
}

(* Edge labels are typed so DOT, the solver, and the residual share one source; θ_e marks a boundary-availability choice, resolution edges carry the product action. *)
type edge_label =
  | BoundaryChoice of boundary_env (* player picks availability θ_e *)
  | ActionLabel of action (* adversary resolves a product transition *)
  | EpsilonLabel (* fail / structural epsilon *)

type arena_edge = {
  arena_edge_from : string;
  arena_edge_to : string;
  arena_edge_label : edge_label;
  arena_edge_action : action option; (* typed action carried by the edge *)
}

type game_arena = {
  arena_name : string;
  arena_start : string;
  arena_nodes : arena_node list;
  arena_edges : arena_edge list;
}

let string_of_edge_label = function
  | BoundaryChoice env -> "θ: " ^ string_of_boundary_env env
  | ActionLabel action -> "α = " ^(string_of_action action)
  | EpsilonLabel -> "ε"

let html_of_edge_label = function
  | BoundaryChoice env -> "θ: " ^ html_of_boundary_env env
  | ActionLabel action -> "α = " ^ (string_of_action action)
  | EpsilonLabel -> "ε"

let node_table arena =
  let table = Hashtbl.create (List.length arena.arena_nodes) in
  List.iter (fun node -> Hashtbl.replace table node.arena_node_id node)
    arena.arena_nodes;
  table

(* Outgoing edge index keyed by arena node id. *)
let arena_outgoing_index arena =
  let index = Hashtbl.create (List.length arena.arena_nodes) in
  List.iter
    (fun edge ->
      let existing =
        match Hashtbl.find_opt index edge.arena_edge_from with
        | Some es -> es
        | None -> []
      in
      Hashtbl.replace index edge.arena_edge_from (edge :: existing))
    arena.arena_edges;
  index

let arena_outgoing index node_id =
  match Hashtbl.find_opt index node_id with Some es -> es | None -> []

let edge_progress_ids edge =
  match edge.arena_edge_action with
  | Some act -> progress_ids_of_action act
  | _ -> StringSet.empty

(* ---- Compatibility game ---- *)

type game_result = {
  compatible : bool;
  winning_nodes : StringSet.t;
  selected_player_edges : arena_edge list;
  summary : string;
  counterexample_trace : string option;
}

let explain_trace ~silent name summary = function
  | None -> summary
  | Some trace when not silent -> summary ^ "\n" ^ trace
  | Some trace ->
      let file = name ^ "_losing_trace.log" in
      DebugLog.file "compat" file (fun out -> Printf.fprintf out "%s\n%s\n" summary trace);
      (match DebugLog.path "compat" file with
       | Some path -> summary ^ " Losing trace: " ^ path
       | None -> summary ^ "\n" ^ trace)

let indent_block prefix text =
  text
  |> String.split_on_char '\n'
  |> List.map (fun line -> prefix ^ line)
  |> String.concat "\n"

let edge_is_clock edge = edge.arena_edge_action = Some Clock

(* Reverse-edge index restricted to valid_region; drives the worklist below so only a node's predecessors are re-checked when its attractor membership changes. *)
let build_predecessor_index outgoing valid_region =
  let pred = Hashtbl.create 64 in
  StringSet.iter
    (fun node_id ->
      List.iter
        (fun edge ->
          if StringSet.mem edge.arena_edge_to valid_region then (
            let existing =
              match Hashtbl.find_opt pred edge.arena_edge_to with
              | Some ps -> ps
              | None -> []
            in
            Hashtbl.replace pred edge.arena_edge_to (node_id :: existing)))
        (arena_outgoing outgoing node_id))
    valid_region;
  pred

(* Reachability attractor (least fixpoint, worklist-driven): nodes that can force reaching an ~is_good edge at least once — NOT sufficient for a Büchi/recurrence condition on its own, see compute_recurrence_region. *)
let compute_reach_attractor ?(is_fair = fun (node : arena_node) -> node.arena_is_fair)
    ?player_choices node_by_id outgoing ~is_good valid_region =
  let pred_index = build_predecessor_index outgoing valid_region in
  let attractor = ref StringSet.empty in
  let queued = Hashtbl.create 64 in
  let worklist = Queue.create () in
  let enqueue node_id =
    if not (Hashtbl.mem queued node_id) then (
      Hashtbl.add queued node_id ();
      Queue.add node_id worklist)
  in
  StringSet.iter enqueue valid_region;
  let try_attract node_id =
    if not (StringSet.mem node_id !attractor) then (
      let node = Hashtbl.find node_by_id node_id in
      let edges = arena_outgoing outgoing node_id in
      let edge_good edge =
        StringSet.mem edge.arena_edge_to valid_region
        && (is_good edge || StringSet.mem edge.arena_edge_to !attractor)
      in
      let existential =
        match node.arena_node_kind with
        | ArenaPlayer -> true
        | ArenaAdversary -> is_fair node
        | ArenaFail -> false
      in
      let progresses =
        if existential then List.exists edge_good edges
        else
          edges <> []
          && List.for_all
               (fun edge -> StringSet.mem edge.arena_edge_to valid_region)
               edges
          && List.for_all edge_good edges
      in
      if progresses then (
        (* Record a move before adding this node, so an idle self-loop cannot win. *)
        (match node.arena_node_kind, player_choices with
        | ArenaPlayer, Some choices ->
            Hashtbl.replace choices node_id (List.find edge_good edges)
        | _ -> ());
        attractor := StringSet.add node_id !attractor;
        match Hashtbl.find_opt pred_index node_id with
        | Some preds -> List.iter enqueue preds
        | None -> ()))
  in
  while not (Queue.is_empty worklist) do
    let node_id = Queue.take worklist in
    Hashtbl.remove queued node_id;
    try_attract node_id
  done;
  !attractor

(* Büchi recurrence: repeatedly shrink candidate region W to nodes that can reach ~is_good landing back inside the CURRENT W, re-seeding every outer pass, until it stabilizes. *)
let compute_recurrence_region ?is_fair node_by_id outgoing ~is_good
    valid_region =
  let region = ref valid_region in
  let changed = ref true in
  while !changed do
    let next =
      compute_reach_attractor ?is_fair node_by_id outgoing
        ~is_good:(fun edge -> is_good edge && StringSet.mem edge.arena_edge_to !region)
        !region
    in
    if StringSet.equal next !region then changed := false else region := next
  done;
  !region

(* Clock recurrence holds on every path independent of fairness; is_fair:(fun _ -> false) forces universal ownership even at fair nodes. *)
let compute_clock_attractor node_by_id outgoing valid_region =
  compute_recurrence_region ~is_fair:(fun _ -> false) node_by_id outgoing
    ~is_good:edge_is_clock valid_region

(* Conjunction of two recurrence conditions: naively intersecting two independently-computed regions can drop a shared waypoint, so both are re-seeded into the shrinking joint region every outer pass. *)
let compute_conjoined_recurrence node_by_id outgoing ~is_fair_a ~is_good_a
    ~is_fair_b ~is_good_b valid_region =
  let region = ref valid_region in
  let changed = ref true in
  while !changed do
    let region_a =
      compute_recurrence_region ~is_fair:is_fair_a node_by_id outgoing
        ~is_good:is_good_a !region
    in
    let region_b =
      compute_recurrence_region ~is_fair:is_fair_b node_by_id outgoing
        ~is_good:is_good_b !region
    in
    let next = StringSet.inter region_a region_b in
    if StringSet.equal next !region then changed := false else region := next
  done;
  !region

(* Dead-end safety: nodes from which ⊥ can't be avoided; the player escapes if ANY successor is safe, while adversary AND fair nodes are unsafe if SOME successor is forced to ⊥ (fairness forces every branch eventually). *)
let forced_fail_set node_by_id outgoing all_nodes =
  let forced = ref StringSet.empty in
  List.iter
    (fun node_id ->
      match (Hashtbl.find node_by_id node_id).arena_node_kind with
      | ArenaFail -> forced := StringSet.add node_id !forced
      | _ -> ())
    (StringSet.elements all_nodes);
  let changed = ref true in
  while !changed do
    changed := false;
    StringSet.iter
      (fun node_id ->
        if not (StringSet.mem node_id !forced) then (
          let node = Hashtbl.find node_by_id node_id in
          let edges = arena_outgoing outgoing node_id in
          let succ_forced edge = StringSet.mem edge.arena_edge_to !forced in
          let unsafe =
            match node.arena_node_kind with
            | ArenaPlayer ->
                (* the environment avoids ⊥ unless every move is forced into it *)
                edges <> [] && List.for_all succ_forced edges
            | ArenaAdversary | ArenaFail ->
                (* the system / fairness can drive any ⊥ branch *)
                List.exists succ_forced edges
          in
          if unsafe then (
            forced := StringSet.add node_id !forced;
            changed := true)))
      all_nodes
  done;
  (* ⊥ self-loops, so it is always in the set; that is intended. *)
  !forced

(* Round-robin monitor: r=|req_ids| copies of every node, "<id>#<k>" = waiting to see req_ids.(k); an edge carrying req_ids.(k) advances to (k+1) mod r. Turns r independently-intersected $id attractors (which could destructively drop a shared waypoint) into one recurring-set condition. *)
let monitor_node_id node_id k = node_id ^ "#" ^ string_of_int k

let build_monitor node_by_id outgoing all_nodes req_ids =
  let r = List.length req_ids in
  let req_ids_arr = Array.of_list req_ids in
  let monitor_node_by_id = Hashtbl.create (StringSet.cardinal all_nodes * r) in
  let monitor_outgoing = Hashtbl.create (StringSet.cardinal all_nodes * r) in
  let monitor_all = ref StringSet.empty in
  StringSet.iter
    (fun node_id ->
      let node = Hashtbl.find node_by_id node_id in
      let edges = arena_outgoing outgoing node_id in
      for k = 0 to r - 1 do
        let m_id = monitor_node_id node_id k in
        monitor_all := StringSet.add m_id !monitor_all;
        Hashtbl.replace monitor_node_by_id m_id
          { node with arena_node_id = m_id };
        let advances edge = StringSet.mem req_ids_arr.(k) (edge_progress_ids edge) in
        let monitor_edges =
          List.map
            (fun edge ->
              let next_k = if advances edge then (k + 1) mod r else k in
              {
                edge with
                arena_edge_from = m_id;
                arena_edge_to = monitor_node_id edge.arena_edge_to next_k;
              })
            edges
        in
        Hashtbl.replace monitor_outgoing m_id monitor_edges
      done)
    all_nodes;
  (monitor_node_by_id, monitor_outgoing, !monitor_all)

(* A one-phase monitor advances on its marker even though its phase stays zero. *)
let monitor_edge_advances req_ids edge =
  let suffix = String.rindex edge.arena_edge_from '#' + 1 in
  let phase = int_of_string (String.sub edge.arena_edge_from suffix
    (String.length edge.arena_edge_from - suffix)) in
  StringSet.mem req_ids.(phase) (edge_progress_ids edge)

(* Winning region: clock-recurrence (always universal) AND id-progress-recurrence (existential for fair nodes), conjoined on the SAME monitor product so they share one outer fixpoint. *)
let solve_region node_by_id outgoing all_nodes req_ids =
  if req_ids = [] then
    (* compute_clock_attractor is already a full recurrence fixpoint, so a single call suffices when no progress markers are required. *)
    compute_clock_attractor node_by_id outgoing all_nodes
  else
    let monitor_node_by_id, monitor_outgoing, monitor_all =
      build_monitor node_by_id outgoing all_nodes req_ids
    in
    let advances = monitor_edge_advances (Array.of_list req_ids) in
    let winning =
      compute_conjoined_recurrence monitor_node_by_id monitor_outgoing
        ~is_fair_a:(fun _ -> false) ~is_good_a:edge_is_clock
        ~is_fair_b:(fun node -> node.arena_is_fair) ~is_good_b:advances
        monitor_all
    in
    (* Conservative projection: a node wins only if EVERY phase copy wins — can only shrink the winning set relative to a phase-exact reading, never manufacture a false "compatible". *)
    let r = List.length req_ids in
    StringSet.filter
      (fun node_id ->
        let rec all_phases_win k =
          k >= r
          || (StringSet.mem (monitor_node_id node_id k) winning
             && all_phases_win (k + 1))
        in
        all_phases_win 0)
      all_nodes

(* ⊥ emits no $id and can never satisfy a non-empty required set; kept winning when T=∅ since dead-end freedom is then the only safety obligation. *)
let drop_fail_when_required node_by_id req_ids winning =
  if req_ids = [] then winning
  else
    StringSet.filter
      (fun node_id ->
        match (Hashtbl.find node_by_id node_id).arena_node_kind with
        | ArenaFail -> false
        | _ -> true)
      winning

(* Collect player choices that stay within the winning region. *)
let select_player_edges arena outgoing winning =
  List.concat_map
    (fun node ->
      match node.arena_node_kind with
      | ArenaPlayer when StringSet.mem node.arena_node_id winning ->
          arena_outgoing outgoing node.arena_node_id
          |> List.filter (fun edge -> StringSet.mem edge.arena_edge_to winning)
      | _ -> [])
    arena.arena_nodes

(* Walk one losing path from the start for a compact counterexample. *)
let losing_trace node_by_id outgoing winning start =
  let buffer = Buffer.create 256 in
  let visited = Hashtbl.create 16 in
  let rec walk node_id =
    if Hashtbl.mem visited node_id then
      Printf.bprintf buffer "\n -> loop at %s" node_id
    else (
      Hashtbl.add visited node_id ();
      let node = Hashtbl.find node_by_id node_id in
      let win = StringSet.mem node_id winning in
      Printf.bprintf buffer "\n%s [%s] %s" node_id
        (match node.arena_node_kind with
        | ArenaPlayer -> "player"
        | ArenaAdversary -> "adversary"
        | ArenaFail -> "fail")
        (if win then "(WIN)" else "(LOSE)");
      if not win then
        let edges = arena_outgoing outgoing node_id in
        let losing =
          List.filter
            (fun edge -> not (StringSet.mem edge.arena_edge_to winning))
            edges
        in
        match losing with
        | [] -> Printf.bprintf buffer "\n -> deadlock / end of trace"
        | edge :: _ ->
            Printf.bprintf buffer "\n --[%s]--> "
              (string_of_edge_label edge.arena_edge_label);
            walk edge.arena_edge_to)
  in
  walk start;
  Buffer.contents buffer

let list_drop n xs =
  let rec aux n xs =
    match (n, xs) with
    | n, xs when n <= 0 -> xs
    | _, [] -> []
    | n, _ :: rest -> aux (n - 1) rest
  in
  aux n xs

(* Reachability parent map from start over edges into `can_visit`. *)
let reachable_parent_map outgoing start can_visit =
  let parent = Hashtbl.create 16 in
  let queue = Queue.create () in
  if can_visit start then (
    Hashtbl.add parent start None;
    Queue.add start queue);
  while not (Queue.is_empty queue) do
    let node_id = Queue.take queue in
    arena_outgoing outgoing node_id
    |> List.iter (fun edge ->
           if can_visit edge.arena_edge_to
              && not (Hashtbl.mem parent edge.arena_edge_to) then (
             Hashtbl.add parent edge.arena_edge_to (Some (node_id, edge));
             Queue.add edge.arena_edge_to queue))
  done;
  parent

let path_from_parent_map parent node_id =
  let rec aux node_id =
    match Hashtbl.find_opt parent node_id with
    | None | Some None -> []
    | Some (Some (prev, edge)) -> aux prev @ [ edge ]
  in
  aux node_id

let find_cycle_avoiding outgoing reachable avoids_edge =
  let visited = Hashtbl.create 16 in
  let visiting = Hashtbl.create 16 in
  let result = ref None in
  let rec dfs node_id path =
    if Option.is_none !result then (
      Hashtbl.replace visiting node_id (List.length path);
      arena_outgoing outgoing node_id
      |> List.filter (fun edge ->
             avoids_edge edge && Hashtbl.mem reachable edge.arena_edge_to)
      |> List.iter (fun edge ->
             if Option.is_none !result then
               match Hashtbl.find_opt visiting edge.arena_edge_to with
               | Some index ->
                   result :=
                     Some
                       ( edge.arena_edge_to,
                         list_drop index path @ [ edge ] )
               | None ->
                   if not (Hashtbl.mem visited edge.arena_edge_to) then
                     dfs edge.arena_edge_to (path @ [ edge ]));
      Hashtbl.remove visiting node_id;
      Hashtbl.replace visited node_id ())
  in
  let node_ids = Hashtbl.fold (fun node_id _ acc -> node_id :: acc) reachable [] in
  List.iter
    (fun node_id ->
      if Option.is_none !result && not (Hashtbl.mem visited node_id) then
        dfs node_id [])
    node_ids;
  !result

let find_clock_avoiding_lasso outgoing start winning =
  let losing node_id = not (StringSet.mem node_id winning) in
  let reachable = reachable_parent_map outgoing start losing in
  match
    find_cycle_avoiding outgoing reachable (fun edge -> not (edge_is_clock edge))
  with
  | None -> None
  | Some (cycle_start, cycle) ->
      Some (path_from_parent_map reachable cycle_start, cycle_start, cycle)

let find_progress_avoiding_lasso outgoing start winning req_ids =
  let losing node_id = not (StringSet.mem node_id winning) in
  let reachable = reachable_parent_map outgoing start losing in
  req_ids
  |> List.find_map (fun req_id ->
         match
           find_cycle_avoiding outgoing reachable (fun edge ->
               not (StringSet.mem req_id (edge_progress_ids edge)))
         with
         | None -> None
         | Some (cycle_start, cycle) ->
             Some
               ( req_id,
                 path_from_parent_map reachable cycle_start,
                 cycle_start,
                 cycle ))

(* Each removed layer either avoids the event or enters an earlier layer.
   Keep every player move; select only the adversary's spoiling moves. *)
let recurrence_counterstrategy node_by_id outgoing ~is_fair ~is_good all_nodes =
  let region = ref all_nodes in
  let restricted = Hashtbl.create (StringSet.cardinal all_nodes) in
  let changed = ref true in
  while !changed do
    let next =
      compute_reach_attractor ~is_fair node_by_id outgoing ~is_good !region
    in
    let removed = StringSet.diff !region next in
    StringSet.iter (fun node_id ->
      let node = Hashtbl.find node_by_id node_id in
      let edges = arena_outgoing outgoing node_id in
      let keep_all = match node.arena_node_kind with
        | ArenaPlayer -> true
        | ArenaAdversary -> is_fair node
        | ArenaFail -> false
      in
      let spoiling =
        if keep_all then edges
        else
          match List.find_opt (fun edge ->
            not (StringSet.mem edge.arena_edge_to !region)
            || (StringSet.mem edge.arena_edge_to removed && not (is_good edge))) edges with
          | Some edge -> [edge]
          | None -> []
      in
      Hashtbl.add restricted node_id spoiling) removed;
    changed := not (StringSet.is_empty removed);
    region := next
  done;
  (!region, restricted)

(* Show progress starvation while the environment still forces recurring clocks. *)
let with_clock_strategy node_by_id outgoing all_nodes =
  let region = compute_clock_attractor node_by_id outgoing all_nodes in
  let choices = Hashtbl.create (StringSet.cardinal region) in
  ignore (compute_reach_attractor ~is_fair:(fun _ -> false)
    ~player_choices:choices node_by_id outgoing ~is_good:edge_is_clock region
    : StringSet.t);
  let restricted = Hashtbl.create (StringSet.cardinal region) in
  StringSet.iter (fun node_id ->
    let edges = match Hashtbl.find_opt choices node_id with
      | Some edge -> [edge]
      | None -> arena_outgoing outgoing node_id
    in
    Hashtbl.add restricted node_id edges) region;
  restricted

let cycle_respects_fairness node_by_id outgoing cycle =
  List.for_all (fun edge ->
    let node = Hashtbl.find node_by_id edge.arena_edge_from in
    match node.arena_node_kind with
    | ArenaAdversary when node.arena_is_fair ->
        List.for_all (fun branch -> List.mem branch cycle)
          (arena_outgoing outgoing node.arena_node_id)
    | _ -> true) cycle

let print_node_context buffer node_by_id winning node_id =
  let node = Hashtbl.find node_by_id node_id in
  let win = StringSet.mem node_id winning in
  Printf.bprintf buffer "%s [%s] %s" node_id
    (match node.arena_node_kind with
    | ArenaPlayer -> "player"
    | ArenaAdversary -> "adversary"
    | ArenaFail -> "fail")
    (if win then "(WIN)" else "(LOSE)")

let print_edge_step buffer node_by_id winning current edge =
  print_node_context buffer node_by_id winning current;
  Printf.bprintf buffer "\n --[%s]--> " (string_of_edge_label edge.arena_edge_label);
  edge.arena_edge_to

(* A cycle explains rejection only when the adversary can sustain the failure. *)
let find_counterexample node_by_id outgoing winning start req_ids =
  let all_nodes = Hashtbl.fold (fun id _ acc -> StringSet.add id acc)
    node_by_id StringSet.empty in
  let clock_winning, clock_spoiler =
    recurrence_counterstrategy node_by_id outgoing ~is_fair:(fun _ -> false)
      ~is_good:edge_is_clock all_nodes
  in
  let witness =
    if not (StringSet.mem start clock_winning) then
      find_clock_avoiding_lasso clock_spoiler start clock_winning
      |> Option.map (fun (prefix, cycle_start, cycle) ->
        ("Clock-starvation counterexample: the adversary can eventually prevent every #.\n",
         "#", prefix, cycle_start, cycle))
    else
      List.find_map (fun req_id ->
        let progress_winning, progress_spoiler =
          recurrence_counterstrategy node_by_id outgoing
            ~is_fair:(fun node -> node.arena_is_fair)
            ~is_good:(fun edge -> StringSet.mem req_id (edge_progress_ids edge))
            all_nodes
        in
        if StringSet.mem start progress_winning then None
        else
          let losing = StringSet.diff all_nodes progress_winning in
          let clocked = with_clock_strategy node_by_id progress_spoiler losing in
          match find_progress_avoiding_lasso clocked start progress_winning [req_id] with
          | Some (req_id, prefix, cycle_start, cycle)
            when cycle_respects_fairness node_by_id outgoing cycle ->
              Some (Printf.sprintf
                "Progress-starvation counterexample: the adversary can eventually prevent $%s. This play keeps clocks recurring.\n"
                req_id, "$" ^ req_id, prefix, cycle_start, cycle)
          | _ -> None) req_ids
  in
  match witness with
  | Some (description, avoided, prefix, cycle_start, cycle) ->
      let buffer = Buffer.create 512 in
      Buffer.add_string buffer description;
      let current = ref start in
      if prefix <> [] then Printf.bprintf buffer "\nPrefix to the avoiding cycle:\n";
      List.iter (fun edge ->
        current := print_edge_step buffer node_by_id winning !current edge) prefix;
      Printf.bprintf buffer "\nCycle avoiding %s starts at %s:\n" avoided cycle_start;
      current := cycle_start;
      List.iter (fun edge ->
        current := print_edge_step buffer node_by_id winning !current edge) cycle;
      Printf.bprintf buffer "Back to %s without taking %s.\n" cycle_start avoided;
      Buffer.contents buffer
  | None ->
      "No joint winning strategy for clock and progress recurrence.\n\
       No certified cycle was reconstructed; the following walk is illustrative.\n"
      ^ losing_trace node_by_id outgoing winning start

let play_arena arena ~progress_ids =
  let node_by_id = node_table arena in
  let outgoing = arena_outgoing_index arena in
  let all_nodes =
    List.fold_left
      (fun acc node -> StringSet.add node.arena_node_id acc)
      StringSet.empty arena.arena_nodes
  in
  (* Safety (dead-end freedom) first, then liveness — a node from which ⊥ is unavoidable is losing regardless of progress. *)
  let forced_fail = forced_fail_set node_by_id outgoing all_nodes in
  let safe_nodes = StringSet.diff all_nodes forced_fail in
  let winning =
    solve_region node_by_id outgoing safe_nodes progress_ids
    |> drop_fail_when_required node_by_id progress_ids
    |> fun w -> StringSet.diff w forced_fail
  in
  let compatible = StringSet.mem arena.arena_start winning in
  let selected_player_edges = select_player_edges arena outgoing winning in
  let summary =
    if compatible then
      Printf.sprintf
        "Compatible: winning strategy from %s (required {%s})."
        arena.arena_start
        (String.concat "," progress_ids)
    else
      Printf.sprintf "Incompatible: no winning strategy from %s."
        arena.arena_start
  in
  let counterexample_trace =
    if compatible then None
    else
      Some
        (indent_block "  "
           (find_counterexample node_by_id outgoing winning arena.arena_start
              progress_ids))
  in
  { compatible; winning_nodes = winning; selected_player_edges; summary;
    counterexample_trace }

let boundary_of_transition t =
  {
    be_now = t.boundary_now;
    be_future = t.boundary_future;
    be_clock = transition_is_clock t;
  }

let unique_boundary_moves moves =
  List.fold_left
    (fun acc move ->
      if List.exists (boundary_env_equal move) acc then acc else move :: acc)
    [] moves
  |> List.rev

let arena_player_id state_id = Printf.sprintf "q%dP" state_id

let arena_adversary_id state_id move_index =
  Printf.sprintf "q%d_e%d" state_id move_index

let arena_fail_id = "bottom"

let move_index moves move =
  let rec aux index = function
    | [] -> raise Not_found
    | candidate :: rest ->
        if boundary_env_equal candidate move then index else aux (index + 1) rest
  in
  aux 0 moves

let build_arena name product =
  recompute_state_summaries product;
  let outgoing = build_outgoing_index product.transitions in
  let state_ids =
    Hashtbl.fold (fun id _ acc -> id :: acc) product.states []
    |> List.sort compare
  in
  let moves_by_state = Hashtbl.create 32 in
  List.iter
    (fun state_id ->
      let transitions = get_outgoing_from_index outgoing state_id in
      let moves =
        match transitions with
        | [] -> [ empty_boundary_env ]
        | _ -> transitions |> List.map boundary_of_transition |> unique_boundary_moves
      in
      Hashtbl.add moves_by_state state_id moves)
    state_ids;
  let nodes = Hashtbl.create 64 in
  let edges = ref [] in
  let add_node node =
    if not (Hashtbl.mem nodes node.arena_node_id) then
      Hashtbl.add nodes node.arena_node_id node
  in
  let add_edge ?action from_node to_node label =
    edges :=
      {
        arena_edge_from = from_node;
        arena_edge_to = to_node;
        arena_edge_label = label;
        arena_edge_action = action;
      }
      :: !edges
  in
  (* A state is a player state when it has any real boundary move; be_clock folds the clock in so no special-casing is needed. *)
  let has_player_state state_id =
    Hashtbl.find moves_by_state state_id |> List.exists boundary_env_nonempty
  in
  let entry state_id =
    if has_player_state state_id then arena_player_id state_id
    else arena_adversary_id state_id 0
  in
  let state_flags state_id =
    let st = Hashtbl.find product.states state_id in
    (st.is_fair, st.adversary)
  in
  List.iter
    (fun state_id ->
      let moves = Hashtbl.find moves_by_state state_id in
      let is_fair, is_adversary = state_flags state_id in
      if has_player_state state_id then
        add_node
          {
            arena_node_id = arena_player_id state_id;
            arena_node_label = Printf.sprintf "q%dP" state_id;
            arena_node_kind = ArenaPlayer;
            arena_product_state = Some state_id;
            arena_boundary = None;
            arena_is_fair = is_fair;
            arena_is_adversary = is_adversary;
          };
      List.iteri
        (fun index move ->
          let adv_id = arena_adversary_id state_id index in
          add_node
            {
              arena_node_id = adv_id;
              arena_node_label =
                Printf.sprintf "q%d\n%s" state_id
                  (string_of_boundary_env move);
              arena_node_kind = ArenaAdversary;
              arena_product_state = Some state_id;
              arena_boundary = Some move;
              arena_is_fair = is_fair;
              arena_is_adversary = is_adversary;
            };
          if has_player_state state_id then
            add_edge (arena_player_id state_id) adv_id (BoundaryChoice move))
        moves)
    state_ids;
  add_node
    {
      arena_node_id = arena_fail_id;
      arena_node_label = "bottom";
      arena_node_kind = ArenaFail;
      arena_product_state = None;
      arena_boundary = None;
      arena_is_fair = false;
      arena_is_adversary = true;
    };
  List.iter
    (fun state_id ->
      let moves = Hashtbl.find moves_by_state state_id in
      let transitions = get_outgoing_from_index outgoing state_id in
      List.iter
        (fun move ->
          let index = move_index moves move in
          let adv_id = arena_adversary_id state_id index in
          let matching =
            List.filter
              (fun t -> boundary_env_equal (boundary_of_transition t) move)
              transitions
          in
          match matching with
          | [] -> add_edge adv_id arena_fail_id EpsilonLabel
          | _ ->
              List.iter
                (fun t ->
                  add_edge ~action:t.action adv_id (entry t.to_state)
                    (ActionLabel t.action))
                matching)
        moves)
    state_ids;
  add_edge arena_fail_id arena_fail_id EpsilonLabel;
  {
    arena_name = name;
    arena_start = entry product.start_state;
    arena_nodes =
      Hashtbl.fold (fun _ node acc -> node :: acc) nodes []
      |> List.sort (fun a b -> String.compare a.arena_node_id b.arena_node_id);
    arena_edges = List.rev !edges;
  }

let print_arena_dot arena out =
  let dot_id id = "\"" ^ escape_dot id ^ "\"" in
  let html_label text = html_of_text_block text in
  let node_attrs kind =
    match kind with
    | ArenaPlayer -> "shape=diamond,color=darkgreen"
    | ArenaAdversary -> "shape=box,color=black"
    | ArenaFail -> "shape=doublecircle,color=red"
  in
  try
    Printf.fprintf out "digraph CompatibilityArena {\n";
    Printf.fprintf out "  rankdir=LR;\n";
    Printf.fprintf out "  label=\"%s\";\n" (escape_dot arena.arena_name);
    Printf.fprintf out "  __start [shape=none,label=\"\"];\n";
    Printf.fprintf out "  __start -> %s [color=grey];\n"
      (dot_id arena.arena_start);
    List.iter
      (fun node ->
        Printf.fprintf out "  %s [%s,label=<%s>];\n"
          (dot_id node.arena_node_id)
          (node_attrs node.arena_node_kind)
          (html_label node.arena_node_label))
      arena.arena_nodes;
    List.iter
      (fun edge ->
        Printf.fprintf out "  %s -> %s [label=<%s>];\n"
          (dot_id edge.arena_edge_from)
          (dot_id edge.arena_edge_to)
          (html_of_edge_label edge.arena_edge_label))
      arena.arena_edges;
    Printf.fprintf out "}\n"
  with exn -> raise exn


let play_game product progress_ids =
  let arena = build_arena product.name product in
  let result = play_arena arena ~progress_ids in
  let explanation = match result.counterexample_trace with
    | None -> result.summary
    | Some trace -> result.summary ^ "\n" ^ trace
  in
  (result.compatible, explanation)
