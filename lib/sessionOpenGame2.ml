open SessionAutomaton2

(* Phase 3/4 foundation: boundary environments, the typed game arena, and the
   open Rabin game solver. This module is opened by SessionOpenCompatiblity2,
   so all types the compat module and the residual builder share live here to
   avoid a module cycle. *)

let format_msgset msgs = "{" ^ string_of_msgset msgs ^ "}"

let msgset_nonempty set = not (MsgSet.is_empty set)

(* One-step boundary environment offered by the external environment (player).
   be_now = U (available now), be_future = F (may still arrive this cycle),
   be_clock = whether the boundary chooses the clock. *)
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

(* A boundary move is "real" (creating a player/environment node) when the
   environment chooses a boundary message OR the shared clock. The clock is an
   environment-controlled boundary action (provide # vs withhold #), so be_clock
   is a genuine environment choice and must be split like a boundary message. *)
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

(* Edge labels are typed so DOT, the solver, and the residual share one source.
   The θ_e label marks a player's boundary-availability choice (no observable
   action); resolution edges carry the underlying product action. *)
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

type open_game_arena = {
  arena_name : string;
  arena_start : string;
  arena_nodes : arena_node list;
  arena_edges : arena_edge list;
}

let string_of_edge_label = function
  | BoundaryChoice env -> "θ: " ^ string_of_boundary_env env
  | ActionLabel action -> string_of_action action
  | EpsilonLabel -> "ε"

let html_of_edge_label = function
  | BoundaryChoice env -> "θ: " ^ html_of_boundary_env env
  | ActionLabel action -> html_of_action action
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
  | Some (Progress ids) -> ids
  | _ -> StringSet.empty

(* ---- Open Rabin game ---- *)

type open_game_result = {
  compatible : bool;
  winning_nodes : StringSet.t;
  selected_player_edges : arena_edge list;
  summary : string;
  counterexample_trace : string option;
}

let indent_block prefix text =
  text
  |> String.split_on_char '\n'
  |> List.map (fun line -> prefix ^ line)
  |> String.concat "\n"

(* Attractor for one required progress id, keyed on node ownership:
   - player nodes win existentially (one good successor suffices),
   - adversary/fail nodes win universally (all successors must stay good).
   This mirrors sessionGame2.compute_id_attractor_indexed but the ∃/∀ split is
   by arena_node_kind, not by an is_fair flag. *)
let compute_id_attractor node_by_id outgoing valid_region req_id =
  let attractor = ref StringSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    StringSet.iter
      (fun node_id ->
        if not (StringSet.mem node_id !attractor) then (
          let node = Hashtbl.find node_by_id node_id in
          let edges = arena_outgoing outgoing node_id in
          let edge_good edge =
            StringSet.mem edge.arena_edge_to valid_region
            && (StringSet.mem req_id (edge_progress_ids edge)
               || StringSet.mem edge.arena_edge_to !attractor)
          in
          (* Existential nodes (player choices and inferred fair-branch states)
             win if one move stays good; universal (system) nodes need all moves
             good. This matches the closed solver's is_fair existential rule and
             realizes "unfair suffixes are allowed to win". *)
          let existential =
            match node.arena_node_kind with
            | ArenaPlayer -> true
            | ArenaAdversary -> node.arena_is_fair
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
            attractor := StringSet.add node_id !attractor;
            changed := true)))
      valid_region
  done;
  !attractor

let edge_is_clock edge = edge.arena_edge_action = Some Clock

(* Attractor for # ∈ Inf(π), required on every path (paper Win_T) independent
   of fairness/progress — mirrors sessionGame2.compute_clock_attractor_indexed.
   Player nodes stay existential (the environment is the friendly quantifier
   for every property in this game, so it only needs one move that keeps
   ticking), but adversary nodes are ALWAYS universal here, even when
   arena_is_fair: unlike the $id property, there is no fair-suffix escape for
   clock recurrence — a fair adversary node with one path that never ticks
   still has a losing (non-recurring) path, which alone makes it non-winning
   for this property. *)
let compute_clock_attractor node_by_id outgoing valid_region =
  let attractor = ref StringSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    StringSet.iter
      (fun node_id ->
        if not (StringSet.mem node_id !attractor) then (
          let node = Hashtbl.find node_by_id node_id in
          let edges = arena_outgoing outgoing node_id in
          let edge_good edge =
            StringSet.mem edge.arena_edge_to valid_region
            && (edge_is_clock edge || StringSet.mem edge.arena_edge_to !attractor)
          in
          let progresses =
            match node.arena_node_kind with
            | ArenaPlayer -> List.exists edge_good edges
            | ArenaAdversary | ArenaFail ->
                edges <> []
                && List.for_all
                     (fun edge -> StringSet.mem edge.arena_edge_to valid_region)
                     edges
                && List.for_all edge_good edges
          in
          if progresses then (
            attractor := StringSet.add node_id !attractor;
            changed := true)))
      valid_region
  done;
  !attractor

(* Dead-end safety (closed solver's sanity_check, lifted to the arena): the set
   of nodes from which ⊥ cannot be avoided. ⊥ is the seed. For *safety*, ownership
   is dual to liveness: the player (our friend) escapes ⊥ if ANY successor is
   safe, while adversary AND fair nodes are unsafe if SOME successor is forced to
   ⊥ — fairness forces every branch to be taken eventually, so a fair node with a
   reachable dead-end is itself a synchronization hazard. Any node in this set is
   losing, independent of liveness. *)
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

(* Winning region: every required id must be forced infinitely often, AND
   # ∈ Inf(π) on every path (paper Win_T, unconditional on fairness/progress).
   The clock-recurrence requirement is a nested outer greatest-fixpoint
   (mirrors sessionGame2.solve_game_custom_indexed): repeatedly shrink the
   candidate region to states that can force reaching Clock again WITHIN the
   current region, then intersect with the per-id progress attractors, until
   it stabilizes. With an empty required id set the inner loop leaves the
   region untouched, so the clock-recurrence check alone still applies. *)
let solve_open_region node_by_id outgoing all_nodes req_ids =
  let winning = ref all_nodes in
  let outer_changed = ref true in
  while !outer_changed do
    let outer_start = !winning in
    let region = ref (compute_clock_attractor node_by_id outgoing !winning) in
    let changed = ref true in
    while !changed do
      let start = !region in
      let current = ref start in
      List.iter
        (fun req_id ->
          if not (StringSet.is_empty !current) then
            current := compute_id_attractor node_by_id outgoing !current req_id)
        req_ids;
      if StringSet.equal start !current then changed := false
      else region := !current
    done;
    winning := !region;
    if StringSet.equal outer_start !winning then outer_changed := false
  done;
  !winning

(* The ⊥ sink emits no $id, so it can never satisfy a non-empty required set;
   when T = ∅ it is kept winning (dead-end freedom is then the only safety
   obligation, enforced because q_e with no resolution edges go to ⊥). *)
let drop_fail_when_required node_by_id req_ids winning =
  if req_ids = [] then winning
  else
    StringSet.filter
      (fun node_id ->
        match (Hashtbl.find node_by_id node_id).arena_node_kind with
        | ArenaFail -> false
        | _ -> true)
      winning

(* Record every player boundary choice that stays winning. The
   residual exposes all of these so it remains the full open type. *)
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

(* Restrict reachability (from start, over edges into `can_visit` nodes) to a
   parent map, mirroring sessionGame2.reachable_parent_map for the arena's
   string-keyed nodes. *)
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

(* Prefer a clock-starvation witness first (# ∈ Inf(π) is required
   unconditionally, paper Win_T), falling back to a progress-avoiding cycle,
   and only then the generic arbitrary-successor walk — mirrors
   sessionGame2.find_counterexample_indexed. *)
let find_counterexample node_by_id outgoing winning start req_ids =
  match find_clock_avoiding_lasso outgoing start winning with
  | Some (prefix, cycle_start, cycle) ->
      let buffer = Buffer.create 512 in
      Printf.bprintf buffer
        "Clock-starvation counterexample: repeat the cycle below forever without ever taking #.\n";
      let current = ref start in
      if prefix <> [] then Printf.bprintf buffer "\nPrefix to the avoiding cycle:\n";
      List.iter
        (fun edge -> current := print_edge_step buffer node_by_id winning !current edge)
        prefix;
      Printf.bprintf buffer "\nCycle avoiding # starts at %s:\n" cycle_start;
      current := cycle_start;
      List.iter
        (fun edge -> current := print_edge_step buffer node_by_id winning !current edge)
        cycle;
      Printf.bprintf buffer "Back to %s without taking #.\n" cycle_start;
      Buffer.contents buffer
  | None -> (
      match find_progress_avoiding_lasso outgoing start winning req_ids with
      | Some (req_id, prefix, cycle_start, cycle) ->
          let buffer = Buffer.create 512 in
          Printf.bprintf buffer
            "Liveness counterexample: repeat the cycle below forever to avoid progress $%s.\n"
            req_id;
          let current = ref start in
          if prefix <> [] then
            Printf.bprintf buffer "\nPrefix to the avoiding cycle:\n";
          List.iter
            (fun edge ->
              current := print_edge_step buffer node_by_id winning !current edge)
            prefix;
          Printf.bprintf buffer "\nCycle avoiding $%s starts at %s:\n" req_id
            cycle_start;
          current := cycle_start;
          List.iter
            (fun edge ->
              current := print_edge_step buffer node_by_id winning !current edge)
            cycle;
          Printf.bprintf buffer "Back to %s without taking $%s.\n" cycle_start
            req_id;
          Buffer.contents buffer
      | None -> losing_trace node_by_id outgoing winning start)

let play_open_game arena ~progress_ids =
  let node_by_id = node_table arena in
  let outgoing = arena_outgoing_index arena in
  let all_nodes =
    List.fold_left
      (fun acc node -> StringSet.add node.arena_node_id acc)
      StringSet.empty arena.arena_nodes
  in
  (* Safety first (dead-end freedom), then liveness. A node from which ⊥ is
     unavoidable is losing regardless of progress, matching the closed solver's
     dead-end check preceding the liveness game. *)
  let forced_fail = forced_fail_set node_by_id outgoing all_nodes in
  let safe_nodes = StringSet.diff all_nodes forced_fail in
  let winning =
    solve_open_region node_by_id outgoing safe_nodes progress_ids
    |> drop_fail_when_required node_by_id progress_ids
    |> fun w -> StringSet.diff w forced_fail
  in
  let compatible = StringSet.mem arena.arena_start winning in
  let selected_player_edges = select_player_edges arena outgoing winning in
  let summary =
    if compatible then
      Printf.sprintf
        "Open compatible: winning strategy from %s (required {%s})."
        arena.arena_start
        (String.concat "," progress_ids)
    else
      Printf.sprintf "Open incompatible: no winning strategy from %s."
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
