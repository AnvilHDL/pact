open Lang
open Except
open SessionAutomaton2
open SessionBuildAutomaton2
open SessionOpenGame2

type open_member_source =
  | Direct
  | Interface of identifier

type open_member_context = {
  member_id : identifier;
  preprocessed_type : session_type ast_node;
  automaton : typeAutomaton;
  message_set : MsgSet.t;
  source_kind : open_member_source;
}

type open_pair_intersection = {
  left_member_id : identifier;
  right_member_id : identifier;
  shared_messages : MsgSet.t;
}

(* One incremental composition step: compose the running composite with the
   next member, solve the game, and (on success) hide the just-checked
   interface to form the residual used by the next step. *)
type open_step_result = {
  composition_name : string;
  residual_name : string;
  step_progress_ids : string list;
  step_internal_messages : MsgSet.t;
  step_boundary_messages : MsgSet.t;
  step_product_dot_path : string;
  step_arena_dot_path : string;
  step_residual_dot_path : string option;
  step_game_result : open_game_result;
}

type open_pool_context = {
  pool_id : identifier;
  members : open_member_context list;
  pairwise_intersections : open_pair_intersection list;
  mutable product_dot_paths : string list;
  mutable arena_dot_path : string option;
  mutable step_results : open_step_result list;
}

let source_kind_string = function
  | Direct -> "direct"
  | Interface _ -> "interface"

let format_msgset msgs = "{" ^ string_of_msgset msgs ^ "}"

let lookup_channel_class channel_classes class_id span =
  match
    List.find_opt
      (fun (channel_class : channel_class_def) -> channel_class.name = class_id)
      channel_classes
  with
  | Some channel_class -> channel_class
  | None ->
      raise
        (TypeError
           [
             Text ("Undefined channel class " ^ class_id);
             codespan_local span;
           ])

let find_pool_channel pool_id member_id endpoint pool_channels span =
  match
    List.find_opt
      (fun (channel : channel_def ast_node) ->
        channel.d.endpoint_left = endpoint || channel.d.endpoint_right = endpoint)
      pool_channels
  with
  | Some channel -> channel
  | None ->
      raise
        (TypeError
           [
             Text
               (Printf.sprintf
                  "Endpoint %s used by interface member %s is not defined in pool %s"
                  endpoint member_id pool_id);
             codespan_local span;
           ])

let normalized_endpoint channel endpoint =
  if endpoint = channel.d.endpoint_right then channel.d.endpoint_left else endpoint

let channel_message_set channel_classes channel endpoint =
  let channel_class =
    lookup_channel_class channel_classes channel.d.channel_class channel.span
  in
  let normalized_ep = normalized_endpoint channel endpoint in
  List.fold_left
    (fun acc (message : message_def) ->
      MsgSet.add { endpoint = normalized_ep; msg = message.name } acc)
    MsgSet.empty channel_class.messages

let interface_argument_message_set channel_classes
    (pool_def : interface_pool_def ast_node) (member : interface_mem_def ast_node)
    (intf_inst : interface_instantiation) =
  List.fold_left
    (fun acc endpoint ->
      let channel =
        find_pool_channel pool_def.d.pool_id member.d.inf_mem_id endpoint
          pool_def.d.pool_channels member.span
      in
      MsgSet.union acc (channel_message_set channel_classes channel endpoint))
    MsgSet.empty intf_inst.params

let preprocessed_direct_type (member : interface_mem_def ast_node) session_ty =
  let endpoint_mapping =
    SessionHelper.build_endpoint_mapping member [] []
  in
  SessionHelper.preprocess_session_type endpoint_mapping session_ty

let preprocessed_interface_type (pool_def : interface_pool_def ast_node)
    session_defs (member : interface_mem_def ast_node)
    (interface_def : session_def ast_node) =
  let endpoint_mapping =
    SessionHelper.build_endpoint_mapping member pool_def.d.pool_channels
      session_defs
  in
  SessionHelper.preprocess_session_type endpoint_mapping interface_def.d.body.d

let add_member_progress_loop member_id auto =
  TypeAutomaton.accepting_states auto
  |> List.iter (fun final_state ->
         TypeAutomaton.add_transition auto final_state auto.start_state
           (Progress (StringSet.singleton member_id))
           { any_guard with forbid_clock = false } MsgSet.empty);
  recompute_state_summaries auto

let create_member_context channel_classes session_defs
    (pool_def : interface_pool_def ast_node)
    (member : interface_mem_def ast_node) =
  match member.d.interface_def, member.d.interface_class_id with
  | Some session_ty, _ ->
      let preprocessed_ty = preprocessed_direct_type member session_ty in
      let preprocessed_node = { d = preprocessed_ty; span = member.span } in
      let automaton =
        build_automaton (Some member.d.inf_mem_id) preprocessed_ty member.span
      in
      add_member_progress_loop member.d.inf_mem_id automaton;
      {
        member_id = member.d.inf_mem_id;
        preprocessed_type = preprocessed_node;
        automaton;
        message_set = messages_of_session_type preprocessed_ty;
        source_kind = Direct;
      }
  | None, Some intf_inst -> (
      match SessionHelper.lookup_interface session_defs intf_inst.id with
      | Some interface_def ->
          let preprocessed_ty =
            preprocessed_interface_type pool_def session_defs member interface_def
          in
          let preprocessed_node = { d = preprocessed_ty; span = member.span } in
          let automaton =
            build_automaton (Some member.d.inf_mem_id) preprocessed_ty member.span
          in
          add_member_progress_loop member.d.inf_mem_id automaton;
          {
            member_id = member.d.inf_mem_id;
            preprocessed_type = preprocessed_node;
            automaton;
            message_set =
              interface_argument_message_set channel_classes pool_def member
                intf_inst;
            source_kind = Interface intf_inst.id;
          }
      | None ->
          raise
            (TypeError
               [
                 Text
                   ("Undefined Session type " ^ intf_inst.id
                  ^ " in pool member " ^ member.d.inf_mem_id);
                 codespan_local member.span;
               ]))
  | None, None ->
      raise
        (TypeError
           [
             Text
               ("Neither interface definition nor instantiation found for pool member "
              ^ member.d.inf_mem_id);
             codespan_local member.span;
           ])

let pairwise_intersections members =
  let rec aux = function
    | [] -> []
    | member :: rest ->
        List.map
          (fun other ->
            {
              left_member_id = member.member_id;
              right_member_id = other.member_id;
              shared_messages = MsgSet.inter member.message_set other.message_set;
            })
          rest
        @ aux rest
  in
  aux members

let create_context channel_classes session_defs
    (pool_def : interface_pool_def ast_node) =
  let members =
    List.map
      (create_member_context channel_classes session_defs pool_def)
      pool_def.d.interface_members
  in
  {
    pool_id = pool_def.d.pool_id;
    members;
    pairwise_intersections = pairwise_intersections members;
    product_dot_paths = [];
    arena_dot_path = None;
    step_results = [];
  }

let msgset_union_list sets =
  List.fold_left MsgSet.union MsgSet.empty sets

let msgset_nonempty set = not (MsgSet.is_empty set)

let sanitize_filename_component name =
  let buffer = Buffer.create (String.length name) in
  String.iter
    (function
      | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-') as c ->
          Buffer.add_char buffer c
      | _ -> Buffer.add_char buffer '_')
    name;
  Buffer.contents buffer

let write_automaton_dot ?(verbose = false) path auto =
  let out = open_out path in
  try
    print_automaton_dot ~show_guards:verbose ~show_transition_debug:verbose
      ~show_empty_boundary:true auto out;
    close_out out
  with exn ->
    close_out_noerr out;
    raise exn

(* boundary_env and its helpers are provided by SessionOpenGame2. *)

type open_product_input = {
  op_member_id : identifier;
  op_automaton : typeAutomaton;
  op_messages : MsgSet.t;
}

let product_input_of_member member =
  {
    op_member_id = member.member_id;
    op_automaton = member.automaton;
    op_messages = member.message_set;
  }

(* Internal messages are those owned by at least two members: they must
   synchronize. Everything else is boundary (relies on the environment). *)
let internal_messages_of_inputs inputs =
  let all_messages =
    inputs |> Array.to_list |> List.map (fun input -> input.op_messages)
    |> msgset_union_list
  in
  MsgSet.filter
    (fun msg ->
      Array.fold_left
        (fun count input ->
          if MsgSet.mem msg input.op_messages then count + 1 else count)
        0 inputs
      >= 2)
    all_messages

let all_messages_of_inputs inputs =
  inputs |> Array.to_list |> List.map (fun input -> input.op_messages)
  |> msgset_union_list

(* Open product = the SAME unified synchronous product used by the closed/internal
   cases, driven with the open interface as its boundary. The internal messages
   (owned by ≥2 members) are synchronized; the rest are boundary, and
   unified_product records each transition's boundary projection E_B = (U, F) in
   boundary_now/boundary_future (plus the pending boundary guard) for the arena. *)
let build_open_product ?(verbose = false) name progress_ids inputs =
  let automata = Array.map (fun input -> input.op_automaton) inputs in
  let internal_messages = internal_messages_of_inputs inputs in
  let all_messages = all_messages_of_inputs inputs in
  let boundary_messages = MsgSet.diff all_messages internal_messages in
  let product =
    unified_product ~progress_ids ~verbose automata ~boundary_messages
      ~use_env:true
  in
  TypeAutomaton.change_name name product;
  recompute_state_summaries product;
  (product, internal_messages, boundary_messages)

(* arena_node_kind, arena_node, arena_edge, edge_label, and open_game_arena are
   provided by SessionOpenGame2. *)

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

let build_open_arena name product =
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
  (* A state is a player state when it has any real boundary move. The clock is
     folded into the boundary env (be_clock), so boundary_env_nonempty already
     covers the clock provide/withhold decision — no special clock casing here. *)
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

let print_open_arena_dot path arena =
  let out = open_out path in
  let dot_id id = "\"" ^ escape_dot id ^ "\"" in
  let html_label text = html_of_text_block text in
  let node_attrs kind =
    match kind with
    | ArenaPlayer -> "shape=diamond,color=darkgreen"
    | ArenaAdversary -> "shape=box,color=black"
    | ArenaFail -> "shape=doublecircle,color=red"
  in
  try
    Printf.fprintf out "digraph OpenCompatibilityArena {\n";
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
    Printf.fprintf out "}\n";
    close_out out
  with exn ->
    close_out_noerr out;
    raise exn

(* composite ids are joined with '-', and the
   newly added member is appended with '_': i1_i2, then i1-i2_i3, etc. *)
let compose_name left right = left ^ "_" ^ right

let residual_name left right = left ^ "-" ^ right

let product_dot_path composition_name =
  Printf.sprintf "open_product_%s.dot"
    (sanitize_filename_component composition_name)

let arena_dot_path composition_name =
  Printf.sprintf "open_arena_%s.dot"
    (sanitize_filename_component composition_name)

let residual_dot_path residual_name =
  Printf.sprintf "open_residual_%s.dot"
    (sanitize_filename_component residual_name)

(* hide_I : internal messages disappear from the boundary; a purely
   internal message step becomes ε; #, $id, and fair markers are preserved. *)
let hide_internal_action internal_messages = function
  | Messages msgs ->
      let visible = MsgSet.diff msgs internal_messages in
      if MsgSet.is_empty visible then Epsilon else Messages visible
  | (Epsilon | Clock | Progress _ | FairBranch _) as action -> action

(* Residual guards keep the boundary projection of the source guard so the next
   composition step still tests genuine boundary availability. *)
let residual_guard boundary_messages boundary source_guard =
  let project_groups groups =
    groups
    |> List.map (fun group -> MsgSet.inter boundary_messages group)
    |> List.filter (fun group -> not (MsgSet.is_empty group))
  in
  (* future_intersects/exists_now_groups are DISJUNCTIONS (∃G. G ∩ F/Imm ≠ ∅ =
     some message of G is present). Projecting per-message via project_groups
     would unsoundly drop a disjunct once its witnessing message is outside
     boundary_messages, even though a boundary message elsewhere in the same
     group could still satisfy it. So a group is kept WHOLE when it has any
     message in boundary_messages, and dropped entirely otherwise. *)
  let keep_disjunctive_groups groups =
    groups |> List.filter (fun group -> not (MsgSet.disjoint group boundary_messages))
  in
  {
    require_now = boundary.be_now;
    forbid_now = MsgSet.inter boundary_messages source_guard.forbid_now;
    missing_now_groups = project_groups source_guard.missing_now_groups;
    exists_now_groups = keep_disjunctive_groups source_guard.exists_now_groups;
    future_intersects = keep_disjunctive_groups source_guard.future_intersects;
    future_disjoint = MsgSet.inter boundary_messages source_guard.future_disjoint;
    subset_now = MsgSet.inter boundary_messages source_guard.subset_now;
    require_clock = source_guard.require_clock;
    forbid_clock = source_guard.forbid_clock;
  }

(* Map each product state to its arena entry node (player node if the state has
   boundary moves, else its single q_e0 adversary node). *)
let entry_nodes_by_product_state arena =
  let table = Hashtbl.create 32 in
  List.iter
    (fun node ->
      match (node.arena_node_kind, node.arena_product_state) with
      | ArenaPlayer, Some state_id -> Hashtbl.replace table state_id node.arena_node_id
      | ArenaAdversary, Some state_id ->
          if not (Hashtbl.mem table state_id) then
            Hashtbl.replace table state_id node.arena_node_id
      | _ -> ())
    arena.arena_nodes;
  table

(* Phase 5: the residual is the WHOLE composed product with the just-checked
   internal interface hidden. We do NOT prune to the game's winning region or to
   the player's selected boundary moves: the game verdict only decides
   compatibility (and stops the pool at the first failure), while the residual
   must expose the full open behaviour so the next composition step's game sees
   the true subsystem. Only hide_internal_action (internal Messages -> Epsilon)
   and the boundary guard projection are applied. *)
let build_residual_automaton residual_nm product internal_messages
    boundary_messages _arena _game_result =
  let residual = TypeAutomaton.create () in
  TypeAutomaton.change_name residual_nm residual;
  let state_map = Hashtbl.create 32 in
  let copy_state product_state =
    match Hashtbl.find_opt state_map product_state with
    | Some residual_state -> residual_state
    | None ->
        let src = Hashtbl.find product.states product_state in
        let residual_state =
          if product_state = product.start_state then residual.start_state
          else TypeAutomaton.new_state residual src.accepting
        in
        Hashtbl.add state_map product_state residual_state;
        let dst = Hashtbl.find residual.states residual_state in
        dst.accepting <- src.accepting;
        dst.is_fair <- src.is_fair;
        dst.adversary <- src.adversary;
        dst.residual_type <- src.residual_type;
        dst.product_components <- src.product_components;
        dst.debug_info <- src.debug_info;
        residual_state
  in
  (* Copy every product state so the residual keeps the full graph. *)
  Hashtbl.iter (fun product_state _ -> ignore (copy_state product_state))
    product.states;
  List.iter
    (fun (t : transition) ->
      let boundary = boundary_of_transition t in
      let from_state = copy_state t.from_state in
      let to_state = copy_state t.to_state in
      let action = hide_internal_action internal_messages t.action in
      (* Carry forward the PENDING (boundary) guard, not the already-discharged
         internal guard: it is the still-live boundary constraint the next
         composition step must test. *)
      let guard = residual_guard boundary_messages boundary t.boundary_guard in
      (* Keep the still-visible (boundary) offers so the next composition step's
         local environment can see what this subsystem presents. Internal offers
         were just hidden and must not leak into the next round. *)
      let offers = MsgSet.diff t.offers internal_messages in
      TypeAutomaton.add_transition_full ~boundary_now:boundary.be_now
        ~boundary_future:boundary.be_future ~offers
        ?transition_debug_info:t.transition_debug_info residual from_state
        to_state action guard)
    product.transitions;
  recompute_state_summaries residual;
  residual

(* One incremental composition step: compose, build the arena, solve the game,
   and on success hide the internal interface to form the residual input for the
   next step. *)
let build_composition_step ?(verbose = false) composition_name residual_nm
    progress_ids inputs =
  let product, internal_messages, boundary_messages =
    build_open_product ~verbose composition_name progress_ids inputs
  in
  let product_path = product_dot_path composition_name in
  write_automaton_dot ~verbose product_path product;
  let arena = build_open_arena composition_name product in
  let arena_path = arena_dot_path composition_name in
  print_open_arena_dot arena_path arena;
  let game_result = play_open_game arena ~progress_ids in
  Printf.printf "Open compatibility result for %s: %s\n" composition_name
    game_result.summary;
  let residual_dot, residual_input =
    if game_result.compatible then (
      let residual =
        build_residual_automaton residual_nm product internal_messages
          boundary_messages arena game_result
      in
      let path = residual_dot_path residual_nm in
      write_automaton_dot ~verbose path residual;
      ( Some path,
        Some
          {
            op_member_id = residual_nm;
            op_automaton = residual;
            op_messages = boundary_messages;
          } ))
    else (None, None)
  in
  ( {
      composition_name;
      residual_name = residual_nm;
      step_progress_ids = progress_ids;
      step_internal_messages = internal_messages;
      step_boundary_messages = boundary_messages;
      step_product_dot_path = product_path;
      step_arena_dot_path = arena_path;
      step_residual_dot_path = residual_dot;
      step_game_result = game_result;
    },
    residual_input )

(* Incremental composition: build i1_i2, solve, residual i1-i2, then compose
   that residual with i3, and so on. Stop at the first failed step. *)
let build_open_artifacts ?(verbose = false) context =
  match context.members with
  | [] ->
      raise
        (TypeError
           [ Text ("Pool " ^ context.pool_id ^ " has no interface members") ])
  | first :: rest ->
      let steps = ref [] in
      let composite_name = ref first.member_id in
      let composite_input = ref (product_input_of_member first) in
      let progress_ids = ref [ first.member_id ] in
      let failed = ref false in
      List.iter
        (fun member ->
          if not !failed then (
            let next_input = product_input_of_member member in
            let composition_name =
              compose_name !composite_name member.member_id
            in
            let res_name = residual_name !composite_name member.member_id in
            let new_progress = !progress_ids @ [ member.member_id ] in
            let step, residual_input =
              build_composition_step ~verbose composition_name res_name
                new_progress
                [| !composite_input; next_input |]
            in
            steps := !steps @ [ step ];
            match residual_input with
            | Some residual_input ->
                composite_name := res_name;
                composite_input := residual_input;
                progress_ids := new_progress
            | None -> failed := true))
        rest;
      (* A single-member pool has nothing to compose; still build its product. *)
      if rest = [] then (
        let product, internal_messages, boundary_messages =
          build_open_product ~verbose first.member_id !progress_ids
            [| !composite_input |]
        in
        let product_path = product_dot_path first.member_id in
        write_automaton_dot ~verbose product_path product;
        let arena = build_open_arena first.member_id product in
        let arena_path = arena_dot_path first.member_id in
        print_open_arena_dot arena_path arena;
        let game_result = play_open_game arena ~progress_ids:!progress_ids in
        Printf.printf "Open compatibility result for %s: %s\n" first.member_id
          game_result.summary;
        steps :=
          [
            {
              composition_name = first.member_id;
              residual_name = first.member_id;
              step_progress_ids = !progress_ids;
              step_internal_messages = internal_messages;
              step_boundary_messages = boundary_messages;
              step_product_dot_path = product_path;
              step_arena_dot_path = arena_path;
              step_residual_dot_path = None;
              step_game_result = game_result;
            };
          ]);
      context.step_results <- !steps;
      context.product_dot_paths <-
        List.map (fun step -> step.step_product_dot_path) !steps;
      context.arena_dot_path <-
        (match List.rev !steps with
        | step :: _ -> Some step.step_arena_dot_path
        | [] -> None)

let first_line text =
  match String.split_on_char '\n' text with line :: _ -> line | [] -> text

let print_context ?(verbose = false) out context =
  Printf.fprintf out "Open Compatibility v2 Context for pool %s\n"
    context.pool_id;
  if verbose then (
    List.iter
      (fun member ->
        Printf.fprintf out "[%s] %s msgs = %s\n"
          (source_kind_string member.source_kind) member.member_id
          (format_msgset member.message_set))
      context.members;
    List.iter
      (fun pair ->
        Printf.fprintf out "%s ∩ %s = %s\n" pair.left_member_id
          pair.right_member_id (format_msgset pair.shared_messages))
      context.pairwise_intersections);
  List.iter
    (fun step ->
      Printf.fprintf out "step %s: %s (I = %s; B = %s)\n" step.composition_name
        (if step.step_game_result.compatible then "compatible"
         else "incompatible")
        (format_msgset step.step_internal_messages)
        (format_msgset step.step_boundary_messages);
      Printf.fprintf out "  game = %s\n"
        (first_line step.step_game_result.summary);
      Printf.fprintf out "  product DOT = %s\n" step.step_product_dot_path;
      Printf.fprintf out "  arena DOT = %s\n" step.step_arena_dot_path;
      (match step.step_residual_dot_path with
      | Some path -> Printf.fprintf out "  residual DOT = %s\n" path
      | None -> ());
      match step.step_game_result.counterexample_trace with
      | Some trace -> Printf.fprintf out "  trace:%s\n" trace
      | None -> ())
    context.step_results;
  Printf.fprintf out "\n"

let check_open_compatibility_multiparty channel_classes session_defs pool_def
    verbose =
  let context = create_context channel_classes session_defs pool_def in
  build_open_artifacts ~verbose context;
  match
    List.find_opt
      (fun step -> not step.step_game_result.compatible)
      context.step_results
  with
  | Some step ->
      ( context,
        false,
        Printf.sprintf "Open compatibility failed at %s. %s" step.composition_name
          step.step_game_result.summary )
  | None ->
      let compatible = context.step_results <> [] in
      ( context,
        compatible,
        if compatible then
          "Compatible: open winning strategy found for all composition steps."
        else "Open compatibility built no composition steps." )
