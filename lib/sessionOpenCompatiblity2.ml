open Lang
open Except
open SessionAutomaton2
open SessionBuildAutomaton2

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

type open_pool_context = {
  pool_id : identifier;
  members : open_member_context list;
  pairwise_intersections : open_pair_intersection list;
  mutable product_dot_paths : string list;
  mutable arena_dot_path : string option;
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
           { any_guard with forbid_clock = true });
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

type boundary_env = {
  be_now : MsgSet.t;
  be_future : MsgSet.t;
}

let empty_boundary_env = { be_now = MsgSet.empty; be_future = MsgSet.empty }

let string_of_boundary_env env =
  Printf.sprintf "U=%s; F=%s" (format_msgset env.be_now)
    (format_msgset env.be_future)

let html_of_boundary_env env =
  "U = " ^ html_of_msgset env.be_now ^ "; F = " ^ html_of_msgset env.be_future

let boundary_env_equal lhs rhs =
  MsgSet.equal lhs.be_now rhs.be_now
  && MsgSet.equal lhs.be_future rhs.be_future

let boundary_env_nonempty env =
  msgset_nonempty env.be_now || msgset_nonempty env.be_future

type open_product_input = {
  op_member_id : identifier;
  op_automaton : typeAutomaton;
  op_messages : MsgSet.t;
}

type component_choice = {
  cc_to_state : int;
  cc_action : action;
  cc_messages : MsgSet.t;
  cc_guard : guard;
  cc_maybe_offers : MsgSet.t;
  cc_changed : bool;
  cc_debug : string;
  cc_transition : transition option;
}

let product_input_of_member member =
  {
    op_member_id = member.member_id;
    op_automaton = member.automaton;
    op_messages = member.message_set;
  }

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

let choice_of_transition component_name (t : transition) =
  {
    cc_to_state = t.to_state;
    cc_action = t.action;
    cc_messages = action_messages t.action;
    cc_guard = t.guard;
    cc_maybe_offers = t.maybe_offers;
    cc_changed = t.to_state <> t.from_state || t.action <> Epsilon;
    cc_debug =
      Printf.sprintf "%s:s%d --[%s]--> s%d" component_name t.from_state
        (html_of_action t.action) t.to_state;
    cc_transition = Some t;
  }

let passive_choice input state_id =
  let st = Hashtbl.find input.op_automaton.states state_id in
  {
    cc_to_state = state_id;
    cc_action = Epsilon;
    cc_messages = MsgSet.empty;
    cc_guard = any_guard;
    cc_maybe_offers = st.maybe_ready;
    cc_changed = false;
    cc_debug = Printf.sprintf "%s:s%d stays" input.op_member_id state_id;
    cc_transition = None;
  }

let reaction_transition (t : transition) =
  match t.action with
  | Messages _ -> true
  | Epsilon -> not (guard_is_any t.guard)
  | _ -> false

let reaction_choices outgoing input state_id =
  passive_choice input state_id
  :: (get_outgoing_from_index outgoing state_id
     |> List.filter reaction_transition
     |> List.map (choice_of_transition input.op_member_id))

let silent_transition (t : transition) =
  match t.action with
  | Epsilon | FairBranch _ -> guard_is_any t.guard
  | _ -> false

let env_debug env =
  Printf.sprintf "Imm=%s; F=%s; clock=%b" (format_msgset env.imm)
    (format_msgset env.future) env.clock

let local_env_for_reaction inputs internal_messages boundary current_arr choices i =
  let own_messages = inputs.(i).op_messages in
  let partner_now =
    Array.mapi
      (fun j state_id ->
        if i = j then MsgSet.empty
        else
          let st = Hashtbl.find inputs.(j).op_automaton.states state_id in
          MsgSet.inter internal_messages st.head)
      current_arr
    |> Array.to_list |> msgset_union_list
  in
  let partner_future =
    Array.mapi
      (fun j choice ->
        if i = j then MsgSet.empty
        else MsgSet.inter internal_messages choice.cc_maybe_offers)
      choices
    |> Array.to_list |> msgset_union_list
  in
  let imm =
    MsgSet.union (MsgSet.inter boundary.be_now own_messages) partner_now
    |> MsgSet.inter own_messages
  in
  let future =
    MsgSet.union (MsgSet.inter boundary.be_future own_messages) partner_future
    |> fun set -> MsgSet.diff set imm
    |> MsgSet.inter own_messages
  in
  { imm; future; clock = false }

let local_env_for_clock inputs internal_messages boundary current_arr i =
  let own_messages = inputs.(i).op_messages in
  let partner_now =
    Array.mapi
      (fun j state_id ->
        if i = j then MsgSet.empty
        else
          let st = Hashtbl.find inputs.(j).op_automaton.states state_id in
          MsgSet.inter internal_messages st.head)
      current_arr
    |> Array.to_list |> msgset_union_list
  in
  let partner_future =
    Array.mapi
      (fun j state_id ->
        if i = j then MsgSet.empty
        else
          let st = Hashtbl.find inputs.(j).op_automaton.states state_id in
          MsgSet.inter internal_messages st.maybe_ready)
      current_arr
    |> Array.to_list |> msgset_union_list
  in
  let imm =
    MsgSet.union (MsgSet.inter boundary.be_now own_messages) partner_now
    |> MsgSet.inter own_messages
  in
  let future =
    MsgSet.union (MsgSet.inter boundary.be_future own_messages) partner_future
    |> fun set -> MsgSet.diff set imm
    |> MsgSet.inter own_messages
  in
  { imm; future; clock = true }

let local_env_for_progress inputs internal_messages boundary current_arr i =
  let env =
    local_env_for_clock inputs internal_messages boundary current_arr i
  in
  { env with clock = false }

let choice_enabled inputs current_arr env i choice =
  match choice.cc_transition with
  | Some _ -> guard_satisfied env choice.cc_guard
  | None ->
      let st = Hashtbl.find inputs.(i).op_automaton.states current_arr.(i) in
      MsgSet.disjoint st.head env.imm

let sync_ok internal_messages choices =
  let internal_actions =
    choices |> Array.to_list |> List.map (fun choice -> choice.cc_messages)
    |> msgset_union_list |> MsgSet.inter internal_messages
  in
  MsgSet.for_all
    (fun msg ->
      Array.fold_left
        (fun count choice ->
          if MsgSet.mem msg choice.cc_messages then count + 1 else count)
        0 choices
      >= 2)
    internal_actions

let boundary_env_of_choices boundary_messages choices =
  (* SyncEdges uses the union of component transition environments. *)
  let required_now =
    choices |> Array.to_list
    |> List.filter_map (fun choice ->
           match choice.cc_transition with
           | Some _ -> Some choice.cc_guard.require_now
           | None -> None)
    |> msgset_union_list
    |> MsgSet.inter boundary_messages
  in
  { be_now = required_now; be_future = MsgSet.empty }

let product_transition_debug internal_messages boundary choices envs =
  let component_lines =
    Array.mapi
      (fun i choice ->
        Printf.sprintf "%s | %s" choice.cc_debug (env_debug envs.(i)))
      choices
    |> Array.to_list
  in
  String.concat "\n"
    ([
       "I = " ^ format_msgset internal_messages;
       "Boundary " ^ string_of_boundary_env boundary;
     ]
    @ component_lines)

let build_open_product name progress_ids inputs =
  Array.iter (fun input -> recompute_state_summaries input.op_automaton) inputs;
  let product = TypeAutomaton.create () in
  TypeAutomaton.change_name name product;
  let internal_messages = internal_messages_of_inputs inputs in
  let all_messages = all_messages_of_inputs inputs in
  let boundary_messages = MsgSet.diff all_messages internal_messages in
  let state_map = Hashtbl.create 32 in
  let start_vector =
    Array.to_list (Array.map (fun input -> input.op_automaton.start_state) inputs)
  in
  Hashtbl.add state_map start_vector product.start_state;
  let outgoing =
    Array.map
      (fun input -> build_outgoing_index input.op_automaton.transitions)
      inputs
  in
  let get_product_state states =
    match Hashtbl.find_opt state_map states with
    | Some id -> id
    | None ->
        let id = TypeAutomaton.new_state product false in
        Hashtbl.add state_map states id;
        id
  in
  let queue = Queue.create () in
  let visited = Hashtbl.create 32 in
  Queue.add start_vector queue;
  let enqueue states =
    if not (Hashtbl.mem visited states) then Queue.add states queue
  in
  let product_components current_arr =
    Array.mapi
      (fun i state_id ->
        let st = Hashtbl.find inputs.(i).op_automaton.states state_id in
        {
          pc_name = inputs.(i).op_member_id;
          pc_state = state_id;
          pc_residual = st.residual_type;
        })
      current_arr
    |> Array.to_list
  in
  let add_product_transition ?(guard = any_guard) ?(boundary = empty_boundary_env)
      ?transition_debug_info from_vec to_vec action =
    let from_id = get_product_state from_vec in
    let to_id = get_product_state to_vec in
    TypeAutomaton.add_transition_full ~boundary_now:boundary.be_now
      ~boundary_future:boundary.be_future ?transition_debug_info product from_id
      to_id action guard;
    if to_vec <> from_vec then enqueue to_vec
  in
  while not (Queue.is_empty queue) do
    let current = Queue.take queue in
    if not (Hashtbl.mem visited current) then (
      Hashtbl.add visited current ();
      let product_state = get_product_state current in
      let current_arr = Array.of_list current in
      let product_state_info = Hashtbl.find product.states product_state in
      set_product_state_debug product product_state
        (product_components current_arr);
      product_state_info.is_fair <-
        Array.mapi
          (fun i state_id ->
            (Hashtbl.find inputs.(i).op_automaton.states state_id).is_fair)
          current_arr
        |> Array.to_list |> List.exists (fun x -> x);
      product_state_info.adversary <-
        Array.mapi
          (fun i state_id ->
            (Hashtbl.find inputs.(i).op_automaton.states state_id).adversary)
          current_arr
        |> Array.to_list |> List.exists (fun x -> x);
      let all_accepting =
        Array.mapi
          (fun i state_id ->
            (Hashtbl.find inputs.(i).op_automaton.states state_id).accepting)
          current_arr
        |> Array.to_list |> List.for_all (fun x -> x)
      in
      if all_accepting then (
        product_state_info.accepting <- true;
        add_progress_transition product product_state product.start_state
          progress_ids)
      else (
        Array.iteri
          (fun i state_id ->
            get_outgoing_from_index outgoing.(i) state_id
            |> List.filter silent_transition
            |> List.iter (fun t ->
                   let next =
                     List.mapi
                       (fun j state -> if i = j then t.to_state else state)
                       current
                   in
                   add_product_transition current next t.action))
          current_arr;
        let choices_by_component =
          Array.mapi
            (fun i state_id -> reaction_choices outgoing.(i) inputs.(i) state_id)
          current_arr
          |> Array.to_list
        in
        choices_by_component |> cartesian_product
        |> List.iter (fun combo ->
               let choices = Array.of_list combo in
               let changed =
                 Array.exists (fun choice -> choice.cc_changed) choices
               in
               let combined_messages =
                 choices |> Array.to_list
                 |> List.map (fun choice -> choice.cc_messages)
                 |> msgset_union_list
               in
               if changed || msgset_nonempty combined_messages then
                 let boundary =
                   boundary_env_of_choices boundary_messages choices
                 in
                 let envs =
                   Array.mapi
                     (fun i _ ->
                       local_env_for_reaction inputs internal_messages boundary
                         current_arr choices i)
                     choices
                 in
                 if
                   Array.mapi
                     (fun i choice ->
                       choice_enabled inputs current_arr envs.(i) i choice)
                     choices
                   |> Array.to_list |> List.for_all (fun x -> x)
                   && sync_ok internal_messages choices
                 then
                   let next =
                     choices |> Array.to_list
                     |> List.map (fun choice -> choice.cc_to_state)
                   in
                   let action =
                     if MsgSet.is_empty combined_messages then Epsilon
                     else Messages combined_messages
                   in
                   let guard =
                     choices |> Array.to_list
                     |> List.filter_map (fun choice ->
                            match choice.cc_transition with
                            | Some _ -> Some choice.cc_guard
                            | None -> None)
                     |> merge_guards
                   in
                   let debug =
                     product_transition_debug internal_messages boundary choices
                       envs
                   in
                   add_product_transition ~guard ~boundary
                     ~transition_debug_info:debug current next action);
        let has_ordinary_non_clock_move =
          List.exists
            (fun t -> t.from_state = product_state && not (transition_is_clock t))
            product.transitions
        in
        if not has_ordinary_non_clock_move then
          let boundary = empty_boundary_env in
          let local_envs =
            Array.mapi
              (fun i _ ->
                local_env_for_progress inputs internal_messages boundary
                  current_arr i)
              current_arr
          in
          Array.iteri
            (fun i state_id ->
              get_outgoing_from_index outgoing.(i) state_id
              |> List.iter (fun t ->
                     match t.action with
                     | Progress _ when guard_satisfied local_envs.(i) t.guard ->
                         let next =
                           List.mapi
                             (fun j state -> if i = j then t.to_state else state)
                             current
                         in
                         let debug =
                           product_transition_debug internal_messages boundary
                             [| choice_of_transition inputs.(i).op_member_id t |]
                             [| local_envs.(i) |]
                         in
                         add_product_transition ~guard:t.guard ~boundary
                           ~transition_debug_info:debug current next t.action
                     | _ -> ()))
            current_arr;
        let clock_choices =
          Array.mapi
            (fun i state_id ->
              get_outgoing_from_index outgoing.(i) state_id
              |> List.filter_map (fun t ->
                     match t.action with
                     | Clock -> Some t
                     | _ -> None))
            current_arr
          |> Array.to_list
        in
        if List.for_all (fun choices -> choices <> []) clock_choices then
          clock_choices |> cartesian_product
          |> List.iter (fun combo ->
                 let transitions = Array.of_list combo in
                 let boundary = empty_boundary_env in
                 let envs =
                   Array.mapi
                     (fun i _ ->
                       local_env_for_clock inputs internal_messages boundary
                         current_arr i)
                     transitions
                 in
                 if
                   Array.mapi
                     (fun i transition ->
                       guard_satisfied envs.(i) transition.guard)
                     transitions
                   |> Array.to_list |> List.for_all (fun x -> x)
                 then
                   let next =
                     transitions |> Array.to_list
                     |> List.map (fun t -> t.to_state)
                   in
                   let guard =
                     transitions |> Array.to_list
                     |> List.map (fun t -> t.guard)
                     |> merge_guards
                   in
                   let debug =
                     let choices =
                       Array.mapi
                         (fun i transition ->
                           choice_of_transition inputs.(i).op_member_id
                             transition)
                         transitions
                     in
                     product_transition_debug internal_messages boundary choices
                       envs
                   in
                   add_product_transition ~guard ~boundary
                     ~transition_debug_info:debug current next Clock)))
  done;
  recompute_state_summaries product;
  (product, internal_messages, boundary_messages)

type arena_node_kind =
  | ArenaPlayer
  | ArenaAdversary
  | ArenaFail

type arena_node = {
  arena_node_id : string;
  arena_node_label : string;
  arena_node_kind : arena_node_kind;
}

type arena_edge = {
  arena_edge_from : string;
  arena_edge_to : string;
  arena_edge_label : string;
}

type open_game_arena = {
  arena_name : string;
  arena_start : string;
  arena_nodes : arena_node list;
  arena_edges : arena_edge list;
}

let boundary_of_transition t =
  { be_now = t.boundary_now; be_future = t.boundary_future }

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
  let add_edge from_node to_node label =
    edges :=
      {
        arena_edge_from = from_node;
        arena_edge_to = to_node;
        arena_edge_label = label;
      }
      :: !edges
  in
  let has_player_state state_id =
    Hashtbl.find moves_by_state state_id
    |> List.exists boundary_env_nonempty
  in
  let entry state_id =
    if has_player_state state_id then arena_player_id state_id
    else arena_adversary_id state_id 0
  in
  List.iter
    (fun state_id ->
      let moves = Hashtbl.find moves_by_state state_id in
      if has_player_state state_id then
        add_node
          {
            arena_node_id = arena_player_id state_id;
            arena_node_label = Printf.sprintf "q%dP" state_id;
            arena_node_kind = ArenaPlayer;
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
            };
          if has_player_state state_id then
            add_edge (arena_player_id state_id) adv_id
              ("θ: " ^ html_of_boundary_env move))
        moves)
    state_ids;
  add_node
    {
      arena_node_id = arena_fail_id;
      arena_node_label = "bottom";
      arena_node_kind = ArenaFail;
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
          | [] -> add_edge adv_id arena_fail_id "ε"
          | _ ->
              List.iter
                (fun t ->
                  add_edge adv_id (entry t.to_state) (html_of_action t.action))
                matching)
        moves)
    state_ids;
  add_edge arena_fail_id arena_fail_id "ε";
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
          edge.arena_edge_label)
      arena.arena_edges;
    Printf.fprintf out "}\n";
    close_out out
  with exn ->
    close_out_noerr out;
    raise exn

let product_dot_path pool_id step =
  Printf.sprintf "open_product_%s_step%d.dot"
    (sanitize_filename_component pool_id) step

let arena_dot_path pool_id =
  Printf.sprintf "open_arena_%s.dot" (sanitize_filename_component pool_id)

let build_open_artifacts ?(verbose = false) context =
  match context.members with
  | [] ->
      raise
        (TypeError
           [ Text ("Pool " ^ context.pool_id ^ " has no interface members") ])
  | members ->
      let inputs =
        members |> List.map product_input_of_member |> Array.of_list
      in
      let final_product = ref None in
      let product_paths = ref [] in
      for prefix_len = 1 to Array.length inputs do
        let prefix_inputs = Array.sub inputs 0 prefix_len in
        let progress_ids =
          prefix_inputs |> Array.to_list
          |> List.map (fun input -> input.op_member_id)
        in
        let product, _internal_messages, _boundary_messages =
          build_open_product
            (Printf.sprintf "%s_prefix%d" context.pool_id prefix_len)
            progress_ids prefix_inputs
        in
        if prefix_len >= 2 || Array.length inputs = 1 then (
          let path = product_dot_path context.pool_id prefix_len in
          write_automaton_dot ~verbose path product;
          product_paths := !product_paths @ [ path ]);
        if prefix_len = Array.length inputs then final_product := Some product
      done;
      let product =
        match !final_product with
        | Some product -> product
        | None -> raise (Failure "Open product construction produced no product")
      in
      let arena = build_open_arena context.pool_id product in
      let arena_path = arena_dot_path context.pool_id in
      print_open_arena_dot arena_path arena;
      context.product_dot_paths <- !product_paths;
      context.arena_dot_path <- Some arena_path;
      (product, arena)

let print_context out context =
  Printf.fprintf out "Open Compatibility v2 Context for pool %s\n"
    context.pool_id;
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
    context.pairwise_intersections;
  List.iter
    (fun path -> Printf.fprintf out "product DOT = %s\n" path)
    context.product_dot_paths;
  (match context.arena_dot_path with
  | Some path -> Printf.fprintf out "arena DOT = %s\n" path
  | None -> ());
  Printf.fprintf out "\n"

let check_open_compatibility_multiparty channel_classes session_defs pool_def
    verbose =
  let context = create_context channel_classes session_defs pool_def in
  ignore (build_open_artifacts ~verbose context);
  ( context,
    false,
    "Open compatibility arena built; open game not implemented." )
