open Lang
open Except
open SessionAutomaton2
open SessionBuildAutomaton2

(* A composed subsystem exposes only its remaining boundary to the next member. *)
type product_input = {
  member_id : identifier;
  automaton : typeAutomaton;
  messages : MsgSet.t;
}

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


let prepare_pool channel_classes session_defs pool =
  let session_ids = SessionHelper.preprocess_pool_for_compatibility pool session_defs in
  let message_sets = List.map (fun (member : interface_mem_def ast_node) ->
    let messages = match member.d.interface_def, member.d.interface_class_id with
      | None, Some instance ->
          interface_argument_message_set channel_classes pool member instance
      | _ ->
          let session_node, _ = List.find
            (fun (_, id) -> id = member.d.inf_mem_id) session_ids in
          messages_of_session_type session_node.d
    in
    (member.d.inf_mem_id, messages)) pool.d.interface_members
  in
  (session_ids, message_sets)

let sanitize_filename name =
  String.map (function
    | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-') as c -> c
    | _ -> '_') name

let write_automaton_dot verbose path automaton =
  let out = open_out path in
  Fun.protect ~finally:(fun () -> close_out_noerr out) (fun () ->
    print_automaton_dot ~show_guards:verbose ~show_transition_debug:verbose
      ~show_empty_boundary:true automaton out)

let build_members message_sets session_ids verbose =
  List.map (fun (session_node, member_id) ->
    let repeated_type = repeat_with_progress member_id session_node.d in
    let automaton = build_automaton (Some member_id) repeated_type session_node.span in
    let messages = match List.assoc_opt member_id message_sets with
      | Some messages -> messages
      | None -> messages_of_session_type session_node.d
    in
    if verbose then
      write_automaton_dot verbose
        (sanitize_filename member_id ^ "_generalized_v2_automaton.dot") automaton;
    { member_id; automaton; messages }) session_ids

let compose verbose name inputs =
  let all_messages, internal_messages = List.fold_left
    (fun (seen, shared) input ->
      (MsgSet.union seen input.messages,
       MsgSet.union shared (MsgSet.inter seen input.messages)))
    (MsgSet.empty, MsgSet.empty) inputs in
  let boundary_messages = MsgSet.diff all_messages internal_messages in
  let automata = List.map (fun input -> input.member_id, input.automaton) inputs in
  let product = unified_product verbose automata boundary_messages internal_messages in
  TypeAutomaton.change_name name product;
  (product, internal_messages, boundary_messages)

let create_product ?(message_sets = []) session_ids verbose pool_id =
  let members = build_members message_sets session_ids verbose in
  if members = [] then raise (TypeError [Text ("Pool " ^ pool_id ^ " has no interface members")]);
  let product, _, _ = compose verbose pool_id members in
  product

(* Stage the full product with internal messages hidden; retain progress and fair markers. *)
let residual_input name product boundary_messages =
  let visible_action = function
    | Clock -> Clock
    | Observations observations ->
        Observations (ObservationSet.filter (function
          | Message msg -> MsgSet.mem msg boundary_messages
          | Progress _ | FairBranch _ -> true) observations)
  in
  let automaton = {
    product with
    name;
    total_message_set = boundary_messages;
    transitions = List.map (fun t ->
      { t with action = visible_action t.action }) product.transitions;
  } in
  { member_id = name; automaton; messages = boundary_messages }

let check_stage verbose artifact_name progress_ids inputs =
  let product, internal_messages, boundary_messages = compose verbose artifact_name inputs in
  let arena = SessionGame2.build_arena artifact_name product in
  let game = SessionGame2.play_arena arena ~progress_ids in
  let path = sanitize_filename artifact_name in
  write_automaton_dot verbose ("product_" ^ path ^ ".dot") product;
  SessionGame2.print_arena_dot ("arena_" ^ path ^ ".dot") arena;
  if verbose then (
    Printf.eprintf "Compatibility stage %s (I={%s}; B={%s}): %s\n"
      artifact_name (string_of_msgset internal_messages)
      (string_of_msgset boundary_messages) game.summary;
    Option.iter (fun trace -> Printf.eprintf "%s\n" trace) game.counterexample_trace);
  let residual = residual_input artifact_name product boundary_messages in
  if game.compatible then
    write_automaton_dot verbose ("residual_" ^ path ^ ".dot") residual.automaton;
  (residual, game)

let check_compatibility_multiparty ?(sequential = false) ?(message_sets = [])
    session_ids pool_id verbose =
  let members = build_members message_sets session_ids verbose in
  let explain name (game : SessionGame2.game_result) =
    let message = if game.compatible then game.summary
      else "Compatibility failed at " ^ name ^ ". " ^ game.summary in
    let message = match game.counterexample_trace with
      | None -> message
      | Some trace -> message ^ "\n" ^ trace
    in
    (game.compatible, message)
  in
  match members with
  | [] -> raise (TypeError [Text ("Pool " ^ pool_id ^ " has no interface members")])
  | first :: rest when sequential && rest <> [] ->
      let rec next_stage stage accumulated progress_ids consumed = function
        | [] -> assert false
        | next :: rest ->
            let hidden = MsgSet.diff consumed accumulated.messages in
            let reused = MsgSet.inter hidden next.messages in
            if not (MsgSet.is_empty reused) then
              raise (TypeError [Text (Printf.sprintf
                "Sequential composition cannot add %s: {%s} are already internal to the accumulated product. Use mode 3 to compose these members together."
                next.member_id (string_of_msgset reused))]);
            let name = Printf.sprintf "%s_sequential_%d" pool_id stage in
            let progress_ids = progress_ids @ [next.member_id] in
            let residual, game = check_stage verbose name progress_ids [accumulated; next] in
            if not game.compatible || rest = [] then explain name game
            else next_stage (stage + 1) residual progress_ids
              (MsgSet.union consumed next.messages) rest
      in
      next_stage 1 first [first.member_id] first.messages rest
  | _ ->
      let name = pool_id ^ (if sequential then "_sequential_1" else "_simultaneous") in
      let progress_ids = List.map (fun input -> input.member_id) members in
      let _, game = check_stage verbose name progress_ids members in
      explain name game
