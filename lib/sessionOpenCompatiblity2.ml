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

let create_member_context channel_classes session_defs
    (pool_def : interface_pool_def ast_node)
    (member : interface_mem_def ast_node) =
  match member.d.interface_def, member.d.interface_class_id with
  | Some session_ty, _ ->
      let preprocessed_ty = preprocessed_direct_type member session_ty in
      let preprocessed_node = { d = preprocessed_ty; span = member.span } in
      {
        member_id = member.d.inf_mem_id;
        preprocessed_type = preprocessed_node;
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
          {
            member_id = member.d.inf_mem_id;
            preprocessed_type = preprocessed_node;
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
  }

let print_context out context =
  Printf.fprintf out "Interface Context for pool %s\n"
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
  Printf.fprintf out "\n"

let check_open_compatibility_multiparty channel_classes session_defs pool_def
    _verbose =
  let context = create_context channel_classes session_defs pool_def in
  ( context,
    false,
    "Open compatibility not implemented." )
