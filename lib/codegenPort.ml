open Lang

type t = {
  dir: message_direction;
  dtype: data_type;
  name: identifier;
}

(* A message has [valid] plus exactly one reverse port, [ack] or [ready].
   Which one is decided per process by {!HandshakeResolve}. *)

let message_has_valid_port (msg : message_def) : bool = msg.send_sync = Dynamic

let message_has_ack_port ?(mode = ValidAck) (msg : message_def) : bool =
  (msg.recv_sync = Dynamic) && (mode = ValidAck)

let message_has_ready_port ?(mode = ValidAck) (msg : message_def) : bool =
  (msg.recv_sync = Dynamic) && (mode = ValidReady)

(* The reverse signal under the resolved mode, or [None] when the message has
   no dynamic reverse port. *)
type reverse_signal = UsesAck | UsesReady

let site_reverse_signal ?(mode = ValidAck) (msg : message_def) : reverse_signal option =
  if msg.recv_sync <> Dynamic then None
  else match mode with
    | ValidAck -> Some UsesAck
    | ValidReady -> Some UsesReady

(* Whether a use site waits for its peer. *)
let site_blocks ?(mode = ValidAck) (msg : message_def) (kind : handshake_kind) : bool =
  kind = Blocking && site_reverse_signal ~mode msg <> None

let message_has_data_port (msg : message_def) (idx : int) : bool = (List.nth msg.sig_types idx).dtype <> unit_dtype

(* Resolved handshake mode per (endpoint, message) for one process. *)
type resolver = identifier -> identifier -> handshake_modes

let default_resolver : resolver = fun _ _ -> ValidAck

let gather_ports_from_endpoint ?(resolve = default_resolver) (channel_classes : channel_class_def list) (endpoint : endpoint_def) : t list =
  let cc = (MessageCollection.lookup_channel_class channel_classes endpoint.channel_class) in
  let cc = match cc with
    | Some cc -> cc
    | None -> raise (Except.CodegenError [Text ("Channel class " ^ endpoint.channel_class ^ " not found for endpoint " ^ endpoint.name)])
   in
  let gen_endpoint_ports = fun (msg : message_def) ->
    let msg = ParamConcretise.concretise_message cc.params endpoint.channel_params msg in
    let folder_inner = fun fmt msg_dir (n, port_list) (stype : sig_type_chan_local) ->
      if stype.dtype = Lang.unit_dtype then (n, port_list)
      else
        (
        let new_port : t = {
          name = fmt endpoint.name msg.name n;
          dir = msg_dir;
          dtype = stype.dtype;
        } in (n + 1, new_port::port_list)
      )
    in
    let msg_data_dir = get_message_direction msg.dir endpoint.dir in
    let (_, res) = List.fold_left (folder_inner CodegenFormat.format_msg_data_signal_name msg_data_dir) (0, []) msg.sig_types in
    let res =
      if message_has_valid_port msg then
        let valid_port = { name = CodegenFormat.format_msg_valid_signal_name endpoint.name msg.name; dir = msg_data_dir; dtype = `Logic} in
        valid_port::res
      else res
    in
      let mode = resolve endpoint.name msg.name in
      if message_has_ack_port ~mode msg then
        let ack_port = {name = CodegenFormat.format_msg_ack_signal_name endpoint.name msg.name; dir = reverse msg_data_dir; dtype = `Logic} in
        ack_port::res
      else if message_has_ready_port ~mode msg then
        let ready_port = {name = CodegenFormat.format_msg_ready_signal_name endpoint.name msg.name; dir = reverse msg_data_dir; dtype = `Logic} in
        ready_port::res
      else res 
  in List.concat_map gen_endpoint_ports cc.messages

let gather_ports ?(resolve = default_resolver) (channel_classes : channel_class_def list) (endpoints : endpoint_def list) : t list =
  List.concat_map (gather_ports_from_endpoint ~resolve channel_classes) endpoints

let clk = {dir = Inp; dtype = `Logic; name = "clk_i"}
let rst = {dir = Inp; dtype = `Logic; name = "rst_ni"}

let format (typedefs : TypedefMap.t) (macro_defs: macro_def list) port =
  let ep_name_formatted = CodegenFormat.sanitize_identifier port.name in
  let inout = match port.dir with
    | Inp -> "input"
    | Out -> "output"
  in if port.dtype <> Lang.unit_dtype then Printf.sprintf "%s %s %s" inout (CodegenFormat.format_dtype typedefs macro_defs port.dtype) ep_name_formatted else ""