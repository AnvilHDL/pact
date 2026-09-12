(** Picks each message's single reverse handshake port ([ack] or [ready]) from
    its use sites, per process. An [irecv] gives valid/ready, an [isend] gives
    valid/ack, and a [>>]/[<<] annotation overrides both. *)

open Lang

(* Use sites whose protocol demand is waived: a single-branch xoffer (and the
   try constructs) asserts its own signal unconditionally, so it works under
   either protocol. Registered by the graph builder as it lowers them. *)
let protocol_agnostic_spans : (Lang.code_span, unit) Hashtbl.t = Hashtbl.create 16

let mark_protocol_agnostic (span : Lang.code_span) =
  Hashtbl.replace protocol_agnostic_spans span ()

(* (canonical endpoint name, message name) within one process. *)
module Key = struct
  type t = identifier * identifier
  let compare = compare
end

module KeyMap = Map.Make (Key)

type use = {
  use_kind : handshake_kind;
  use_is_recv : bool; (** whether the use site receives (vs sends) *)
  use_span : code_span;
  use_endpoint : identifier;
    (** endpoint as written; message lookup needs this, not the canonical name *)
}

(** The mode a use site requires. [irecv] asserts [ready] and [isend] asserts
    [valid] unconditionally, which each fit only one protocol. Blocking ops fit
    either, so they require nothing. *)
let demanded_mode (u : use) : handshake_modes option =
  if Hashtbl.mem protocol_agnostic_spans u.use_span then None
  else
  match u.use_kind, u.use_is_recv with
  | Instant, true -> Some ValidReady
  | Instant, false -> Some ValidAck
  | Blocking, _ -> None

let string_of_use (u : use) =
  match u.use_kind, u.use_is_recv with
  | Instant, true -> "irecv"
  | Instant, false -> "isend"
  | Blocking, true -> "recv"
  | Blocking, false -> "send"

(* Every message use in a process, keyed by canonicalised endpoint and message. *)
let collect_uses (pg : EventGraph.proc_graph) : use list KeyMap.t =
  let tbl = ref KeyMap.empty in
  let add (g : EventGraph.event_graph) (msg : message_specifier) kind is_recv span =
    let ep = CodegenFormat.canonicalize_endpoint_name msg.endpoint g in
    let key = (ep, msg.msg) in
    let u = {use_kind = kind; use_is_recv = is_recv; use_span = span;
             use_endpoint = msg.endpoint} in
    tbl := KeyMap.update key (function None -> Some [u] | Some l -> Some (u :: l)) !tbl
  in
  List.iter (fun ((g : EventGraph.event_graph), _) ->
    List.iter (fun (e : EventGraph.event) ->
      List.iter (fun (sa : EventGraph.sustained_action ast_node) ->
        match sa.d.ty with
        | EventGraph.Send (msg, _, k) -> add g msg k false sa.span
        | EventGraph.Recv (msg, k) -> add g msg k true sa.span
      ) e.sustained_actions;
      List.iter (fun (ac : EventGraph.action ast_node) ->
        match ac.d with
        | EventGraph.ImmediateSend (msg, _, k) -> add g msg k false ac.span
        | EventGraph.ImmediateRecv (msg, k) -> add g msg k true ac.span
        | _ -> ()
      ) e.actions
    ) g.events
  ) pg.threads;
  !tbl

let string_of_mode = function
  | ValidAck -> "valid/ack"
  | ValidReady -> "valid/ready"

let annotation_of_mode = function
  | ValidAck -> ">>"
  | ValidReady -> "<<"

(* Resolve one (endpoint, message) from its use sites. *)
let resolve_key msg_name (uses : use list) (declared : handshake_modes option) =
  match declared with
  | Some mode ->
    (* The annotation decides; a use site needing the other port is an error. *)
    List.iter (fun u ->
      match demanded_mode u with
      | Some needed when needed <> mode ->
        raise (Except.TypeError [
          Except.Text (Printf.sprintf
            "'%s' on %s.%s needs a %s message, but %s is declared %s (%s)"
            (string_of_use u) u.use_endpoint msg_name (string_of_mode needed)
            msg_name (string_of_mode mode) (annotation_of_mode mode));
          Except.codespan_local u.use_span])
      | _ -> ()
    ) uses;
    mode
  | None ->
    (* Messages have a fixed direction, so the two demands should not collide;
       the check guards against that changing. *)
    let wants_ready = List.find_opt (fun u -> demanded_mode u = Some ValidReady) uses
    and wants_ack = List.find_opt (fun u -> demanded_mode u = Some ValidAck) uses in
    (match wants_ready, wants_ack with
     | Some r, Some a ->
       raise (Except.TypeError [
         Except.Text (Printf.sprintf
           "conflicting handshakes for %s.%s: '%s' needs %s but '%s' needs %s, \
            and a message has only one reverse handshake port"
           r.use_endpoint msg_name
           (string_of_use r) (string_of_mode ValidReady)
           (string_of_use a) (string_of_mode ValidAck));
         Except.codespan_local r.use_span])
     | Some _, None -> ValidReady
     | None, Some _ -> ValidAck
     | None, None -> ValidAck)

(** Resolve every message used by [pg], keyed by (endpoint, message). *)
let resolve_proc (channel_classes : channel_class_def list) (pg : EventGraph.proc_graph)
  : handshake_modes KeyMap.t =
  let uses = collect_uses pg in
  KeyMap.mapi (fun (_ep, msg_name) us ->
    (* Look up the message to find any explicit annotation. *)
    let declared =
      List.find_map (fun u ->
        match MessageCollection.lookup_message pg.messages
                {endpoint = u.use_endpoint; msg = msg_name} channel_classes with
        | Some m -> Some m.handshake_mode
        | None -> None
      ) us |> Option.join
    in
    resolve_key msg_name us declared
  ) uses

(* Pair each spawned child with the parent-side endpoints handed to it. *)
let spawn_children (graphs : EventGraph.event_graph_collection) (pg : EventGraph.proc_graph) =
  List.filter_map (fun ((module_name, spawn) : identifier * (spawn_def ast_node)) ->
    match List.find_opt (fun (p : EventGraph.proc_graph) -> p.name = module_name)
            graphs.external_event_graphs with
    | None -> None
    | Some child ->
      let parent_eps = preprocess_ep_spawn_args spawn.d.params in
      let child_eps = List.map (fun (ep : endpoint_def) -> ep.name) child.messages.args in
      if List.length child_eps <> List.length parent_eps then None
      else Some (child, List.combine child_eps parent_eps)
  ) pg.spawns

(** The resolver {!CodegenPort.gather_ports} consults. Unused messages fall
    back to their annotation, then to valid/ack. *)
let resolver_of_proc ?(children = []) (channel_classes : channel_class_def list)
  (pg : EventGraph.proc_graph) : CodegenPort.resolver =
  let resolved = resolve_proc channel_classes pg in
  (* Endpoints handed to a spawned child take that child's resolution, since
     both sides share one wire. *)
  let resolved =
    List.fold_left (fun acc ((child : EventGraph.proc_graph), (arg_map : (identifier * identifier) list)) ->
      let child_resolved = resolve_proc channel_classes child in
      List.fold_left (fun acc (child_ep, parent_ep) ->
        KeyMap.fold (fun (ep, msg_name) mode acc ->
          if ep = child_ep then KeyMap.add (parent_ep, msg_name) mode acc else acc
        ) child_resolved acc
      ) acc arg_map
    ) resolved children
  in
  (* Both ends of a local channel share one wire, so reconcile them. *)
  let resolved =
    List.fold_left (fun acc (ep : endpoint_def) ->
      match ep.opp with
      | None -> acc
      | Some opp_name ->
        let cc = MessageCollection.lookup_channel_class channel_classes ep.channel_class in
        (match cc with
         | None -> acc
         | Some cc ->
           List.fold_left (fun acc (m : message_def) ->
             let here = KeyMap.find_opt (ep.name, m.name) acc
             and there = KeyMap.find_opt (opp_name, m.name) acc in
             (* If either end needs valid/ready, both use it. *)
             let agreed = match here, there with
               | Some ValidReady, _ | _, Some ValidReady -> Some ValidReady
               | Some mode, _ | _, Some mode -> Some mode
               | None, None -> None
             in
             match agreed with
             | None -> acc
             | Some mode ->
               acc
               |> KeyMap.add (ep.name, m.name) mode
               |> KeyMap.add (opp_name, m.name) mode
           ) acc cc.messages)
    ) resolved pg.messages.endpoints
  in
  fun ep msg_name ->
    match KeyMap.find_opt (ep, msg_name) resolved with
    | Some mode -> mode
    | None ->
      (* Unused here: fall back to the declaration, else the default. *)
      (match MessageCollection.lookup_message pg.messages
               {endpoint = ep; msg = msg_name} channel_classes with
       | Some {handshake_mode = Some mode; _} -> mode
       | _ -> ValidAck)


(** The resolver for a process, accounting for spawned children. Codegen must
    use this everywhere, so that all sites naming a signal agree. *)
let resolver_for (graphs : EventGraph.event_graph_collection) (pg : EventGraph.proc_graph)
  : CodegenPort.resolver =
  resolver_of_proc ~children:(spawn_children graphs pg) graphs.channel_classes pg
