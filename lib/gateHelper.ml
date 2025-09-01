
open Lang
open EventGraph
let gate_sanity_check g (reg_defs:reg_def ast_node list) (_channel_args: endpoint_def ast_node list) =
  let reg_membership id = List.exists (fun (r:reg_def ast_node) -> r.d.name = id) reg_defs in
  let ep_membership _id =
    (* List.exists (fun ep -> match_msg_spec ep id  )channel_args  in  To Do*) true in

  List.iter (fun gvar -> 
    match gvar with
    | Msg msg_spec ->
      if not (ep_membership msg_spec) then
        raise (Except.TypeError [Text ("Gate control endpoint/msg not found " ^ string_of_msg_spec msg_spec); Except.codespan_local g.gate_id.span])

    | Register (_, id) ->
      if not (reg_membership id) then
        raise (Except.TypeError [Text ("Gate control register not found " ^ id); Except.codespan_local g.gate_id.span])
  ) g.gate_elements



let add_reg_assignment_event gate_context (lval) (ev) span : gate_class list=

  let full_reg_add_event (gcl: EventGraph.gate_class) id =
    let gm = List.map (fun mem ->
      match mem.mid with
      | Register (op, id') when (op = GateWrite || op = GateReadWrite && id = id') -> 
        {mem with g_events = (ev,span):: mem.g_events}
      | _ ->  mem
    ) gcl.gmem in
    {gcl with gmem = gm} in

  match lval with 
    | Reg id -> 
      List.map (fun gcl ->
        full_reg_add_event gcl id
      ) gate_context
    | _ -> gate_context



let add_msg_event gate_context (msg_spec: Lang.message_specifier) (ev) span : gate_class list = 
  List.map (fun gcl -> 
    let gcm = List.map (fun mem -> 
      match mem.mid with
      | Msg ms when ms = msg_spec -> 
        {mem with g_events = (ev, span):: mem.g_events}
      | _ ->  mem
    ) gcl.gmem in 
    {gcl with gmem = gcm}
  ) gate_context

