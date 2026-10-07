open Lang

(* A blocking arm waits across cycles, so an offer with an else arm takes only instant arms. *)
let check_blocking_else span (sty : session_type) =
  let is_else (o : offering_session_type) = match o.trigger with AtomDelay _ -> true | _ -> false in
  let is_blocking (o : offering_session_type) = match o.trigger with
    | AtomicAct (AtomBMsg _) -> true
    | AtomConjunction acts -> List.exists (function AtomBMsg _ -> true | AtomNBMsg _ -> false) acts
    | _ -> false
  in
  let rec go sty = match sty with
    | StyOffer offs | StyXOffer offs | StyFairXOffer offs | StyOfferMatch (offs, _) ->
        if List.exists is_else offs && List.exists is_blocking offs then
          raise (Except.TypeError [
            Text ("A blocking arm cannot sit beside an else arm; use #m for an arm decided this cycle: "
                  ^ string_of_protocol sty);
            Except.codespan_local span]);
        List.iter (fun (o : offering_session_type) ->
          (match o.trigger with AtomTerminal t -> go t | _ -> ());
          Option.iter go o.continuation) offs;
        (match sty with StyOfferMatch (_, cases) -> List.iter (fun c -> go c.match_body) cases | _ -> ())
    | StySeq (a, b) | StyChoice (a, b) | StyFairChoice (a, b) | StyParallel (a, b) | StyLet (_, a, b) -> go a; go b
    | StyFuture a | StyRec (_, a) | StyForall (_, _, _, a, _) | StyAtom (AtomTerminal a) -> go a
    | StyAtom _ | StySkip | StyEnd _ | StyVar _ -> ()
  in
  go sty

(** Check AST for well-formedness *)
let syntax_tree_precheck (_config : Config.compile_config) cunit =
  (* just check if the channel definitions have well-formed sync modes *)
  List.iter (fun cc ->
    let msg_set = ref Utils.StringSet.empty in
    List.iter (fun (msg : message_def) ->
      if Utils.StringSet.mem msg.name !msg_set then
        raise (Except.TypeError [Text "Duplicate message!"; Except.codespan_local msg.span])
      else (
        msg_set := Utils.StringSet.add msg.name !msg_set
      )
    ) cc.messages;
    List.iter (fun (msg : message_def) ->
      List.iter (fun {lifetime = lt_d; _} ->
        match lt_d.e with
        | `Cycles _ | `Eternal -> ()
        | `Message_with_offset (msg_name, _, _) ->
          if not @@ Utils.StringSet.mem msg_name !msg_set then
            raise (Except.TypeError [Text "Undefined message specified in delay pattern!"; Except.codespan_local msg.span])
      ) msg.sig_types;
      let check_dependent_msg msg_name =
        if msg_name = msg.name then
          raise (Except.TypeError [Text "Self-referential dependent sync mode is not allowed!"; Except.codespan_local msg.span]);
        if not @@ Utils.StringSet.mem msg_name !msg_set then
          raise (Except.TypeError [Text "Undefined message specified in dynamic sync mode!"; Except.codespan_local msg.span])
      in
      match msg.send_sync, msg.recv_sync with
      | Static (o_n, n), Static (o_m, m) ->
        if n <> m || o_n <> o_m then (* the cycle counts on both sides must be equal *)
          raise (Except.TypeError [Text "Static sync mode must be symmetric!"; Except.codespan_local msg.span])
      | Static _, Dependent (msg_name, _)
      | Dependent (msg_name, _), Static _
      | Dynamic, Dependent (msg_name, _) ->
        check_dependent_msg msg_name
      | Dependent _, Dynamic ->
        raise (Except.TypeError [Text "Dependent sync mode cannot be mixed with other sync mode!"; Except.codespan_local msg.span])
      | Dependent (msg1, n1), Dependent (msg2, n2) ->
        if msg1 <> msg2 || n1 <> n2 then
          raise (Except.TypeError [Text "Dependent sync mode must be symmetric!"; Except.codespan_local msg.span]);
        check_dependent_msg msg1
      | _ -> ()
    ) cc.messages
  ) cunit.channel_classes;
  List.iter (fun (sd : session_def ast_node) -> check_blocking_else sd.d.body.span sd.d.body.d) cunit.session_defs;
  List.iter (fun (pool : interface_pool_def ast_node) ->
    List.iter (fun (m : interface_mem_def ast_node) ->
      Option.iter (check_blocking_else m.span) m.d.interface_def) pool.d.interface_members) cunit.pools
