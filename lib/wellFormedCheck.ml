open Lang


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
