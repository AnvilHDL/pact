module IntHashtbl = Hashtbl.Make(Int)
module EventStateFormatter = struct
  let format_reg_state state_name thread_id ev_id =
    Printf.sprintf "_thread_%d_event_%s_%d" thread_id state_name ev_id

  (* these following are to be suffixed with _q and _n *)
  let format_counter = format_reg_state "counter"
  let format_scorer = format_reg_state "reg"
  let format_syncstate = format_reg_state "syncstate"

  let format_current thread_id ev_id =
    Printf.sprintf "EVENTS%d[%d].event_current" thread_id ev_id
end

let is_wildcard_present msg_list =
    List.exists (fun (msg : Lang.message_specifier) ->
      if msg.endpoint = "*" && msg.msg = "*" then true else false
    ) msg_list

let collect_reg_states g =
  let open EventGraph in
  let need_delay_reg = GraphAnalysis.make_branch_root_delay_checker g.events in
  List.concat_map (fun e ->
    let rec get_reg_States src =

      (
    match src with
    | `Seq (_, d) -> (
      match d with
      | `Cycles n ->
        if g.is_general_recursive || n = 1 then (
          (* split into one-hot single cycles in general recursive case *)
          let sn = EventStateFormatter.format_counter g.thread_id e.id in
          Seq.ints 1 |> Seq.take n |> Seq.map (fun i -> ("logic", Printf.sprintf "%s_%d" sn i))
            |> List.of_seq
        ) else (
          (* otherwise, count *)
          let width = Utils.int_log2 (n + 1) in
          let sn = EventStateFormatter.format_counter g.thread_id e.id in
          [(Printf.sprintf "logic[%d:0]" (width - 1), sn)]
        )
      | `Send _ | `Recv _| `Sync _ ->
        let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
        [("logic", sn)]
      |  `Choice msg_list ->
        if is_wildcard_present msg_list then
          []
        else
        let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
        [("logic", sn)]
    )
    | `Later _ ->
      (* this state needs to distinguish two sources *)
      let sn = EventStateFormatter.format_scorer g.thread_id e.id in
      [("logic[1:0]", sn)]
    | `Branch _  -> []
    | `Root (Some (_, br_side_info)) ->
      let is_branch_empty =  List.for_all(fun child_ev -> match child_ev.source with
        | `Branch _ -> true
        | _ -> false
      ) e.outs in
      if need_delay_reg e && br_side_info.owner_branch.branch_cond = TrueFalse && is_branch_empty then(
        Printf.eprintf "[Warning] Added Delay Register for Event %d in Thread %d to prevent combinational loop! If you dont expect this, please report a bug.\n" e.id g.thread_id;
        let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
        [("logic", sn)]
      )
      else
        []
    | `Root None -> []
    | `Recurse (source, _) ->
      get_reg_States source
      ) in 
      get_reg_States e.source
  ) g.events

(* prints out declarations for event-related wires and registers *)
let codegen_decl printer (g : EventGraph.event_graph) =
  let st_count = List.length g.events in
  (* `current` is a wire indicates if an event is reached in the current cycle *)
  [
    Printf.sprintf "for (genvar i = 0; i < %d; i ++) begin : EVENTS%d" st_count g.thread_id;
    "logic event_current;";
    "end"
  ] |> CodegenPrinter.print_lines printer;

  Printf.sprintf "logic _init_%d;" g.thread_id |> CodegenPrinter.print_line printer;

  (* print per-event states *)
  collect_reg_states g
  |> List.iter (fun (ty, sn) ->
    Printf.sprintf "%s %s_q, %s_n;" ty sn sn |> CodegenPrinter.print_line printer
  )
let _codegen_next_comb printer (g : EventGraph.event_graph) =
  let event = g.events |> List.hd in
  (* generate combinational next state logic for the first event *)
  
  let print_lines = CodegenPrinter.print_lines printer in
  let cn = EventStateFormatter.format_current g.thread_id event.id in
  [
        Printf.sprintf "assign %s = 1'd1;"
        cn
  ] |> print_lines





                
(* generate the next-cycle signals*)
let codegen_next printer (graphs : EventGraph.event_graph_collection)
                         (pg : EventGraph.proc_graph) (g : EventGraph.event_graph) =
  let print_line = CodegenPrinter.print_line printer in
  let print_lines = CodegenPrinter.print_lines printer in
  let lookup_msg_def msg = MessageCollection.lookup_message pg.messages msg graphs.channel_classes in
  GraphAnalysis.events_prepare_outs g.events;
  let recurse_event = List.find (fun e -> let open EventGraph in e.is_loop_terminal && (List.is_empty e.outs)) g.events in
  let need_delay_reg = GraphAnalysis.make_branch_root_delay_checker g.events in
  let print_compute_next (e : EventGraph.event) =
      let cn = EventStateFormatter.format_current g.thread_id e.id in
      let rec gen_next (src : EventGraph.event_source) trigger =
        match src with
        | `Seq (e', d) ->
          (
            let cn' = EventStateFormatter.format_current g.thread_id e'.id in
            match d with
            | `Cycles n when n >= 1 ->
              if g.is_general_recursive || n = 1 then (
                (* To Do : Need to reevaluate *)
                (* we need to split into individual cycles one-hot *)
                let sn = EventStateFormatter.format_counter g.thread_id e.id in
                Printf.sprintf "assign %s = %s_%d_q %s;" cn sn n trigger |> print_line;
                for i = 2 to n do
                  Printf.sprintf "assign %s_%d_n = %s_%d_q;" sn i sn (i - 1) |> print_line
                done;
                Printf.sprintf "assign %s_1_n = %s;" sn cn' |> print_line
              ) else (
                (* recurse at the end node *)
                let width = Utils.int_log2 (n + 1) in
                let sn = EventStateFormatter.format_counter g.thread_id e.id in
                (* current cond *)
                Printf.sprintf "assign %s = (%s_q == %d'd%d) %s;" cn sn width n trigger |> print_line;
                Printf.sprintf "assign %s_n = %s ? %d'd1 : %s ? '0 : %s_q ? (%s_q + %d'd1) : %s_q;" sn cn' width cn sn sn width sn |> print_line
              )
            | `Cycles _ ->
              failwith "Invalid number of cycles" (* TODO: proper handling *)
            | `Send msg ->
              let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
              let msg_def = lookup_msg_def msg |> Option.get in
              if CodegenPort.message_has_ack_port msg_def then (
                (* Valid-Ack: sender asserts valid and waits for ack to come back *)
                let ack_n = CodegenFormat.format_msg_ack_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn ack_n trigger |> print_line;
                Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn ack_n |> print_line
              ) 
            else if CodegenPort.message_has_ready_port msg_def then (
                (* Valid-Ready: sender waits for ready, then asserts valid *)
                let ready_n = CodegenFormat.format_msg_ready_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                  Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn ready_n trigger |> print_line;
                  Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn ready_n |> print_line
              ) else (
                  Printf.sprintf "assign %s = %s || %s_q %s ;" cn cn' sn trigger |> print_line;
                  Printf.sprintf "assign %s_n = 1'b0;" sn |> print_line
              )
            | `Choice msg_list ->
              let is_wildcard_present = is_wildcard_present msg_list in
              (*For this we want to wait till or of the valid/ready port becomes 1 *)
              let sn_opt = if is_wildcard_present then
                None
              else
                Some (EventStateFormatter.format_syncstate g.thread_id e.id) in
              (* Collect all the handshake signals to OR together *)
              let handshake_signals = List.filter_map (fun (msg : Lang.message_specifier) ->
                (* Skip wildcard when collecting signals *)
                if msg.endpoint = "*" && msg.msg = "*" then None
                else
                  let msg_def = lookup_msg_def msg |> Option.get in
                  (* Check message direction: Out (send) or Inp (recv) *)
                  match msg_def.dir with
                  | Out -> 
                    (* Output message (Send): wait for ready port *)
                    if CodegenPort.message_has_ready_port msg_def then
                      Some (CodegenFormat.format_msg_ready_signal_name 
                        (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                    else if CodegenPort.message_has_ack_port msg_def then
                      Some (CodegenFormat.format_msg_ack_signal_name 
                        (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                    else None
                  | Inp ->
                    (* Input message (Recv): wait for valid port *)
                    if CodegenPort.message_has_valid_port msg_def then
                      Some (CodegenFormat.format_msg_valid_signal_name 
                        (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                    else None
              ) msg_list in

              if handshake_signals <> [] && not is_wildcard_present then (
                (* No wildcard: wait for one of the signals *)
              if Option.is_none sn_opt then raise (Failure "Internal error: syncstate expected in Choice without wildcard");
                let sn = Option.get sn_opt in
                let or_condition = String.concat " || " handshake_signals in
                Printf.sprintf "assign %s = ((%s || %s_q) && (%s)) %s;" cn cn' sn or_condition trigger |> print_line;
                Printf.sprintf "assign %s_n = (%s || %s_q) && !(%s);" sn cn' sn or_condition |> print_line
              ) else(
                (* Wildcard present: complete immediately upon any handshake signal *)
                  Printf.sprintf "assign %s = %s %s;" cn cn' trigger |> print_line
              )
              
            | `Recv msg ->
              let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
              let msg_def = lookup_msg_def msg |> Option.get in
              if CodegenPort.message_has_ready_port msg_def then (
                (* Valid-Ready: assert ready and wait for valid to come back *)
                let vld_n = CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                [
                  Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn vld_n trigger;
                  Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn vld_n
                ] |> print_lines
              ) else if CodegenPort.message_has_valid_port msg_def then (
                (* Valid-Ack: wait for valid then assert ack *)
                let vld_n = CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                [
                  Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn vld_n trigger;
                  Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn vld_n
                ] |> print_lines
              ) else (
                [
                  Printf.sprintf "assign %s = ((%s || %s_q) %s;" cn cn' sn trigger;
                  Printf.sprintf "assign %s_n = 1'b0;" sn
                ] |> print_lines
              )
            | `Sync s ->
              let si = Hashtbl.find pg.shared_vars_info s in
              let assigned_at = Option.get si.assigned_at in
              let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
              let wn = EventStateFormatter.format_current assigned_at.graph.thread_id assigned_at.id in

              [
                Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn wn trigger;
                Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn wn
              ] |> print_lines
          )
        | `Branch (_e, br_info) ->
          let branch_cond = List.map (fun (e : EventGraph.event) ->
            EventStateFormatter.format_current g.thread_id e.id) br_info.branches_val |> String.concat " || " in
          Printf.sprintf "assign %s = (%s) %s;" cn branch_cond trigger |> print_line
        | `Later (e1, e2) ->
          let cn1 = EventStateFormatter.format_current g.thread_id e1.id in
          let cn2 = EventStateFormatter.format_current g.thread_id e2.id in
          let sn = EventStateFormatter.format_scorer g.thread_id e.id in
          [
            (* {cn1, cn2} kept in state *)
            Printf.sprintf "assign %s = ((%s & %s_q[0]) | (%s & %s_q[1]) | (%s & %s)) %s;" cn cn1 sn cn2 sn cn1 cn2 trigger;
            Printf.sprintf "assign %s_n = %s_q ^ {%s, %s} ^ {%s, %s};" sn sn cn1 cn2 cn cn
          ] |> print_lines
        | `Root None ->
          [
            Printf.sprintf "assign %s = (_init_%d || %s) %s;"
              cn
              g.thread_id
              (EventStateFormatter.format_current g.thread_id recurse_event.id)
              trigger
          ] |> print_lines
        | `Root (Some (e', br_side_info)) ->
          let cn' = EventStateFormatter.format_current g.thread_id e'.id in
          let w = Option.get br_side_info.owner_branch.branch_cond_v.w in
          let wn = CodegenFormat.format_wirename w.thread_id w.id in
          let need_to_add_delay = need_delay_reg e in
          (
            match br_side_info.owner_branch.branch_cond with
            | TrueFalse ->
              if not e'.removed then (
                if need_to_add_delay then (
                  (* Add one cycle delay to prevent combinational loop *)
                  let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
                  let cond = if br_side_info.branch_side_sel = 0 then
                    Printf.sprintf "%s && %s" cn' wn
                  else
                    Printf.sprintf "%s && !%s" cn' wn
                  in
                  [
                    Printf.sprintf "assign %s = %s_q %s;" cn sn trigger;
                    Printf.sprintf "assign %s_n = %s;" sn cond
                  ] |> print_lines
                ) else (
                  print_line
                    @@
                    if br_side_info.branch_side_sel = 0 then
                      Printf.sprintf "assign %s = (%s && %s) %s;" cn cn' wn trigger
                    else
                      Printf.sprintf "assign %s = (%s && !%s) %s;" cn cn' wn trigger
                )
              )
            | MatchCases pats ->
              let fst_valid_idx = List.find_index (fun (e : EventGraph.event) -> not e.removed) br_side_info.owner_branch.branches_to |> Option.get in
              if br_side_info.branch_side_sel == fst_valid_idx then (
                CodegenPrinter.print_line ~lvl_delta_post:1 printer
                  @@ Printf.sprintf "always_comb begin: _match_cases_%d_%d"
                    g.thread_id e.id;

                List.iter (fun (e : EventGraph.event) ->
                  if not e.removed then
                    CodegenPrinter.print_line printer @@ Printf.sprintf "%s = '0;"
                      @@ EventStateFormatter.format_current g.thread_id e.id
                ) br_side_info.owner_branch.branches_to;

                CodegenPrinter.print_line ~lvl_delta_post:1 printer
                  @@ Printf.sprintf "if (%s) begin" cn';

                (* select cases *)
                CodegenPrinter.print_line ~lvl_delta_post:1 printer
                  @@ Printf.sprintf "unique case (%s)" @@ CodegenFormat.format_wirename w.thread_id w.id;

                (* cases: *)
                let branches_to_no_default =
                  List.to_seq br_side_info.owner_branch.branches_to
                  |> Seq.take (br_side_info.owner_branch.branch_count - 1)
                in
                Seq.iter2 (fun (td_pat : EventGraph.lowering_data) (br_to : EventGraph.event) ->
                  let wp = Option.get td_pat.w in
                  CodegenPrinter.print_line ~lvl_delta_post:1 printer
                    @@ Printf.sprintf "%s:" @@ CodegenFormat.format_wirename wp.thread_id wp.id;
                  if br_to.removed then
                    CodegenPrinter.print_line ~lvl_delta_post:(-1) printer ";"
                  else
                    CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
                      @@ Printf.sprintf "%s = 1'b1;" @@ EventStateFormatter.format_current g.thread_id br_to.id
                ) (List.to_seq pats) branches_to_no_default;

                (* default case *)
                let default_case = List.nth br_side_info.owner_branch.branches_to (br_side_info.owner_branch.branch_count - 1) in
                CodegenPrinter.print_line ~lvl_delta_post:1 printer "default:";
                if default_case.removed then
                  CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
                    @@ Printf.sprintf ";"
                else
                  CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
                    @@ Printf.sprintf "%s = 1'b1;" @@ EventStateFormatter.format_current g.thread_id default_case.id;

                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "endcase";

                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"; (* ending if *)
                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end" (* ending always_comb *)
              )
          )
        | `Recurse (source, trig_id) ->
          let cn' = EventStateFormatter.format_current g.thread_id trig_id in
          let trigger_string = Printf.sprintf "|| %s" cn' in
          gen_next source trigger_string
      in
    gen_next e.source "" 
  in

  List.iter print_compute_next g.events

let codegen_actions printer (g : EventGraph.event_graph) =
  let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) =
    CodegenPrinter.print_line printer ~lvl_delta_pre:lvl_delta_pre ~lvl_delta_post:lvl_delta_post in
  let open EventGraph in
  let print_event_actions (e : event) =
    if e.actions <> [] then begin
      EventStateFormatter.format_current g.thread_id e.id
      |> Printf.sprintf "if (%s) begin" |> print_line ~lvl_delta_post:1;
      let print_action (a : action Lang.ast_node) =
        match a.d with
        | DebugPrint (s, tds) ->
          Printf.sprintf "$display(\"%s\"%s);"
            s
            (List.map (fun (td : lowering_data) ->
              let w = Option.get td.w in
              Printf.sprintf ", %s" @@ CodegenFormat.format_wirename w.thread_id w.id) tds |>
            String.concat "") |> print_line
        | DebugFinish ->
          print_line "$finish;"
        | RegAssign (lval_info, td) ->
          let (le, len) = lval_info.lval_range.subreg_range_interval in
          let w = Option.get td.w in
          Printf.sprintf "%s[%s +: %d] <= %s;"
            (CodegenFormat.format_regname_current lval_info.lval_range.subreg_name)
            (MaybeConst.map (fun td -> Option.get td.w) le |> CodegenFormat.format_wire_maybe_const)
            len
            (CodegenFormat.format_wirename w.thread_id w.id)
            |> print_line
        | PutShared _ -> ()
        | ImmediateRecv _ -> ()
        | ImmediateSend _ -> ()
      in
      List.iter print_action e.actions;
      print_line ~lvl_delta_pre:(-1) "end"
    end else ()
  in
  List.iter print_event_actions g.events


let codegen_transition printer (_graphs : EventGraph.event_graph_collection)
                               (g : EventGraph.event_graph) (reset_by : Lang.message_specifier option) =
  let open EventGraph in
  let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) =
    CodegenPrinter.print_line printer ~lvl_delta_pre:lvl_delta_pre ~lvl_delta_post:lvl_delta_post in
  let reg_states = collect_reg_states g in
  (* reset states *)

  let owned_regs = GraphAnalysis.graph_owned_regs g |> Utils.StringSet.of_list in
  let owned_regs = Utils.StringMap.filter (fun name _ -> Utils.StringSet.mem name owned_regs) g.regs in

  Printf.sprintf "always_ff @(posedge clk_i or negedge rst_ni) begin : _thread_%d_st_transition" g.thread_id |> print_line ~lvl_delta_post:1;
  print_line ~lvl_delta_post:1 "if (~rst_ni) begin";
  (* register reset *)
  print_line @@ Printf.sprintf "_init_%d <= 1'b1;" g.thread_id;
  Utils.StringMap.iter (
    fun _ (r : Lang.reg_def) ->
      let open CodegenFormat in
      Printf.sprintf "%s <= '0;" (format_regname_current r.name) |> print_line
  ) owned_regs;
  List.iter (fun (_, sn) -> Printf.sprintf "%s_q <= '0;" sn |> print_line) reg_states;
  print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 "end else begin";
  (* actions *)
  codegen_actions printer g;
  (
    match reset_by with
    | None -> ()
    | Some reset_by ->
      let reset_msg_signal = CodegenFormat.format_msg_data_signal_name
                            (CodegenFormat.canonicalize_endpoint_name reset_by.endpoint g)
                            reset_by.msg 0 in
      print_line ~lvl_delta_post:1 @@ Printf.sprintf "if (%s) begin" reset_msg_signal;
      print_line @@ Printf.sprintf "_init_%d <= 1'b1;" g.thread_id;
      Utils.StringMap.iter (
        fun _ (r : Lang.reg_def) ->
          let open CodegenFormat in
          Printf.sprintf "%s <= '0;" (format_regname_current r.name) |> print_line
      ) owned_regs;
      List.iter (fun (_, sn) -> Printf.sprintf "%s_q <= '0;" sn |> print_line) reg_states;
          print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 "end else begin"
  );
  print_line @@ Printf.sprintf "_init_%d <= 1'b0;" g.thread_id;
  (* next states *)
  List.iter (fun (_, sn) -> Printf.sprintf "%s_q <= %s_n;" sn sn |> print_line) reg_states;
  if Option.is_some reset_by then print_line ~lvl_delta_pre:(-1) "end";
  print_line ~lvl_delta_pre:(-1) "end";
  print_line ~lvl_delta_pre:(-1) "end"

let codegen_sustained_actions printer (graphs : EventGraph.event_graph_collection)
                                      (pg : EventGraph.proc_graph) (g : EventGraph.event_graph) =
  let print_line = CodegenPrinter.print_line printer in
  let send_or_assigns = Hashtbl.create 8 in
  let recv_or_assigns = Hashtbl.create 8 in
  let choice_valid_asserts = Hashtbl.create 8 in (* For Choice ValidAck send assertions (no data) *)
  let send_valid_only_assigns = Hashtbl.create 8 in
  let insert_to tbl w_name has_sync_port cond =
    (
      match Hashtbl.find_opt tbl w_name with
      | None -> Hashtbl.add tbl w_name (has_sync_port, ref [cond])
      | Some (_has_sync_port', li) -> li := cond::!li
    )
  in
  let insert_valid_only tbl w_name has_sync_port cond =
    (
      match Hashtbl.find_opt tbl w_name with
      | None -> Hashtbl.add tbl w_name (has_sync_port, ref [cond])
      | Some (_has_sync_port', li) -> li := cond::!li
    )
  in
  let lookup_msg_def msg = MessageCollection.lookup_message pg.messages msg graphs.channel_classes in
  let open Lang in
  let print_send_recv (e : EventGraph.event) =
    let open EventGraph in
    let print_recv activated msg =
        let msg_def = lookup_msg_def msg |> Option.get in
        let has_ack_port = CodegenPort.message_has_ack_port msg_def in
        let has_ready_port = CodegenPort.message_has_ready_port msg_def in

        if has_ready_port then
          insert_to recv_or_assigns
            (CodegenFormat.format_msg_ready_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
            has_ready_port
            activated
        else
        insert_to recv_or_assigns
          (CodegenFormat.format_msg_ack_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          has_ack_port
          activated
        
    in
    let print_send activated msg td =
      let msg_def = lookup_msg_def msg |> Option.get in
      let has_valid_port = CodegenPort.message_has_valid_port msg_def in
      if Option.is_some td.w then
        (* Non-void message: has data wire *)
        let w = Option.get td.w in
        insert_to send_or_assigns
          (CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          has_valid_port
          (
            activated,
            CodegenFormat.format_msg_data_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg 0,
            CodegenFormat.format_wirename w.thread_id w.id
          )
      else
        (* Void message: no data wire, only valid signal *)
        insert_valid_only send_valid_only_assigns
          (CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          has_valid_port
          activated
    in

    List.iter (fun (sa : EventGraph.sustained_action Lang.ast_node) ->
      let msg_def_opt = match sa.d.ty with
        | Send (msg, _) -> Some (lookup_msg_def msg)
        | Recv msg -> Some (lookup_msg_def msg)
      in
      let msg_def = Option.get msg_def_opt |> Option.get in
      
      (* Protocol-specific signal assertion:
         - ValidAck Send: assert valid while waiting for ack (sustained)
         - ValidAck Recv: assert ack only when valid arrives (immediate)
         - ValidReady Send: assert valid only when ready arrives (immediate)
         - ValidReady Recv: assert ready while waiting for valid (sustained) *)
      let use_sustained = match sa.d.ty with
        | Send _ -> msg_def.handshake_mode = Lang.ValidAck
        | Recv _ -> msg_def.handshake_mode = Lang.ValidReady
      in
      
      let activated = 
        if use_sustained then
          Printf.sprintf "(%s || %s_q)"
            (EventStateFormatter.format_current g.thread_id e.id)
            (EventStateFormatter.format_syncstate g.thread_id sa.d.until.id)
        else
          EventStateFormatter.format_current g.thread_id sa.d.until.id
      in
      match sa.d.ty with
      | Send (msg, td) -> print_send activated msg td
      | Recv msg -> print_recv activated msg
    ) e.sustained_actions;

    let activated = (EventStateFormatter.format_current g.thread_id e.id) in
    List.iter (fun (ac : EventGraph.action Lang.ast_node) ->
      match ac.d with
      | ImmediateSend (msg, td) -> print_send activated msg td
      | ImmediateRecv msg -> print_recv activated msg
      | _ -> ()
    ) e.actions;

    (* Handle Choice events: assert signals while waiting for handshake *)
    match e.source with
    | `Seq (_, `Choice msg_list) ->
      let is_wildcard = is_wildcard_present msg_list in
      let activated = if not is_wildcard then (
           Printf.sprintf "(%s || %s_q)"
          (EventStateFormatter.format_current g.thread_id e.id)
          (EventStateFormatter.format_syncstate g.thread_id e.id)
      ) else (
          EventStateFormatter.format_current g.thread_id e.id
      ) in
        List.iter (fun (msg : Lang.message_specifier) ->
          if msg.endpoint <> "*" || msg.msg <> "*" then
            let msg_def = lookup_msg_def msg |> Option.get in
            match msg_def.dir with
            | Out ->
              (* Output message (Send): assert valid only for ValidAck protocol *)
              if msg_def.handshake_mode = Lang.ValidAck then
                insert_to choice_valid_asserts
                  (CodegenFormat.format_msg_valid_signal_name 
                    (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                  true
                  activated
            | Inp ->
              (* Input message (Recv): assert ready only for ValidReady protocol *)
              if msg_def.handshake_mode = Lang.ValidReady then
                insert_to recv_or_assigns
                  (CodegenFormat.format_msg_ready_signal_name 
                    (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                  true
                  activated
        ) msg_list

    | _ -> ()
  in
  (* assuming reverse topo order, the assign lists will be in topo order *)
  List.iter print_send_recv g.events;
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      String.concat " || " !conds
      |> Printf.sprintf "assign %s = %s;" w_name
      |> print_line
    )
  ) recv_or_assigns;

  (* Merge Choice valid assertions into send_or_assigns *)
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      List.iter (fun cond ->
        insert_to send_or_assigns w_name true (cond, "", "")
      ) !conds
    )
  ) choice_valid_asserts;
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      String.concat " || " !conds
      |> Printf.sprintf "assign %s = %s;" w_name
      |> print_line
    )
  ) send_valid_only_assigns;

  let send_data_selectors = ref [] in
  Hashtbl.iter (fun w_name (has_sync_port, conds_dw) ->
    if has_sync_port then (
      List.map (fun (c, _, _) -> c) !conds_dw
      |> String.concat " || "
      |> Printf.sprintf "assign %s = %s;" w_name
      |> print_line;
    );
    (* Filter out entries with empty data strings (from Choice assertions) *)
    let conds_with_data = List.filter (fun (_, dw, vw) -> dw <> "" && vw <> "") !conds_dw in
    let n = List.length conds_with_data in
    if n = 1 then (
      let (_, dw, vw) = List.hd conds_with_data in
      Printf.sprintf "assign %s = %s;" dw vw
      |> print_line
    ) else if n > 1 then (
      (* if we have more than one site that sends, keep track of which event is the last send (TODO: optimisation) *)
      let width = Utils.int_log2 n in
      send_data_selectors := (width, w_name, conds_with_data)::!send_data_selectors
    )
    (* if n = 0, no data signals to assign (all are Choice assertions) *)
  ) send_or_assigns;

  if !send_data_selectors <> [] then (
    (* generate declarations for selectors *)
    List.iter (fun (width, name, conds_dw) ->
      Printf.sprintf "logic[%d:0] %s_selector_q, %s_selector_n;" (width - 1) name name
      |> print_line;
      let (_, dw, _) = List.hd conds_dw in
      List.mapi (fun site_idx (_, _, vw) ->
        Printf.sprintf "(%s_selector_n == %d'd%d) ? %s : " name width site_idx vw
      ) conds_dw
      |> String.concat ""
      |> Printf.sprintf "assign %s = %s'0;" dw
      |> print_line
    ) !send_data_selectors;

    Printf.sprintf "always_comb begin: _thread_%d_selector" g.thread_id
    |> CodegenPrinter.print_line ~lvl_delta_post:1 printer;
    List.iter (fun (width, name, conds) ->
      Printf.sprintf "%s_selector_n = %s_selector_q;" name name |> print_line;
      List.iteri (fun site_idx (c, _, _) ->
        Printf.sprintf "if (%s) %s_selector_n = %d'd%d;" c name width site_idx
          |> print_line
      ) conds;
    ) !send_data_selectors;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";

    Printf.sprintf "always_ff @(posedge clk_i or negedge rst_ni) begin : _thread_%d_selector_trans" g.thread_id
    |> CodegenPrinter.print_line ~lvl_delta_post:1 printer;

    CodegenPrinter.print_line ~lvl_delta_post:1 printer "if (~rst_ni) begin";
    List.iter (fun (_, name, _) ->
      Printf.sprintf "%s_selector_q <= '0;" name
      |> print_line
    ) !send_data_selectors;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 printer "end else begin";
    List.iter (fun (_, name, _) ->
      Printf.sprintf "%s_selector_q <= %s_selector_n;" name name
      |> print_line
    ) !send_data_selectors;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";

    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
  )

let codegen_states printer
  (graphs : EventGraph.event_graph_collection)
  (pg : EventGraph.proc_graph)
  (g : EventGraph.event_graph)
  (reset_by : Lang.message_specifier option) =
  if g.comb then(
    codegen_sustained_actions printer graphs pg g
  ) else (
    codegen_decl printer g;
    codegen_next printer graphs pg g;
    codegen_sustained_actions printer graphs pg g;
    codegen_transition printer graphs g reset_by
  )

let codegen_proc_states printer proc =
  let open EventGraph in
  let g = fst @@ List.hd proc.threads in

  CodegenPrinter.print_line ~lvl_delta_post:1 printer
    "always_ff @(posedge clk_i or negedge rst_ni) begin : _proc_transition";
  CodegenPrinter.print_line ~lvl_delta_post:1 printer "if (~rst_ni) begin";

  (* figure out the set of registers not set in any thread *)
  let owned_regs = ref Utils.StringSet.empty in
  List.iter (
    fun (graph, _) ->
      owned_regs := GraphAnalysis.graph_owned_regs graph
                |> Utils.StringSet.of_list |> Utils.StringSet.union !owned_regs
  ) proc.threads;

  Utils.StringMap.filter (fun name _ -> Utils.StringSet.mem name !owned_regs |> not) g.regs
  |> Utils.StringMap.iter (
    fun _ (r : Lang.reg_def) ->
      let open CodegenFormat in
      Printf.sprintf "%s <= '0;" (format_regname_current r.name)
        |> CodegenPrinter.print_line printer
  );
  CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";
  CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"

