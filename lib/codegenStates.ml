module IntHashtbl = Hashtbl.Make(Int)
module EventStateFormatter = struct
  let format_reg_state state_name thread_id ev_id =
    Printf.sprintf "_thread_%d_event_%s_%d" thread_id state_name ev_id

  (* these following are to be suffixed with _q and _n *)
  let format_counter = format_reg_state "counter"
  let format_scorer = format_reg_state "reg"
  let format_syncstate = format_reg_state "syncstate"
  let format_select_selected = format_reg_state "select_selected"
  let format_select_done = format_reg_state "select_done"

  let format_current thread_id ev_id =
    Printf.sprintf "EVENTS%d[%d].event_current" thread_id ev_id
end

let flatten_choice_msg_groups = List.flatten

let is_wildcard_present msg_groups =
    List.exists (fun (msg : Lang.message_specifier) ->
      if msg.endpoint = "*" && msg.msg = "*" then true else false
    ) (flatten_choice_msg_groups msg_groups)

let is_wildcard_msg (msg : Lang.message_specifier) =
  msg.endpoint = "*" && msg.msg = "*"

let is_wildcard_msg_group msg_group =
  List.exists is_wildcard_msg msg_group

let format_msg_group msg_group =
  msg_group
  |> List.map Lang.string_of_msg_spec
  |> String.concat ", "

let plural count singular plural_form =
  if count = 1 then singular else plural_form

let describe_atomic_delay = function
  | `Cycles n -> Printf.sprintf "delay %d %s" n (plural n "cycle" "cycles")
  | `Send (msg, kind) ->
    Printf.sprintf "%s %s" (match kind with Lang.Instant -> "isend" | Lang.Blocking -> "send")
      (Lang.string_of_msg_spec msg)
  | `Recv (msg, kind) ->
    Printf.sprintf "%s %s" (match kind with Lang.Instant -> "irecv" | Lang.Blocking -> "recv")
      (Lang.string_of_msg_spec msg)
  | `Choice (msg_groups, _, _) ->
    Printf.sprintf "choice among %s"
      (msg_groups |> List.map format_msg_group |> String.concat " | ")
  | `Sync shared_ident -> Printf.sprintf "sync on %s" shared_ident

let describe_branch_side (br_side_info : EventGraph.branch_side_info) =
  match br_side_info.owner_branch.branch_cond with
  | EventGraph.TrueFalse ->
    if br_side_info.branch_side_sel = 0 then "true branch" else "false branch"
  | EventGraph.MatchCases _ | EventGraph.MatchCasesNoDefault _ ->
    Printf.sprintf "match case %d" br_side_info.branch_side_sel

let describe_event_source (source : EventGraph.event_source) =
  let open EventGraph in
  match source with
  | `Root None -> "thread root"
  | `Root (Some (parent_event, br_side_info)) ->
    Printf.sprintf "%s from event %d"
      (describe_branch_side br_side_info)
      parent_event.id
  | `Later (left_event, right_event) ->
    Printf.sprintf "after both event %d and event %d" left_event.id right_event.id
  | `Seq (prev_event, delay) ->
    Printf.sprintf "after event %d, %s" prev_event.id (describe_atomic_delay delay)
  | `Branch (source_event, branch_info) ->
    Printf.sprintf "join %d %s from event %d"
      branch_info.branch_count
      (plural branch_info.branch_count "branch" "branches")
      source_event.id
  | `Recurse (_, trigger_event_id) ->
    Printf.sprintf "recursive path triggered by event %d" trigger_event_id
  | `Select (parent_event, msg_group) ->
    Printf.sprintf "Offer Select from event %d with message group {%s}"
      parent_event.id
      (msg_group |> List.map Lang.string_of_msg_spec |> String.concat "; ")
  | `SelectJoin join_info ->
    Printf.sprintf "Joining offer select from parent event %d with join roots [%s] and join nodes [%s]"
      join_info.join_parent.id
      (String.concat "; " (List.map (fun e -> string_of_int e.id) join_info.join_roots))
      (String.concat "; " (List.map (fun e -> string_of_int e.id) join_info.join_nodes))
      

(* The number of cycles every arm of an offer takes from its selection to its
   end, when it is the same fixed number for all arms: arms made only of delays,
   register writes and instantaneous actions. All arms of one offer are selected
   in the same cycle, so they then also finish together. Used at -O 3. *)
let select_join_fixed_latency (config : Config.compile_config) (join_info : EventGraph.join_info) =
  let rec latency (root : EventGraph.event) (ev : EventGraph.event) =
    if ev.id = root.id then Some 0
    else match ev.source with
      | `Seq (prev, `Cycles n) -> Option.map (( + ) n) (latency root prev)
      | `Seq (prev, (`Send (_, Lang.Instant) | `Recv (_, Lang.Instant))) -> latency root prev
      | `Later (a, b) ->
        (match latency root a, latency root b with
         | Some x, Some y -> Some (max x y)
         | _ -> None)
      | `Root (Some (parent, _)) -> latency root parent
      | `Branch (_, info) ->
        (match List.map (latency root) info.branches_val with
         | Some x :: rest when List.for_all (( = ) (Some x)) rest -> Some x
         | _ -> None)
      | _ -> None
  in
  if config.opt_level < 3 then None
  else match List.map2 latency join_info.join_roots join_info.join_nodes with
  | Some d :: rest when List.for_all (( = ) (Some d)) rest -> Some d
  | _ -> None

(* Whether arm [idx] of the offer joined at [join_id] was taken. A fresh offer
   can finish in its selection cycle; when an older offer is pending, roots in
   this cycle belong to its successor. An arm known to take a cycle has always
   been recorded by the time the join is reached. *)
let select_join_arm_taken ?(recorded = false) thread_id join_id idx (root : EventGraph.event) =
  let selected_q = EventStateFormatter.format_select_selected thread_id join_id ^ "_q" in
  if recorded then Printf.sprintf "%s[%d]" selected_q idx
  else
    Printf.sprintf "(%s[%d] || (!(|%s) && %s))" selected_q idx selected_q
      (EventStateFormatter.format_current thread_id root.id)

(* -O 3 sharing of one-cycle delay flip-flops. A one-cycle delay is one
   flip-flop on its input, so delay(a) || delay(b) = delay(a || b): delays whose
   only reader ORs them into the same event (a branch join, a fixed-latency
   offer join, or a recursion re-entering it) share one flip-flop. A loop whose end is
   such a delay, read by nothing else, starts from that flip-flop reset to 1
   instead of a separate start flag. *)
type delay_sharing = {
  shared_rep : (int, int) Hashtbl.t; (* member delay -> delay that keeps the flip-flop *)
  shared_inputs : (int, EventGraph.event list) Hashtbl.t; (* that delay -> inputs of all members *)
  start_delay : int option; (* loop-end delay whose flip-flop resets to 1 *)
}

let delay_sharing (config : Config.compile_config) (g : EventGraph.event_graph) =
  let open EventGraph in
  let shared_rep = Hashtbl.create 8 and shared_inputs = Hashtbl.create 8 in
  if config.opt_level < 3 || g.comb then { shared_rep; shared_inputs; start_delay = None }
  else begin
    (* every reader of every event: the OR of a branch join, or anything else *)
    let reads = Hashtbl.create 16 in
    let add id r = Hashtbl.replace reads id (r :: Option.value ~default:[] (Hashtbl.find_opt reads id)) in
    let rec src_reads (x : event) = function
      (* a same-cycle step passes its input on unchanged *)
      | `Seq (e, `Cycles 0) -> add e.id (`Or x.id)
      | `Seq (e, _) -> add e.id `Other
      | `Later (a, b) -> add a.id `Other; add b.id `Other
      | `Branch (e_r, br) ->
        add e_r.id `Other;
        List.iter (fun (v : event) -> add v.id (`Or x.id)) br.branches_val
      | `Root (Some (e', _)) -> add e'.id `Other
      | `Root None -> ()
      (* a recursion trigger is ORed into the event it re-enters *)
      | `Recurse (src, trig) -> add trig (`Or x.id); src_reads x src
      | `Select (p, _) -> add p.id `Other
      | `SelectJoin ji ->
        add ji.join_parent.id `Other;
        List.iter (fun (e : event) -> add e.id `Other) ji.join_roots;
        (* a join whose arms finish together fires on the OR of their ends *)
        let node_read = if Option.is_some (select_join_fixed_latency config ji) then `Or x.id else `Other in
        List.iter (fun (e : event) -> add e.id node_read) ji.join_nodes
    in
    List.iter (fun (x : event) ->
      src_reads x x.source;
      List.iter (fun (sa : sustained_action Lang.ast_node) -> add sa.d.until.id `Other) x.sustained_actions
    ) g.events;
    let readers (e : event) = List.sort_uniq compare (Option.value ~default:[] (Hashtbl.find_opt reads e.id)) in
    let plain_delay (e : event) = match e.source with
      | `Seq (p, `Cycles 1) when e.actions = [] && e.sustained_actions = [] -> Some p
      | _ -> None
    in
    let groups = Hashtbl.create 8 in
    List.iter (fun (e : event) ->
      match plain_delay e, readers e with
      | Some p, [ `Or j ] -> Hashtbl.replace groups j ((e, p) :: Option.value ~default:[] (Hashtbl.find_opt groups j))
      | _ -> ()
    ) g.events;
    Hashtbl.iter (fun _ members ->
      if List.length members >= 2 then begin
        let members = List.sort (fun ((a : event), _) ((b : event), _) -> compare a.id b.id) members in
        let (keep : event) = fst (List.hd members) in
        List.iter (fun ((m : event), _) -> if m.id <> keep.id then Hashtbl.replace shared_rep m.id keep.id) members;
        Hashtbl.replace shared_inputs keep.id (List.map snd members)
      end
    ) groups;
    GraphAnalysis.events_prepare_outs g.events;
    let start_delay =
      match List.find_opt (fun e -> e.is_loop_terminal && List.is_empty e.outs) g.events with
      | Some t when Option.is_some (plain_delay t) && readers t = [] -> Some t.id
      | _ -> None
    in
    { shared_rep; shared_inputs; start_delay }
  end

let collect_reg_states config g =
  let open EventGraph in
  let sharing = delay_sharing config g in
  let need_delay_reg = GraphAnalysis.make_branch_root_delay_checker g.events in
  List.concat_map (fun e ->
    let rec collect_event_reg_states src =

      (
    match src with
    | `Seq (_, d) -> (
      match d with
      | `Cycles 0 -> []
      | `Cycles 1 when Hashtbl.mem sharing.shared_rep e.id -> []
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
      (* Instantaneous ops never wait, so they need no syncstate. *)
      | `Send (_, Lang.Instant) | `Recv (_, Lang.Instant) -> []
      | `Send _ | `Recv _| `Sync _ ->
        let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
        [("logic", sn)]
      |  `Choice (msg_list, kind, _) ->
        (* An instantaneous choice never waits, so it needs no syncstate. *)
        if kind = Lang.Instant || is_wildcard_present msg_list then
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
    | `Root (Some _) ->
      if need_delay_reg e then(
        CliOutput.warning "Added a delay register for event %d in thread %d to prevent a combinational loop. If you do not expect this, please report a bug." e.id g.thread_id;
        let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
        [("logic", sn)]
      )
      else
        []
    | `Root None -> []
    | `Recurse (source, _) ->
      collect_event_reg_states source
    | `Select _ -> []
    | `SelectJoin join_info ->
      let width = List.length join_info.join_roots in
      let ty = Printf.sprintf "logic[%d:0]" (max 0 (width - 1)) in
      let selected = (ty, EventStateFormatter.format_select_selected g.thread_id e.id) in
      (* Arms that finish together need no done bits, and the arms taken are
         kept only for an offer match. *)
      (match select_join_fixed_latency config join_info, join_info.join_tag with
       | Some _, Some _ -> [ selected ]
       | Some _, None -> []
       | None, _ -> [ selected; (ty, EventStateFormatter.format_select_done g.thread_id e.id) ])
      ) in 
      collect_event_reg_states e.source
  ) g.events

(* prints out declarations for event-related wires and registers *)
let codegen_decl config printer (g : EventGraph.event_graph) =
  let st_count = List.length g.events in
  CodegenPrinter.print_section printer (Printf.sprintf "Thread %d event state" g.thread_id);
  CodegenPrinter.print_comment printer "event_current marks events active in the current cycle";
  Printf.sprintf "for (genvar i = 0; i < %d; i ++) begin : EVENTS%d" st_count g.thread_id
  |> CodegenPrinter.print_line ~lvl_delta_post:1 printer;
  CodegenPrinter.print_line printer "logic event_current;";
  CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";

  if Option.is_none (delay_sharing config g).start_delay then
    Printf.sprintf "logic _init_%d;" g.thread_id |> CodegenPrinter.print_line printer;

  (* print per-event states *)
  collect_reg_states config g
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
let codegen_next config printer (graphs : EventGraph.event_graph_collection)
                         (pg : EventGraph.proc_graph) (g : EventGraph.event_graph) =
  let print_line = CodegenPrinter.print_line printer in
  let print_lines = List.iter print_line in
  let lookup_msg_def msg = MessageCollection.lookup_message pg.messages msg graphs.channel_classes in
  let resolve_mode = HandshakeResolve.resolver_for graphs pg in
  let mode_of (msg : Lang.message_specifier) =
    resolve_mode (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
  let readiness_signal_of_msg (msg : Lang.message_specifier) =
    let msg_def = lookup_msg_def msg |> Option.get in
    match msg_def.dir with
    | Out ->
      if CodegenPort.message_has_ack_port ~mode:(mode_of msg) msg_def then
        CodegenFormat.format_msg_ack_signal_name
          (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg
      else if CodegenPort.message_has_ready_port ~mode:(mode_of msg) msg_def then
        CodegenFormat.format_msg_ready_signal_name
          (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg
      else
        "1'b1"
    | Inp ->
      if CodegenPort.message_has_valid_port msg_def then
        CodegenFormat.format_msg_valid_signal_name
          (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg
      else
        "1'b1"
  in
  let readiness_condition_of_msg_group msg_group =
    match List.filter (fun msg -> not (is_wildcard_msg msg)) msg_group with
    | [] -> "1'b1"
    | msgs ->
      msgs
      |> List.map readiness_signal_of_msg
      |> String.concat " && "
      |> Printf.sprintf "(%s)"
  in
  let select_condition_for_event (parent_event : EventGraph.event) msg_group =
    if not (is_wildcard_msg_group msg_group) then
      readiness_condition_of_msg_group msg_group
    else
      (* Siblings share the choice; a recursing else arm is not in the join. *)
      let sibling_conditions =
        g.events
        |> List.filter_map (fun (event : EventGraph.event) ->
          match event.source with
          | `Select (p, sibling_group)
            when p.id = parent_event.id && not (is_wildcard_msg_group sibling_group) ->
            Some (readiness_condition_of_msg_group sibling_group)
          | _ -> None
        )
      in
      match sibling_conditions with
      | [] -> "1'b1"
      | _ ->
        sibling_conditions
        |> String.concat " || "
        |> Printf.sprintf "!(%s)"
  in
  GraphAnalysis.events_prepare_outs g.events;
  let sharing = delay_sharing config g in
  let recurse_event = List.find (fun e -> let open EventGraph in e.is_loop_terminal && (List.is_empty e.outs)) g.events in
  let need_delay_reg = GraphAnalysis.make_branch_root_delay_checker g.events in
  let print_compute_next (e : EventGraph.event) =
      CodegenPrinter.print_comment printer
        (Printf.sprintf "event %d: %s" e.id (describe_event_source e.source));
      let cn = EventStateFormatter.format_current g.thread_id e.id in
      let rec gen_next (src : EventGraph.event_source) trigger =
        match src with
        | `Seq (e', d) ->
          (
            let cn' = EventStateFormatter.format_current g.thread_id e'.id in
            match d with
            | `Cycles 1 when Hashtbl.mem sharing.shared_rep e.id ->
              (* shares the flip-flop of another delay into the same join *)
              let keep = Hashtbl.find sharing.shared_rep e.id in
              Printf.sprintf "assign %s = %s_1_q %s;" cn (EventStateFormatter.format_counter g.thread_id keep) trigger |> print_line
            | `Cycles 1 when Hashtbl.mem sharing.shared_inputs e.id ->
              let sn = EventStateFormatter.format_counter g.thread_id e.id in
              let inputs = Hashtbl.find sharing.shared_inputs e.id
                |> List.map (fun (p : EventGraph.event) -> EventStateFormatter.format_current g.thread_id p.id) in
              Printf.sprintf "assign %s = %s_1_q %s;" cn sn trigger |> print_line;
              Printf.sprintf "assign %s_1_n = %s;" sn (String.concat " || " inputs) |> print_line
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
            | `Cycles 0 ->
              (* a step in the same cycle *)
              Printf.sprintf "assign %s = %s %s;" cn cn' trigger |> print_line
            | `Cycles _ ->
              failwith "Invalid number of cycles" (* TODO: proper handling *)
            | `Send (msg, kind) ->
              let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
              let msg_def = lookup_msg_def msg |> Option.get in
              (* Only a blocking send waits on the reverse signal. *)
              let mode = mode_of msg in
              (match (if CodegenPort.site_blocks ~mode msg_def kind then
                        CodegenPort.site_reverse_signal ~mode msg_def
                      else None) with
              | Some CodegenPort.UsesAck ->
                (* Valid-Ack: sender asserts valid and waits for ack to come back *)
                let ack_n = CodegenFormat.format_msg_ack_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn ack_n trigger |> print_line;
                Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn ack_n |> print_line
              | Some CodegenPort.UsesReady ->
                (* Valid-Ready: sender waits for ready, then asserts valid *)
                let ready_n = CodegenFormat.format_msg_ready_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                  Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn ready_n trigger |> print_line;
                  Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn ready_n |> print_line
              | None when kind = Lang.Instant ->
                  Printf.sprintf "assign %s = %s %s;" cn cn' trigger |> print_line
              | None ->
                  Printf.sprintf "assign %s = %s || %s_q %s ;" cn cn' sn trigger |> print_line;
                  Printf.sprintf "assign %s_n = 1'b0;" sn |> print_line)
            | `Choice (msg_groups, choice_kind, _) ->
              let msg_list = flatten_choice_msg_groups msg_groups in
              let is_wildcard_present = is_wildcard_present msg_groups in
              (*For this we want to wait till or of the valid/ready port becomes 1 *)
              let sn_opt = if is_wildcard_present || choice_kind = Lang.Instant then
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
                    if CodegenPort.message_has_ready_port ~mode:(mode_of msg) msg_def then
                      Some (CodegenFormat.format_msg_ready_signal_name 
                        (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                    else if CodegenPort.message_has_ack_port ~mode:(mode_of msg) msg_def then
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

              (* An instantaneous choice completes in the cycle it is reached:
                 it never latches a syncstate to wait for a peer. *)
              if handshake_signals <> [] && not is_wildcard_present
                 && choice_kind <> Lang.Instant then (
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
              
            | `Recv (msg, kind) ->
              let sn = EventStateFormatter.format_syncstate g.thread_id e.id in
              let msg_def = lookup_msg_def msg |> Option.get in
              (* Only a blocking recv waits on valid. *)
              if CodegenPort.site_blocks ~mode:(mode_of msg) msg_def kind
                 && CodegenPort.message_has_valid_port msg_def then (
                let vld_n = CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
                [
                  Printf.sprintf "assign %s = ((%s || %s_q) && %s) %s;" cn cn' sn vld_n trigger;
                  Printf.sprintf "assign %s_n = (%s || %s_q) && !%s;" sn cn' sn vld_n
                ] |> print_lines
              ) else if kind = Lang.Instant then
                Printf.sprintf "assign %s = %s %s;" cn cn' trigger |> print_line
              else (
                [
                  Printf.sprintf "assign %s = (%s || %s_q) %s;" cn cn' sn trigger;
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
          let branch_cond = match br_info.branches_val with
            | [] -> "1'b0" (* no side completes *)
            | vals -> List.map (fun (e : EventGraph.event) ->
                EventStateFormatter.format_current g.thread_id e.id) vals |> String.concat " || " in
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
        | `Root None when Option.is_some sharing.start_delay ->
          (* the loop-end delay is reset to 1, so it also starts the loop *)
          Printf.sprintf "assign %s = %s %s;" cn
            (EventStateFormatter.format_current g.thread_id recurse_event.id) trigger |> print_line
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
            | MatchCases _ | MatchCasesNoDefault _ ->
              let (pats, has_default) =
                match br_side_info.owner_branch.branch_cond with
                | MatchCases p -> (p, true)
                | MatchCasesNoDefault p -> (p, false)
                | TrueFalse -> ([], true)
              in
              let fst_valid_idx = List.find_index (fun (e : EventGraph.event) -> not e.removed) br_side_info.owner_branch.branches_to |> Option.get in
              if br_side_info.branch_side_sel = fst_valid_idx then (
                CodegenPrinter.print_line ~lvl_delta_post:1 printer
                  @@ Printf.sprintf "always_comb begin: _thread_%d_event_%d_match_cases"
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
                  |> Seq.take (if has_default then br_side_info.owner_branch.branch_count - 1
                               else br_side_info.owner_branch.branch_count)
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
                CodegenPrinter.print_line ~lvl_delta_post:1 printer "default:";
                if not has_default then
                  (* No else arm: nothing is enabled when no case matches. *)
                  CodegenPrinter.print_line ~lvl_delta_post:(-1) printer ";"
                else (
                  let default_case = List.nth br_side_info.owner_branch.branches_to (br_side_info.owner_branch.branch_count - 1) in
                  if default_case.removed then
                    CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
                      @@ Printf.sprintf ";"
                  else
                    CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
                      @@ Printf.sprintf "%s = 1'b1;" @@ EventStateFormatter.format_current g.thread_id default_case.id
                );

                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "endcase";

                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"; (* ending if *)
                CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end" (* ending always_comb *)
              )
          )
        | `Recurse (source, trig_id) ->
          let cn' = EventStateFormatter.format_current g.thread_id trig_id in
          let trigger_string = Printf.sprintf "%s || %s" trigger cn' in
          gen_next source trigger_string
        | `Select (parent_event, msg_group) ->
          let parent_current = EventStateFormatter.format_current g.thread_id parent_event.id in
          let select_condition = select_condition_for_event parent_event msg_group in
          Printf.sprintf "assign %s = (%s && %s) %s;"
            cn
            parent_current
            select_condition
            trigger
          |> print_line
        | `SelectJoin join_info when Option.is_some (select_join_fixed_latency config join_info) ->
          (* All taken arms finish in the same cycle, so the join fires when
             any arm ends. The arms taken are recorded only for an offer match. *)
          let join_arms = List.combine join_info.join_roots join_info.join_nodes in
          let join_node_current (join_node : EventGraph.event) =
            EventStateFormatter.format_current g.thread_id join_node.id
          in
          let any_done = match join_arms with
            | [] -> "1'b0"
            | _ ->
              List.map (fun (_, node) -> join_node_current node) join_arms
              |> String.concat " || " |> Printf.sprintf "(%s)"
          in
          Printf.sprintf "assign %s = %s %s;" cn any_done trigger |> print_line;
          if Option.is_some join_info.join_tag then begin
            let selected_name = EventStateFormatter.format_select_selected g.thread_id e.id in
            let selected_q = selected_name ^ "_q" and selected_n = selected_name ^ "_n" in
            CodegenPrinter.print_line ~lvl_delta_post:1 printer
              @@ Printf.sprintf "always_comb begin: _thread_%d_event_%d_select_join_state"
                g.thread_id e.id;
            Printf.sprintf "%s = %s ? '0 : %s;" selected_n cn selected_q |> print_line;
            List.iteri (fun idx ((root : EventGraph.event), _) ->
              Printf.sprintf "if (%s && (!%s || (|%s))) %s[%d] = 1'b1;"
                (EventStateFormatter.format_current g.thread_id root.id)
                cn selected_q selected_n idx
              |> print_line) join_arms;
            CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
          end
        | `SelectJoin join_info ->
          let join_arms = List.combine join_info.join_roots join_info.join_nodes in
          let width = List.length join_arms in
          let selected_name = EventStateFormatter.format_select_selected g.thread_id e.id in
          let done_name = EventStateFormatter.format_select_done g.thread_id e.id in
          let selected_q = selected_name ^ "_q" in
          let selected_n = selected_name ^ "_n" in
          let done_q = done_name ^ "_q" in
          let done_n = done_name ^ "_n" in
          let done_bit idx = Printf.sprintf "%s[%d]" done_q idx in
          let join_node_current (join_node : EventGraph.event) =
            EventStateFormatter.format_current g.thread_id join_node.id
          in
          let pending = Printf.sprintf "(|%s)" selected_q in
          let selected idx root = select_join_arm_taken g.thread_id e.id idx root in
          let any_selected =
            if width = 0 then
              "1'b0"
            else
              List.mapi (fun idx (root, _) -> selected idx root) join_arms
              |> String.concat " || "
              |> Printf.sprintf "(%s)"
          in
          let selected_done =
            if width = 0 then
              "1'b0"
            else
              List.mapi (fun idx ((root, join_node) : EventGraph.event * EventGraph.event) ->
                Printf.sprintf "(!%s || %s || %s)"
                  (selected idx root)
                  (done_bit idx)
                  (join_node_current join_node)
              ) join_arms
              |> String.concat " && "
              |> Printf.sprintf "(%s)"
          in
          Printf.sprintf "assign %s = (%s && %s) %s;"
            cn
            any_selected
            selected_done
            trigger
          |> print_line;
          CodegenPrinter.print_line ~lvl_delta_post:1 printer
            @@ Printf.sprintf "always_comb begin: _thread_%d_event_%d_select_join_state"
              g.thread_id e.id;
          Printf.sprintf "%s = %s ? '0 : %s;" selected_n cn selected_q |> print_line;
          Printf.sprintf "%s = %s ? '0 : %s;" done_n cn done_q |> print_line;
          List.iteri (fun idx ((root, join_node) : EventGraph.event * EventGraph.event) ->
            let root_current = EventStateFormatter.format_current g.thread_id root.id in
            let join_current = join_node_current join_node in
            Printf.sprintf "if (%s && (!%s || %s)) %s[%d] = 1'b1;"
              root_current
              cn
              pending
              selected_n
              idx
            |> print_line;
            Printf.sprintf "if (((%s ? 1'b0 : %s[%d]) || (%s && (!%s || %s))) && %s) %s[%d] = 1'b1;"
              cn
              selected_q
              idx
              root_current
              cn
              pending
              join_current
              done_n
              idx
            |> print_line
          ) join_arms;
          CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
      in
    gen_next e.source "" 
  in

  List.iter print_compute_next g.events

(* Every RegAssign to reg_name, in event order, across the whole graph. *)
let collect_reg_assigns (g : EventGraph.event_graph) : (string, (EventGraph.event * EventGraph.lvalue_info * EventGraph.lowering_data) list) Hashtbl.t =
  let open EventGraph in
  let table = Hashtbl.create 16 in
  List.iter (fun (e : event) ->
    List.iter (fun (a : action Lang.ast_node) ->
      match a.d with
      | RegAssign (lval_info, td) ->
        let name = lval_info.lval_range.subreg_name in
        let prev = Hashtbl.find_opt table name |> Option.value ~default:[] in
        Hashtbl.replace table name (prev @ [(e, lval_info, td)])
      | _ -> ()
    ) e.actions
  ) g.events;
  table

(* Registers written from 2+ distinct events; only these get merged into one always_comb next-state signal. *)
let multi_writer_reg_names (reg_assigns : (string, 'a list) Hashtbl.t) : Utils.StringSet.t =
  Hashtbl.fold (fun name sites acc ->
    let distinct_events = List.length (List.sort_uniq (fun (e1, _, _) (e2, _, _) -> compare e1.EventGraph.id e2.EventGraph.id) sites) in
    if distinct_events >= 2 then Utils.StringSet.add name acc else acc
  ) reg_assigns Utils.StringSet.empty

(* For every multi-writer register: one always_comb block holding data_n = data_q, then one guarded override per writer event, in event order. *)
let codegen_reg_next_state printer (graphs : EventGraph.event_graph_collection) (g : EventGraph.event_graph)
    (reg_assigns : (string, (EventGraph.event * EventGraph.lvalue_info * EventGraph.lowering_data) list) Hashtbl.t)
    (multi_writer : Utils.StringSet.t) =
  let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) =
    CodegenPrinter.print_line printer ~lvl_delta_pre:lvl_delta_pre ~lvl_delta_post:lvl_delta_post in
  if not (Utils.StringSet.is_empty multi_writer) then (
    Utils.StringSet.iter (fun name ->
      let (r : Lang.reg_def) = Utils.StringMap.find name g.regs in
      Printf.sprintf "%s %s;"
        (CodegenFormat.format_dtype graphs.typedefs graphs.macro_defs r.d_type)
        (CodegenFormat.format_regname_next name)
      |> print_line
    ) multi_writer;
    Printf.sprintf "always_comb begin : _thread_%d_reg_next_state" g.thread_id
    |> print_line ~lvl_delta_post:1;
    Utils.StringSet.iter (fun name ->
      Printf.sprintf "%s = %s;" (CodegenFormat.format_regname_next name) (CodegenFormat.format_regname_current name)
      |> print_line;
      Hashtbl.find reg_assigns name
      |> List.iter (fun ((e : EventGraph.event), (lval_info : EventGraph.lvalue_info), (td : EventGraph.lowering_data)) ->
        let (le, len) = lval_info.lval_range.subreg_range_interval in
        let w = Option.get td.w in
        Printf.sprintf "if (%s) %s[%s +: %d] = %s;"
          (EventStateFormatter.format_current g.thread_id e.id)
          (CodegenFormat.format_regname_next name)
          (MaybeConst.map (fun (td : EventGraph.lowering_data) -> Option.get td.w) le |> CodegenFormat.format_wire_maybe_const)
          len
          (CodegenFormat.format_wirename w.thread_id w.id)
        |> print_line
      )
    ) multi_writer;
    print_line ~lvl_delta_pre:(-1) "end"
  )

let codegen_actions printer (g : EventGraph.event_graph) (multi_writer : Utils.StringSet.t) =
  let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) =
    CodegenPrinter.print_line printer ~lvl_delta_pre:lvl_delta_pre ~lvl_delta_post:lvl_delta_post in
  let open EventGraph in
  (* True iff the action emits a line below; PutShared/Immediate* never do, and a multi-writer RegAssign is handled by codegen_reg_next_state instead. *)
  let action_prints_line (a : action Lang.ast_node) =
    match a.d with
    | DebugPrint _ | DebugFinish -> true
    | RegAssign (lval_info, _) -> not (Utils.StringSet.mem lval_info.lval_range.subreg_name multi_writer)
    | PutShared _ | ImmediateRecv _ | ImmediateSend _ -> false
  in
  let print_event_actions (e : event) =
    if List.exists action_prints_line e.actions then begin
      print_line @@ Printf.sprintf "// event %d actions" e.id;
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
          if Utils.StringSet.mem lval_info.lval_range.subreg_name multi_writer then ()
          else (
            let (le, len) = lval_info.lval_range.subreg_range_interval in
            let w = Option.get td.w in
            Printf.sprintf "%s[%s +: %d] <= %s;"
              (CodegenFormat.format_regname_current lval_info.lval_range.subreg_name)
              (MaybeConst.map (fun td -> Option.get td.w) le |> CodegenFormat.format_wire_maybe_const)
              len
              (CodegenFormat.format_wirename w.thread_id w.id)
              |> print_line
          )
        | PutShared _ -> ()
        | ImmediateRecv _ -> ()
        | ImmediateSend _ -> ()
      in
      List.iter print_action e.actions;
      print_line ~lvl_delta_pre:(-1) "end"
    end else ()
  in
  List.iter print_event_actions g.events


let codegen_shared_reg_transitions printer (pg : EventGraph.proc_graph) =
  let open EventGraph in
  let _, shared_regs = List.fold_left (fun (seen, shared) (g, _) ->
    let written = Utils.StringSet.of_list (GraphAnalysis.graph_owned_regs g) in
    (Utils.StringSet.union seen written,
     Utils.StringSet.union shared (Utils.StringSet.inter seen written))
  ) (Utils.StringSet.empty, Utils.StringSet.empty) pg.threads in
  if not (Utils.StringSet.is_empty shared_regs) then (
    let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) line =
      CodegenPrinter.print_line printer ~lvl_delta_pre ~lvl_delta_post line in
    let reset names = Utils.StringSet.iter (fun name ->
      print_line (Printf.sprintf "%s <= '0;" (CodegenFormat.format_regname_current name))
    ) names in
    CodegenPrinter.print_section printer "Registers written by multiple threads";
    print_line ~lvl_delta_post:1
      "always_ff @(posedge clk_i or negedge rst_ni) begin : _shared_reg_transition";
    print_line ~lvl_delta_post:1 "if (~rst_ni) begin";
    reset shared_regs;
    print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 "end else begin";
    List.iter (fun ((g : event_graph), reset_by) ->
      (* Keep all updates in one clocked block, including thread-local resets. *)
      let events = List.map (fun (e : event) ->
        { e with actions = List.filter (fun (a : action Lang.ast_node) ->
            match a.d with
            | RegAssign (lval, _) -> Utils.StringSet.mem lval.lval_range.subreg_name shared_regs
            | _ -> false) e.actions }
      ) g.events in
      codegen_actions printer { g with events } Utils.StringSet.empty;
      match reset_by with
      | None -> ()
      | Some (msg : Lang.message_specifier) ->
          let owned = Utils.StringSet.inter shared_regs
            (Utils.StringSet.of_list (GraphAnalysis.graph_owned_regs g)) in
          if not (Utils.StringSet.is_empty owned) then (
            let signal = CodegenFormat.format_msg_data_signal_name
              (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg 0 in
            print_line ~lvl_delta_post:1 (Printf.sprintf "if (%s) begin" signal);
            reset owned;
            print_line ~lvl_delta_pre:(-1) "end")
    ) pg.threads;
    print_line ~lvl_delta_pre:(-1) "end";
    print_line ~lvl_delta_pre:(-1) "end"
  );
  shared_regs

let codegen_transition shared_regs printer (config : Config.compile_config) (graphs : EventGraph.event_graph_collection)
                               (g : EventGraph.event_graph) (reset_by : Lang.message_specifier option) =
  let open EventGraph in
  let print_line ?(lvl_delta_pre = 0) ?(lvl_delta_post = 0) =
    CodegenPrinter.print_line printer ~lvl_delta_pre:lvl_delta_pre ~lvl_delta_post:lvl_delta_post in
  let reg_states = collect_reg_states config g in
  let start_state =
    Option.map (fun t -> EventStateFormatter.format_counter g.thread_id t ^ "_1") (delay_sharing config g).start_delay in
  let print_init v =
    if Option.is_none start_state then print_line @@ Printf.sprintf "_init_%d <= 1'b%d;" g.thread_id v in
  let reset_state sn =
    Printf.sprintf "%s_q <= %s;" sn (if Some sn = start_state then "1'b1" else "'0") in
  (* reset states *)

  let owned_regs = GraphAnalysis.graph_owned_regs g |> Utils.StringSet.of_list in
  let owned_regs = Utils.StringMap.filter (fun name _ ->
    Utils.StringSet.mem name owned_regs && not (Utils.StringSet.mem name shared_regs)) g.regs in

  (* Merge only applies when reset_by is None: reset_by re-resets registers later in the same always_ff, and reg_n doesn't account for that override yet. *)
  let reg_assigns = collect_reg_assigns g in
  let multi_writer =
    if config.merge_reg_writes && Option.is_none reset_by then
      Utils.StringSet.diff (multi_writer_reg_names reg_assigns) shared_regs
    else Utils.StringSet.empty
  in
  codegen_reg_next_state printer graphs g reg_assigns multi_writer;

  CodegenPrinter.print_section printer (Printf.sprintf "Thread %d state transition" g.thread_id);
  Printf.sprintf "always_ff @(posedge clk_i or negedge rst_ni) begin : _thread_%d_st_transition" g.thread_id |> print_line ~lvl_delta_post:1;
  print_line ~lvl_delta_post:1 "if (~rst_ni) begin";
  (* register reset *)
  print_init 1;
  Utils.StringMap.iter (
    fun _ (r : Lang.reg_def) ->
      let open CodegenFormat in
      Printf.sprintf "%s <= '0;" (format_regname_current r.name) |> print_line
  ) owned_regs;
  List.iter (fun (_, sn) -> reset_state sn |> print_line) reg_states;
  print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 "end else begin";
  (* actions *)
  codegen_actions printer g (Utils.StringSet.union multi_writer shared_regs);
  (
    match reset_by with
    | None -> ()
    | Some reset_by ->
      let reset_msg_signal = CodegenFormat.format_msg_data_signal_name
                            (CodegenFormat.canonicalize_endpoint_name reset_by.endpoint g)
                            reset_by.msg 0 in
      print_line ~lvl_delta_post:1 @@ Printf.sprintf "if (%s) begin" reset_msg_signal;
      print_init 1;
      Utils.StringMap.iter (
        fun _ (r : Lang.reg_def) ->
          let open CodegenFormat in
          Printf.sprintf "%s <= '0;" (format_regname_current r.name) |> print_line
      ) owned_regs;
      List.iter (fun (_, sn) -> reset_state sn |> print_line) reg_states;
          print_line ~lvl_delta_pre:(-1) ~lvl_delta_post:1 "end else begin"
  );
  print_init 0;
  (* next states *)
  List.iter (fun (_, sn) -> Printf.sprintf "%s_q <= %s_n;" sn sn |> print_line) reg_states;
  Utils.StringSet.iter (fun name ->
    Printf.sprintf "%s <= %s;" (CodegenFormat.format_regname_current name) (CodegenFormat.format_regname_next name) |> print_line
  ) multi_writer;
  if Option.is_some reset_by then print_line ~lvl_delta_pre:(-1) "end";
  print_line ~lvl_delta_pre:(-1) "end";
  print_line ~lvl_delta_pre:(-1) "end"

let codegen_sustained_actions (config : Config.compile_config) printer (graphs : EventGraph.event_graph_collection)
                                      (pg : EventGraph.proc_graph) (g : EventGraph.event_graph) =
  let print_line = CodegenPrinter.print_line printer in
  let send_or_assigns = Hashtbl.create 8 in
  let send_msg_defs = Hashtbl.create 8 in
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
  let resolve_mode = HandshakeResolve.resolver_for graphs pg in
  let mode_of (msg : Lang.message_specifier) =
    resolve_mode (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg in
  let open Lang in
  let print_send_recv (e : EventGraph.event) =
    let open EventGraph in
    let true_branch_attempt_condition () =
      let rec collect src extra_sources =
        match src with
        | `Root (Some (parent_event, br_side_info))
            when br_side_info.owner_branch.branch_cond = TrueFalse
                 && br_side_info.branch_side_sel = 0 ->
            Some
              (EventStateFormatter.format_current g.thread_id parent_event.id
               :: extra_sources)
        | `Recurse (src', trigger_event_id) ->
            collect src'
              (EventStateFormatter.format_current g.thread_id trigger_event_id
               :: extra_sources)
        | _ -> None
      in
      match collect e.source [] with
      | Some [only] -> Some only
      | Some sources -> Some (Printf.sprintf "(%s)" (String.concat " || " sources))
      | None -> None
    in
    let print_recv ?attempt_cond kind activated msg =
        let msg_def = lookup_msg_def msg |> Option.get in
        ignore kind;
        match CodegenPort.site_reverse_signal ~mode:(mode_of msg) msg_def with
        | Some CodegenPort.UsesReady ->
          insert_to recv_or_assigns
            (CodegenFormat.format_msg_ready_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
            true
            (Option.value attempt_cond ~default:activated)
        | Some CodegenPort.UsesAck ->
          insert_to recv_or_assigns
            (CodegenFormat.format_msg_ack_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
            true
            activated
        | None -> ()
    in
    let print_send ?attempt_cond kind activated msg td =
      let msg_def = lookup_msg_def msg |> Option.get in
      let uses_ack =
        CodegenPort.site_reverse_signal ~mode:(mode_of msg) msg_def = Some CodegenPort.UsesAck in
      ignore kind;
      let has_valid_port = CodegenPort.message_has_valid_port msg_def in
      (* The parent Choice drives valid for offer sends; reusing an ack-gated
         Select root here recreates a valid/ack combinational loop. *)
      let select_valid_ack_send =
        uses_ack
        && (match e.source with
            | `Select _ -> true
            | _ -> false)
      in
      let valid_cond =
        if select_valid_ack_send then
          None
        else if uses_ack then
          Some (Option.value attempt_cond ~default:activated)
        else
          Some activated
      in
      let data_cond =
        Option.value valid_cond ~default:activated
      in
      if Option.is_some td.w then
        (* Non-void message: has data wire *)
        let w = Option.get td.w in
        Hashtbl.replace send_msg_defs
          (CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          msg_def;
        insert_to send_or_assigns
          (CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          has_valid_port
          (
            valid_cond,
            data_cond,
            CodegenFormat.format_msg_data_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg 0,
            CodegenFormat.format_wirename w.thread_id w.id
          )
      else if Option.is_some valid_cond then
        (* Void message: no data wire, only valid signal *)
        insert_valid_only send_valid_only_assigns
          (CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
          has_valid_port
          (Option.get valid_cond)
    in

    List.iter (fun (sa : EventGraph.sustained_action Lang.ast_node) ->
      let (msg_def, kind) = match sa.d.ty with
        | Send (msg, _, k) -> (lookup_msg_def msg |> Option.get, k)
        | Recv (msg, k) -> (lookup_msg_def msg |> Option.get, k)
      in

      (* Protocol-specific signal assertion:
         - ValidAck Send: assert valid while waiting for ack (sustained)
         - ValidAck Recv: assert ack only when valid arrives (immediate)
         - ValidReady Send: assert valid only when ready arrives (immediate)
         - ValidReady Recv: assert ready while waiting for valid (sustained)
         An instantaneous op never waits, so its assertion is a single-cycle
         pulse rather than a sustained one. *)
      let sa_mode = (match sa.d.ty with
        | Send (msg, _, _) | Recv (msg, _) -> mode_of msg) in
      let use_sustained =
        CodegenPort.site_blocks ~mode:sa_mode msg_def kind &&
        (match sa.d.ty, CodegenPort.site_reverse_signal ~mode:sa_mode msg_def with
         | Send _, Some CodegenPort.UsesAck -> true
         | Recv (_, _), Some CodegenPort.UsesReady -> true
         | _ -> false)
      in

      let activated = 
        if use_sustained then
          Printf.sprintf "(%s || %s_q)"
            (EventStateFormatter.format_current g.thread_id e.id)
            (EventStateFormatter.format_syncstate g.thread_id sa.d.until.id)
        else if CodegenPort.site_blocks ~mode:sa_mode msg_def kind then
          EventStateFormatter.format_current g.thread_id sa.d.until.id
        else
          (* Instantaneous: fires in the cycle the event is reached. *)
          EventStateFormatter.format_current g.thread_id e.id
      in
      match sa.d.ty with
      | Send (msg, td, k) -> print_send k activated msg td
      | Recv (msg, k) -> print_recv k activated msg
    ) e.sustained_actions;

    let activated = (EventStateFormatter.format_current g.thread_id e.id) in
    let attempt_cond = true_branch_attempt_condition () in
    List.iter (fun (ac : EventGraph.action Lang.ast_node) ->
      match ac.d with
      | ImmediateSend (msg, td, k) -> print_send ?attempt_cond k activated msg td
      | ImmediateRecv (msg, k) -> print_recv ?attempt_cond k activated msg
      | _ -> ()
    ) e.actions;

    (* Handle Choice events: assert signals while waiting for handshake *)
    (* A retried choice is wrapped in a recursion; it is still the same choice. *)
    let rec choice_source = function
      | `Seq (p, `Choice (groups, kind, _)) -> Some (p, groups, kind)
      | `Recurse (src, _) -> choice_source src
      | _ -> None
    in
    match choice_source e.source with
    | Some (choice_parent, msg_groups, choice_kind) ->
      let msg_list = flatten_choice_msg_groups msg_groups in
      (* An instantaneous choice has no syncstate to sustain the assertion. *)
      let is_wildcard = is_wildcard_present msg_groups || choice_kind = Lang.Instant in
      let parent_current = EventStateFormatter.format_current g.thread_id choice_parent.id in
      let activated =
        if not is_wildcard then
          Printf.sprintf "(%s || %s_q)"
            parent_current
            (EventStateFormatter.format_syncstate g.thread_id e.id)
        else
          (* Fires on the first attempt and on every retry. *)
          EventStateFormatter.format_current g.thread_id e.id
      in
        List.iter (fun (msg : Lang.message_specifier) ->
          if msg.endpoint <> "*" || msg.msg <> "*" then
            let msg_def = lookup_msg_def msg |> Option.get in
            match msg_def.dir with
            | Out ->
              (* Output message (Send): assert valid only for ValidAck protocol *)
              if CodegenPort.message_has_ack_port ~mode:(mode_of msg) msg_def then
                insert_to choice_valid_asserts
                  (CodegenFormat.format_msg_valid_signal_name 
                    (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg)
                  true
                  activated
            | Inp ->
              (* Input message (Recv): assert ready only for ValidReady protocol *)
              if CodegenPort.message_has_ready_port ~mode:(mode_of msg) msg_def then
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
  if Hashtbl.length recv_or_assigns > 0
     || Hashtbl.length send_or_assigns > 0
     || Hashtbl.length choice_valid_asserts > 0
     || Hashtbl.length send_valid_only_assigns > 0 then
    CodegenPrinter.print_section printer (Printf.sprintf "Thread %d handshake outputs" g.thread_id);
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      String.concat " || " !conds
      |> Printf.sprintf "assign %s = %s; // recv handshake" w_name
      |> print_line
    )
  ) recv_or_assigns;

  (* Merge Choice valid assertions into send_or_assigns *)
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      List.iter (fun cond ->
        insert_to send_or_assigns w_name true (Some cond, "", "", "")
      ) !conds
    )
  ) choice_valid_asserts;
  Hashtbl.iter (fun w_name (has_sync_port, conds) ->
    if has_sync_port then (
      String.concat " || " !conds
      |> Printf.sprintf "assign %s = %s; // send valid" w_name
      |> print_line
    )
  ) send_valid_only_assigns;

  let send_data_selectors = ref [] in
  Hashtbl.iter (fun w_name (has_sync_port, conds_dw) ->
    let valid_conditions =
      List.filter_map (fun (valid_cond, _, _, _) -> valid_cond) !conds_dw
    in
    if has_sync_port && valid_conditions <> [] then (
      valid_conditions
      |> String.concat " || "
      |> Printf.sprintf "assign %s = %s; // send valid" w_name
      |> print_line;
    );
    (* Filter out entries with empty data strings (from Choice assertions) *)
    let conds_with_data =
      List.filter_map (fun (_, data_cond, dw, vw) ->
        if dw <> "" && vw <> "" then Some (data_cond, dw, vw) else None
      ) !conds_dw
    in
    let n = List.length conds_with_data in
    (* At -O 3, when the data lives only in the handshake cycle and each
       site's own valid covers every cycle it is sent, the data can follow
       the active site without a stored selector. *)
    let sites_cover_valid =
      config.Config.opt_level >= 3
      && (match Hashtbl.find_opt send_msg_defs w_name with
          | Some (msg_def : Lang.message_def) ->
              List.for_all (fun (st : Lang.sig_type_chan_local) -> st.lifetime.e = `Cycles 1) msg_def.sig_types
          | None -> false)
      && List.for_all (fun (valid_cond, _, dw, _) -> Option.is_some valid_cond && dw <> "") !conds_dw
    in
    if n = 1 then (
      let (_, dw, vw) = List.hd conds_with_data in
      Printf.sprintf "assign %s = %s; // send data" dw vw
      |> print_line
    ) else if n > 1 && sites_cover_valid then (
      let (_, dw, _) = List.hd conds_with_data in
      List.map (fun (c, _, vw) -> Printf.sprintf "(%s ? %s : '0)" c vw) conds_with_data
      |> String.concat " | "
      |> Printf.sprintf "assign %s = %s; // send data of the active site" dw
      |> print_line
    ) else if n > 1 then (
      (* if we have more than one site that sends, keep track of which event is the last send (TODO: optimisation) *)
      let width = Utils.int_log2 n in
      send_data_selectors := (width, w_name, conds_with_data)::!send_data_selectors
    )
    (* if n = 0, no data signals to assign (all are Choice assertions) *)
  ) send_or_assigns;

  if !send_data_selectors <> [] then (
    List.iter (fun (width, name, conds_dw) ->
      Printf.sprintf "logic[%d:0] %s_selector_q, %s_selector_n; // send data selector for %s"
        (width - 1)
        name
        name
        name
      |> print_line;
      let (_, dw, _) = List.hd conds_dw in
      List.mapi (fun site_idx (_, _, vw) ->
        Printf.sprintf "(%s_selector_n == %d'd%d) ? %s : " name width site_idx vw
      ) conds_dw
      |> String.concat ""
      |> Printf.sprintf "assign %s = %s'0; // selected send data" dw
      |> print_line
    ) !send_data_selectors;

    Printf.sprintf "always_comb begin: _thread_%d_send_data_selector" g.thread_id
    |> CodegenPrinter.print_line ~lvl_delta_post:1 printer;
    List.iter (fun (width, name, conds) ->
      Printf.sprintf "%s_selector_n = %s_selector_q;" name name |> print_line;
      List.iteri (fun site_idx (c, _, _) ->
        Printf.sprintf "if (%s) %s_selector_n = %d'd%d;" c name width site_idx
          |> print_line
      ) conds;
    ) !send_data_selectors;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";

    Printf.sprintf "always_ff @(posedge clk_i or negedge rst_ni) begin : _thread_%d_send_data_selector_trans" g.thread_id
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

let codegen_states shared_regs printer
  (config : Config.compile_config)
  (graphs : EventGraph.event_graph_collection)
  (pg : EventGraph.proc_graph)
  (g : EventGraph.event_graph)
  (reset_by : Lang.message_specifier option) =
  if g.comb then(
    codegen_sustained_actions config printer graphs pg g
  ) else (
    codegen_decl config printer g;
    codegen_next config printer graphs pg g;
    codegen_sustained_actions config printer graphs pg g;
    codegen_transition shared_regs printer config graphs g reset_by
  )

let codegen_proc_states printer proc =
  let open EventGraph in
  let g = fst @@ List.hd proc.threads in

  let owned_regs = ref Utils.StringSet.empty in
  List.iter (
    fun (graph, _) ->
      owned_regs := GraphAnalysis.graph_owned_regs graph
                |> Utils.StringSet.of_list |> Utils.StringSet.union !owned_regs
  ) proc.threads;

  let process_regs =
    Utils.StringMap.filter (fun name _ -> Utils.StringSet.mem name !owned_regs |> not) g.regs
  in
  if not (Utils.StringMap.is_empty process_regs) then (
    CodegenPrinter.print_section printer "Process-level register reset";
    CodegenPrinter.print_line ~lvl_delta_post:1 printer
      "always_ff @(posedge clk_i or negedge rst_ni) begin : _proc_transition";
    CodegenPrinter.print_line ~lvl_delta_post:1 printer "if (~rst_ni) begin";
    Utils.StringMap.iter (
      fun _ (r : Lang.reg_def) ->
        let open CodegenFormat in
        Printf.sprintf "%s <= '0;" (format_regname_current r.name)
          |> CodegenPrinter.print_line printer
    ) process_regs;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end";
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
  )
