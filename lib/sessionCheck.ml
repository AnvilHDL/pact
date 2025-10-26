open Lang
open EventGraph


module IntHashtbl = Hashtbl.Make(Int)

(** Extract atomic actions from an event's actions and sustained actions *)
let extract_atomic_actions (ev : event) (default_span : Lang.code_span) : (Lang.atomic_action_with_gap * Lang.code_span) list =
  let extract_from_action (a_span : action Lang.ast_node) : (Lang.atomic_action_with_gap * Lang.code_span) option =
    match a_span.d with
    | ImmediateSend (msg, _) -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), a_span.span)
    | ImmediateRecv msg -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), a_span.span)
    | _ -> None
  in
  let extract_from_sustained (sa_span : sustained_action Lang.ast_node) : (Lang.atomic_action_with_gap * Lang.code_span) option =
    match sa_span.d.ty with
    | Send (msg, _) -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), sa_span.span)
    | Recv msg -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), sa_span.span)
  in
  let immediate_actions = List.filter_map extract_from_action ev.actions in
  let sustained_actions = List.filter_map extract_from_sustained ev.sustained_actions in

  let out_acts = List.map (fun ev -> ev.source) ev.outs in

  let delay_actions = List.filter_map (fun (src : event_source) ->
    match src with
    | `Seq (_, `Cycles n) -> Some (Lang.AtomDelay n, default_span)
    | _ -> None
  ) out_acts in
  
  delay_actions @ immediate_actions @ sustained_actions

let equivalence_of_action (a1 : Lang.atomic_action_with_gap) (a2 : Lang.atomic_action_with_gap) : (bool * (int option)) =
  match (a1, a2) with
  | (Lang.AtomicAct act1, Lang.AtomicAct act2) ->
      (match (act1, act2) with
      | (Lang.AtomBMsg msg1, Lang.AtomBMsg msg2) ->
          msg1.endpoint = msg2.endpoint && msg1.msg = msg2.msg, None
      | (Lang.AtomBMsg msg1, Lang.AtomNBMsg msg2) ->
          msg1.endpoint = msg2.endpoint && msg1.msg = msg2.msg, None
      | (Lang.AtomNBMsg msg1, Lang.AtomNBMsg msg2) ->
          msg1.endpoint = msg2.endpoint && msg1.msg = msg2.msg, None
      | _ -> (false, None)
      )
  | (Lang.AtomDelay n1, Lang.AtomDelay n2) ->
      n1 <= n2, if n1 < n2 then Some (n2 - n1) else None
  | _ -> (false, None)


(** Check if event satisfies atomic action *)
let event_satisfies_atomic (ev : event) (atom : Lang.atomic_action_with_gap) (verbose : bool) (default_span : code_span): (bool * Lang.code_span option * int option) =
  let actions = extract_atomic_actions ev default_span in
  let debug_action_list = List.map (fun (a, _) -> Lang.string_of_atomic_action_with_gap a) actions in
if verbose then Printf.eprintf "Checking event %d for atomic action %s | present actions: %s\n" ev.id (Lang.string_of_atomic_action_with_gap atom) (String.concat ", " debug_action_list); 

  match List.find_opt (fun (a, _) -> fst (equivalence_of_action a atom)) actions with
  | Some (a, span) -> (true, Some span, snd (equivalence_of_action a atom))
  | None -> (false, None, None)

(** Check if event has any communication action that conflicts with expected action *)
let event_has_wrong_action (ev : event) (expected : Lang.atomic_action_with_gap) (default_span : code_span) : (Lang.atomic_action_with_gap * Lang.code_span) option =
  let actions = extract_atomic_actions ev default_span in
  let satisfy_act = List.find_opt (fun (a, _) -> fst (equivalence_of_action a expected)) actions in
  match satisfy_act with
  | Some _ -> None
  | None ->
      let conflicting_act = List.find_opt (fun (a, _) -> not (fst (equivalence_of_action a expected))) actions in
      match conflicting_act with
      | Some (act, span) -> Some (act, span)
      | None -> None

(** Advance session type based on event actions, returning (updated_type, error_opt) *)
let rec session_judgement (st : Lang.session_type ast_node) (ev : event) (config : Config.compile_config) (default_span : Lang.code_span)
    : (Lang.session_type option * (string * Lang.code_span) option) =
  let sty = st.d in
  match sty with
  | Lang.StyAtom (Lang.AtomicAct atom) ->
      let (satisfied, _span, _) = event_satisfies_atomic ev (Lang.AtomicAct atom) config.verbose default_span in
      if satisfied then
        (None, None) (* Session completed *)
      else (
        (* Check if there's a wrong action *)
        match event_has_wrong_action ev (Lang.AtomicAct atom) default_span with
        | Some (wrong_act, span) ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but found '%s'"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom))
              (Lang.string_of_atomic_action_with_gap wrong_act) in
            (Some sty, Some (err_msg, span))
        | None ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but no matching action found"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom)) in
            (Some sty, Some (err_msg, default_span))
            
      )
  
  | Lang.StyAtom (Lang.AtomDelay n) ->
    let satisfied, code_span, slack_opt = event_satisfies_atomic ev (Lang.AtomDelay n) config.verbose default_span in
    let code_span  = match code_span with
      | Some span -> span
      | None -> Lang.code_span_dummy in
    if satisfied then(
        if Option.is_some slack_opt then (
          let slack = Option.get slack_opt in
          Some (Lang.StyAtom (Lang.AtomDelay slack)), None
        )
        else None, None
    )
      else (
        let err_msg = Printf.sprintf "Session type mismatch: expected delay of at least %d cycles" n in
        (Some sty, Some (err_msg, code_span)) (* No delay satisfied, error *)
      )
  | Lang.StySeq (s1, s2) ->
      let (s1_res, err1) = session_judgement {st with d = s1} ev config default_span in
      (match err1 with
      | Some _ -> (Some sty, err1) (* Propagate error *)
      | None ->
          match s1_res with
          | None -> (Some s2, None) (* First part complete, continue with second *)
          | Some s1' -> (Some (Lang.StySeq (s1', s2)), None) (* First part still ongoing *)
      )
  
  | Lang.StyChoice (s1, s2) ->
      (* Internal choice: try both branches *)
      let (s1_res, err1) = session_judgement {st with d = s1} ev config default_span in
      let (s2_res, err2) = session_judgement {st with d = s2} ev config default_span in
      (match s1_res, s2_res with
      | None, _ -> (None, None) (* Chose s1 and completed *)
      | _, None -> (None, None) (* Chose s2 and completed *)
      | Some s1', Some s2' ->
          (* Neither satisfied yet - only error if BOTH have errors *)
          (match err1, err2 with
          | Some e1, Some _e2 -> (Some sty, Some e1) (* Both failed, report first error *)
          | _ -> (Some (Lang.StyChoice (s1', s2')), None)
          )
      )
  
  | Lang.StyParallel (s1, s2) ->
      (* Both branches must be satisfied (possibly at different events) *)
      let (s1_res, err1) = session_judgement {st with d = s1} ev config default_span in
      let (s2_res, err2) = session_judgement {st with d = s2} ev config default_span in
      (match err1, err2 with
      | Some e, _ | _, Some e -> (Some sty, Some e) (* Propagate any error *)
      | None, None ->
          match s1_res, s2_res with
          | None, None -> (None, None) (* Both completed *)
          | Some s1', None -> (Some s1', None) (* s2 done, s1 continues *)
          | None, Some s2' -> (Some s2', None) (* s1 done, s2 continues *)
          | Some s1', Some s2' -> (Some (Lang.StyParallel (s1', s2')), None)
      )
  
  | Lang.StyFuture s ->
      (* Future: session can be satisfied at any later point, so don't error yet *)
      let (s_res, _err) = session_judgement {st with d = s} ev config default_span in
      (match s_res with
      | None -> (None, None) (* Future satisfied *)
      | Some s' -> (Some (Lang.StyFuture s'), None) (* Keep waiting *)
      )
  
  | Lang.StyChoiceDual offerings ->
    if List.length offerings < 2 then 
                  raise (Except.TypeError [Text (Printf.sprintf "Not well formed choice dual session type | No of offerings = %d" (List.length offerings)); Except.codespan_local default_span]);
    (* get the message list from the event outbound edges *)
    if config.verbose then
      Printf.eprintf "Checking event %d for dual choice with offerings: %s\n" ev.id (String.concat ", " (List.map (fun (o:offering_session_type) -> match o.trigger with
        | Lang.AtomBMsg m -> Printf.sprintf "BMsg(%s, %s)" m.endpoint m.msg
        | Lang.AtomNBMsg m -> Printf.sprintf "NBMsg(%s, %s)" m.endpoint m.msg
      ) offerings));
      let msg_list = List.find_map (fun (e : event) ->
            match e.source with `Seq ( _ , `Choice msg_list) -> Some msg_list
            | _ -> None
          ) ev.outs in
          let msg_list = if Option.is_none msg_list then let err_msg = Printf.sprintf "Session type mismatch at event %d: expected choice messages but none found from event outbound edges event ids of outbounds = %s" ev.id (String.concat ", " (List.map string_of_int (List.map (fun e -> e.id) ev.outs))) in
            raise (Except.TypeError [Text err_msg; Except.codespan_local default_span])
          else Option.get msg_list in


          let msg_list_offering = List.map (fun (o : offering_session_type) -> 
            match o.trigger with
            | Lang.AtomBMsg msg -> msg
            | Lang.AtomNBMsg msg -> msg
          ) offerings in
          if List.exists (fun m -> List.exists (fun expected_m -> m.endpoint = expected_m.endpoint && m.msg = expected_m.msg) msg_list_offering) msg_list then
            
          let rec build_choice_from_offerings (offerings : offering_session_type list) =
            if List.length offerings = 1 then
              let only = List.hd offerings in
              match only.continuation with
              | Some sty -> Lang.StySeq(
                  Lang.StyAtom (Lang.AtomicAct (only.trigger)),
                  sty
                )
              | None -> Lang.StyAtom (Lang.AtomicAct (only.trigger))
            else
                let first = List.hd offerings in
                  let rest = List.tl offerings in
                  Lang.StyChoice(
                    (match first.continuation with
                    | Some sty -> Lang.StySeq(
                      Lang.StyAtom (Lang.AtomicAct (first.trigger)),
                      sty
                    )
                    | None -> Lang.StyAtom (Lang.AtomicAct (first.trigger)))
                    ,
                    build_choice_from_offerings rest
                  )
              in
              let new_sty = build_choice_from_offerings offerings  in
              (Some new_sty, None)
          else
          (
            let err_msg = "Session type mismatch: none of the offered messages match the expected choices" in
            (Some sty, Some (err_msg, default_span))
          )
            (* create choice session type from the offerings *)

      


(** Check session type conformance for entire event graph *)
let check_session (config : Config.compile_config) (g : event_graph) module_name =
  let last_node_id = (List.length g.events) - 1 in

  
  if config.verbose then (
  Printf.eprintf "\n[Session Type Check] Starting session type  ....\n";
  Printf.eprintf "Checking graph with %d events...\n" (List.length g.events);
  EventGraphOps.print_graph g;
  );
  match g.interface_protocol with
  (* dont check at last node *)
  | None -> () (* No session type to check *)
  | Some protocol_node ->
      if config.verbose then
        Printf.eprintf "\n[Session Type Check] Checking protocol: %s\n" 
          (Lang.string_of_protocol protocol_node.Lang.d);
      
      GraphAnalysis.events_prepare_outs g.events;
      
      let bfs_queue = Queue.create () in
      let visited = IntHashtbl.create (List.length g.events) in
      

      let session_states = IntHashtbl.create (List.length g.events) in
      
      let explore_graph start_ev initial_sty  =
        Queue.add (start_ev, initial_sty) bfs_queue;
        IntHashtbl.add visited start_ev.id true;
        IntHashtbl.add session_states start_ev.id initial_sty;
        
        while not (Queue.is_empty bfs_queue) do
          let (ev, current_sty) = Queue.pop bfs_queue in
          (* Update event's session type *)
          if ev.id = last_node_id then
            ()
          else (
            ev.session_type <- Some {protocol_node with Lang.d = current_sty};
            
            (* Compute next session type based on this event's actions *)

            (* for branch continue to next one by taking the session type as it is *)
            let check_is_branch_event (ev : event) : bool =
              List.exists (fun src ->
                match src.source with
                | `Root(Some (_)) -> true
                | `Branch (_, _) -> true
                | _ -> false
              ) ev.outs
            in
            let (next_sty_opt, error_opt) = if check_is_branch_event ev then Some current_sty, None
            else  session_judgement {protocol_node with Lang.d = current_sty} ev config g.thread_codespan 
          in
            
            (* Check for errors *)
            (match error_opt with
            | Some (err_msg, err_span) ->
                raise (Except.TypeError [
                  Text "Session type violation: ";
                  Text err_msg;
                  Except.codespan_local err_span
                ])
            | None -> ()
            );
            (* Update event's session type *)
            (* Handle branching: for internal choice and parallel, branches may have different session states *)
            (match ev.source with
            | `Branch (_, branch_info) ->
                (* Branch event: distribute session type to all branches *)
                List.iter (fun branch_ev ->
                  if not (IntHashtbl.mem visited branch_ev.id) then (
                    let branch_sty = match next_sty_opt with
                    | None -> protocol_node.Lang.d (* Completed, restart or no more *)
                    | Some s -> s
                    in
                    IntHashtbl.add visited branch_ev.id true;
                    IntHashtbl.add session_states branch_ev.id branch_sty;
                    Queue.add (branch_ev, branch_sty) bfs_queue
                  )
                ) branch_info.branches_to
            | _ ->
                (* Normal event: propagate to successors *)
                List.iter (fun succ_ev ->
                  if not (IntHashtbl.mem visited succ_ev.id) then (
                    let succ_sty = match next_sty_opt with
                    | None -> 
                        (* Session completed - restart with original protocol for loop *)
                        if config.verbose then
                          Printf.eprintf "Session type completed at event %d, restarting protocol for event %d\n" ev.id succ_ev.id;
                        protocol_node.Lang.d
                    | Some s -> s
                    in
                    IntHashtbl.add visited succ_ev.id true;
                    IntHashtbl.add session_states succ_ev.id succ_sty;
                    Queue.add (succ_ev, succ_sty) bfs_queue
                  )
                ) ev.outs
            )
          )
        done;
        
        (* Verify that all events were visited and session is complete or consistent *)
        List.iter (fun ev ->
          if not (IntHashtbl.mem visited ev.id) && ev.id <> last_node_id then
            Printf.eprintf "[Warning]: Event %d was not reachable during session type check\n" ev.id
        ) g.events;
        
        (* Check if final session type is satisfied at loop end *)
        let last_ev = List.find (fun e -> e.is_recurse) g.events in
        let final_sty = IntHashtbl.find_opt session_states last_ev.id in
        (match final_sty with
        | Some sty when sty <> protocol_node.Lang.d ->
            if config.verbose then
              raise (Except.TypeError [
                Text (Printf.sprintf "Session type not fully completed at loop end: %s" (Lang.string_of_protocol sty));
                Except.codespan_local g.thread_codespan
              ])
        | _ -> ()
        )
      in
      
      let root_ev = List.find (fun e -> e.source = `Root None) g.events in
      explore_graph root_ev protocol_node.Lang.d ;
      if config.verbose then
        Printf.eprintf "[Session Type Check] Session type check completed successfully.\n";

        let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph.dot" module_name) in
      EventGraphOps.print_graph_with_session_types g file_handler;
      Out_channel.close file_handler