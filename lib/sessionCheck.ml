open Lang
open EventGraph


module IntHashtbl = Hashtbl.Make(Int)


let get_event_id_for_atomic_action (ev : event) (g : event_graph) (atom : Lang.atomic_action_with_gap) : int=
  let atom_delay = match atom with
    | Lang.AtomicAct (Lang.AtomBMsg msg) -> Some msg
    | Lang.AtomicAct (Lang.AtomNBMsg msg) -> Some msg
    | _ -> None
  in
  if match atom with | Lang.AtomDelay _-> true | _ -> false then (
    let id = List.find_map (fun e ->
      match e.source with
      | `Seq (_, `Cycles _) -> Some e.id
      | _ -> None
    ) ev.outs in
    if Option.is_none id then
      raise (Except.TypeError [Text (Printf.sprintf "No event found for atomic action %s" (Lang.string_of_atomic_action_with_gap atom)); Except.codespan_local g.thread_codespan])
    else
      Option.get id
  )
    else (
      let atom_delay = Option.get atom_delay in
      let ids = List.find_map (fun e ->
        match e.source with
        | `Seq (_, `Send msg) when atom_delay.endpoint = msg.endpoint && atom_delay.msg = msg.msg -> Some e.id
        | `Seq (_, `Recv msg) when atom_delay.endpoint = msg.endpoint && atom_delay.msg = msg.msg -> Some e.id
        | _ -> None
      ) ev.outs in
      if Option.is_none ids then
        raise (Except.TypeError [Text (Printf.sprintf "No event found for atomic action %s" (Lang.string_of_atomic_action_with_gap atom)); Except.codespan_local g.thread_codespan])
      else
        Option.get ids
    )

let update_sty (graph : event_graph) (ev_id : int) (new_sty : Lang.session_type) (default_span : code_span) (verbose : bool) =
  if ev_id < 0 then ()
  else
    let ev_opt = List.find_opt (fun e -> e.id = ev_id) graph.events in
    if Option.is_none ev_opt then
      raise (Except.TypeError [Text (Printf.sprintf "Event with id %d not found in graph during session type update" ev_id); Except.codespan_local graph.thread_codespan])
    else
      let ev = Option.get ev_opt in
    
      if verbose then Printf.eprintf "Updating event %d session type to %s\n" ev.id (Lang.string_of_protocol new_sty);
   
    ev.session_type <- Some {d= new_sty; span = default_span}

let update_sty_seq (graph : event_graph) (ev_id : int) (new_sty : Lang.session_type) (default_span : code_span) (verbose : bool)=
  if ev_id < 0 then ()
  else
    let ev_opt = List.find_opt (fun e -> e.id = ev_id) graph.events in
    if Option.is_none ev_opt then
      raise (Except.TypeError [Text (Printf.sprintf "Event with id %d not found in graph during session type update" ev_id); Except.codespan_local graph.thread_codespan])
    else
      let ev = Option.get ev_opt in
      (* Printf.eprintf "Updating event %d session type to %s\n" ev.id (Lang.string_of_protocol new_sty); *)
      if Option.is_none ev.session_type then
          ev.session_type <- Some {d= new_sty; span = default_span}
      else
        let existing_sty = Option.get ev.session_type in
          if verbose then Printf.eprintf "Updating event %d session type (%s) by sequencing with %s \n" ev_id (Lang.string_of_protocol existing_sty.d) (Lang.string_of_protocol new_sty);
        ev.session_type <- Some {d = Lang.StySeq (existing_sty.d, new_sty); span = default_span}

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
let event_satisfies_atomic (ev : event) (atom : Lang.atomic_action_with_gap) (verbose : bool) (default_span : code_span): (bool * Lang.code_span option * int option ) =
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

(** Advance session type based on event actions, returning (continuation_opt, error_opt) *)
let rec session_judgement (st : Lang.session_type ast_node) (ev : event) (config : Config.compile_config) (default_span : Lang.code_span) (graph : event_graph)
    : (int*Lang.session_type option * (string * Lang.code_span) option) =
(* 
  if config.verbose then
    Printf.eprintf "Session judgement at event %d with session type: %s\n" ev.id (Lang.string_of_protocol st.d); *)
  let sty = st.d in
  match sty with
  | Lang.StyAtom (Lang.AtomicAct atom) ->
      let (satisfied, _span, _) = event_satisfies_atomic ev (Lang.AtomicAct atom) config.verbose default_span in
      if satisfied then (
        let id = get_event_id_for_atomic_action ev graph (Lang.AtomicAct atom) in
        (* update_sty graph id st.d default_span; *)
        (id,None, None) (* Session completed *)
      ) else (
        (* Check if there's a wrong action *)
        match event_has_wrong_action ev (Lang.AtomicAct atom) default_span with
        | Some (wrong_act, span) ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but found '%s'"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom))
              (Lang.string_of_atomic_action_with_gap wrong_act) in
            (-1,Some sty, Some (err_msg, span))
        | None ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but no matching action found"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom)) in
            (-1,Some sty, Some (err_msg, default_span))
      )
  
  | Lang.StyAtom (Lang.AtomDelay n) ->
      let satisfied, code_span, slack_opt = event_satisfies_atomic ev (Lang.AtomDelay n) config.verbose default_span in
      let code_span  = match code_span with
        | Some span -> span
        | None -> Lang.code_span_dummy in
      if satisfied then(
        let evid = get_event_id_for_atomic_action ev graph (Lang.AtomDelay n) in
        if Option.is_some slack_opt then (
          let slack = Option.get slack_opt in
          (* update_sty graph evid (Lang.StyAtom (Lang.AtomDelay slack)) default_span; *)
          (evid, Some (Lang.StyAtom (Lang.AtomDelay slack)), None)
        )
        else (
          (* update_sty graph evid st.d default_span; *)
          (evid,None, None)
        )
      )
      else (
        let err_msg = Printf.sprintf "Session type mismatch: expected delay of at least %d cycles" n in
        (-1,Some sty, Some (err_msg, code_span))
      )
  | Lang.StyTrue ->
      (* True session type is always satisfied *)
      raise (Except.TypeError [Text "Unexpected true session type during session judgement"; Except.codespan_local default_span])
  | Lang.StySeq (s1, s2) ->
   if config.verbose then Printf.eprintf "Checking sequence session type at event %d | s_1 = %s | s_2 = %s\n" ev.id (Lang.string_of_protocol s1) (Lang.string_of_protocol s2);
      let (id, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      (match err1 with
      | Some _ -> 
          (* s1 failed - this is an error *)
          (-1, Some sty, err1)
      | None ->
          (match s1_cont with
          | None ->
              (* s1 completed, propagate s2 to successors *)
              if id < 0 then
                List.iter (fun succ_ev ->
                  update_sty_seq graph succ_ev.id s2 default_span config.verbose
                ) ev.outs
              else update_sty graph id s2 default_span config.verbose;

              (id,Some s2, None)
          | Some s1' ->
              (* s1 partially completed, propagate seq(s1', s2) *)
              Printf.eprintf "Sequence continuation at event %d: s1' = %s, s2 = %s\n" ev.id (Lang.string_of_protocol s1') (Lang.string_of_protocol s2);
              let remaining = Lang.StySeq (s1', s2) in
              if id < 0 then
              List.iter (fun succ_ev ->
                update_sty_seq graph succ_ev.id remaining default_span config.verbose
              ) ev.outs
              else
              update_sty graph id remaining default_span config.verbose;

              
              (* List.iter (fun succ_ev ->
                update_sty graph succ_ev.id remaining default_span
              ) ev.outs; *)
              (id, Some remaining, None)
          )
      )
  | Lang.StyChoice (s1, s2) ->
      (* Internal choice: try both branches *)
      let (id1, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      let (id2, s2_cont, err2) = session_judgement {st with d = s2} ev config default_span graph in
      (
        match err1, err2 with
        | None, None ->
        (
          match s1_cont, s2_cont with
          | None, None ->
              (* Both satisfied *)
              (-1, None, None)
          | Some s1', None ->
              (id1, Some s1', None)
          | None, Some s2' ->
              (id2, Some s2', None)
          | Some s1', Some s2' ->
            let remaining = Lang.StyChoice (s1', s2') in
            if id1 != id2 then 
              let err_msg = "Session type mismatch in choice: different events for continuations" in
              (-1, Some sty, Some (err_msg, default_span))
            else
            (id1, Some remaining, None)
      )

        | Some _ , None ->
            (* s2 satisfied *)
            (match s2_cont with
            | None ->
                (* List.iter (fun succ_ev ->
                  update_sty graph succ_ev.id s1 default_span
                ) ev.outs; *)
                (id2, None, None)
            | Some s2' ->
                (* let remaining = Lang.StyChoice (s1, s2') in *)
                update_sty graph id2 s2' default_span config.verbose;
                (* List.iter (fun succ_ev ->
                  update_sty graph succ_ev.id remaining default_span
                ) ev.outs; *)
                (id2,Some s2', None)
            )
        | None, Some _ ->
            (* s1 satisfied *)
            (match s1_cont with
            | None ->
                (* List.iter (fun succ_ev ->
                  update_sty graph succ_ev.id s2 default_span
                ) ev.outs; *)
                (id1, None, None)
            | Some s1' ->
                (* let remaining = Lang.StyChoice (s1', s2) in *)
                (* List.iter (fun succ_ev ->
                  update_sty graph succ_ev.id remaining default_span
                ) ev.outs; *)
                 update_sty graph id1 s1' default_span config.verbose;
                (id1, Some s1', None)
            )
        | Some e1, Some e2 ->
            (-1, Some sty, Some (if Option.is_some err1 then e1 else e2))
      )
  
  | Lang.StyParallel (s1, s2) ->
      (* Both branches must be satisfied (possibly at different events) *)
      let (id1, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      let (id2, s2_cont, err2) = session_judgement {st with d = s2} ev config default_span graph in
      (match err1, err2 with
      | None, None ->
          (match s1_cont, s2_cont with
          | None, None ->
              (-1,None, None)
          | None, Some s2' ->
               update_sty graph id2 s2' default_span config.verbose;
              (id2,Some s2', None)
          | Some s1', None ->
              update_sty graph id1 s1' default_span config.verbose  ;
              (id1,Some s1', None)
          | Some s1', Some s2' ->
              update_sty graph id1 s1' default_span config.verbose;
              update_sty graph id2 s2' default_span config.verbose;
              let ev_id = List.find_map (fun e ->
                match e.source with
                | `Later (id_a, id_b) when (id_a.id = id1 && id_b.id = id2) || (id_a.id = id2 && id_b.id = id1) -> Some e.id
                | _ -> None
              ) ev.outs in
              let ev_id = Option.value ev_id ~default:(-1) in
              (ev_id, None, None)
          )
        | _ , _ ->
            let err_msg = "Session type mismatch in parallel composition" in
            (-1, Some sty, Some (err_msg, default_span))
      )
  
  | Lang.StyFuture s ->
    let actions = extract_atomic_actions ev default_span in
      let delay_act = match List.find_opt (fun (a, _) -> match a with
        | Lang.AtomDelay _ -> true
        | _ -> false
      ) actions with
        | Some (a, span) -> Some (a, span)
        | None -> None
      in

      if Option.is_some delay_act && List.length actions == 1 then
        (-1, Some (Lang.StyFuture s), None)
      else            
      let (_id, s_cont, err) = session_judgement {st with d = s} ev config default_span graph in
      if Option.is_some err then
        (-1, Some sty, err)
      else
      (match s_cont with
      | None -> (-1, None, None) (* Future satisfied *)
      | Some s' ->
          (* let remaining = s' in *)
          (* List.iter (fun succ_ev ->
            update_sty graph succ_ev.id remaining default_span
          ) ev.outs; *)
          (* update_sty graph _id s' default_span; *)
          (_id, Some s', None)
      )
  | Lang.StyOffer offerings ->
      (* External choice: match offered messages with event outbound edges *)
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
        if Option.is_none msg_list then 
          (
        let err_msg = Printf.sprintf "Session type mismatch at event %d: expected choice messages but none found from event outbound edges event ids of outbounds = %s" ev.id (String.concat ", " (List.map string_of_int (List.map (fun e -> e.id) ev.outs))) in
        (-1, Some sty, Some (err_msg, default_span))
      )
      else 
      (
        let msg_list = Option.get msg_list in

      let msg_list_offering = List.map (fun (o : offering_session_type) -> 
        match o.trigger with
        | Lang.AtomBMsg msg -> msg
        | Lang.AtomNBMsg msg -> msg
      ) offerings in
      if List.exists (fun m -> List.exists (fun expected_m -> m.endpoint = expected_m.endpoint && m.msg = expected_m.msg) msg_list_offering) msg_list then (
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
        let new_sty = build_choice_from_offerings offerings in
        let evid = List.find_map (fun e ->
          match e.source with
          | `Seq (_, `Choice msg_list_ev) ->
              if List.exists (fun m -> List.exists (fun expected_m -> m.endpoint = expected_m.endpoint && m.msg = expected_m.msg) msg_list_offering) msg_list_ev then
                Some e.id
              else None
          | _ -> None
        ) ev.outs in
        let evid = Option.value evid ~default:(-1) in
        (* update_sty graph evid new_sty default_span; *)
        (evid, Some new_sty, None)
      ) else
        (
          let err_msg = "Session type mismatch: none of the offered messages match the expected choices" in
          (-1, Some sty, Some (err_msg, default_span))
        )
      )
  | Lang.StyXOffer offerings ->
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
        if Option.is_none msg_list then 
          (
        let err_msg = Printf.sprintf "Session type mismatch at event %d: expected choice messages but none found from event outbound edges event ids of outbounds = %s" ev.id (String.concat ", " (List.map string_of_int (List.map (fun e -> e.id) ev.outs))) in
        (-1, Some sty, Some (err_msg, default_span))
      )
      else 
      (
        let msg_list = Option.get msg_list in

      let msg_list_offering = List.map (fun (o : offering_session_type) -> 
        match o.trigger with
        | Lang.AtomBMsg msg -> msg
        | Lang.AtomNBMsg msg -> msg
      ) offerings in
      if List.exists (fun m -> List.exists (fun expected_m -> m.endpoint = expected_m.endpoint && m.msg = expected_m.msg) msg_list_offering) msg_list then (
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
        let new_sty = build_choice_from_offerings offerings in
        let evid = List.find_map (fun e ->
          match e.source with
          | `Seq (_, `Choice msg_list_ev) ->
              if List.exists (fun m -> List.exists (fun expected_m -> m.endpoint = expected_m.endpoint && m.msg = expected_m.msg) msg_list_offering) msg_list_ev then
                Some e.id
              else None
          | _ -> None
        ) ev.outs in
        let evid = Option.value evid ~default:(-1) in
        (* update_sty graph evid new_sty default_span; *)
        (evid, Some new_sty, None)
      ) else
        (
          let err_msg = "Session type mismatch: none of the offered messages match the expected choices" in
          (-1, Some sty, Some (err_msg, default_span))
        )
      )


(** Check session type conformance for entire event graph *)
let check_session (config : Config.compile_config) (g : event_graph) module_name =
  let last_node_id = (List.length g.events) - 1 in

  
  if config.verbose then (
    Printf.eprintf "\n[Session Type Check] Starting session type  ....\n";
    Printf.eprintf "Checking graph with %d events...\n" (List.length g.events);
    let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph_before.dot" module_name) in
    EventGraphOps.print_dot_graph g file_handler;
    Out_channel.close file_handler;
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
      
      let explore_graph start_ev initial_sty  =
        Queue.add start_ev bfs_queue;
        IntHashtbl.add visited start_ev.id true;
        (* Set initial session type on start event *)
        start_ev.session_type <- Some {protocol_node with Lang.d = initial_sty};
        let is_empty_branch (e : event) : bool = 
            (
              let first_node = match e.source with
              | `Root (Some (__, _branch_side_info)) ->
                true
              | _ -> false
            in
            let last_node = List.exists (fun out_ev ->
              match out_ev.source with
              | `Branch (_, _) -> true
              | _ -> false
            ) e.outs in
            first_node && last_node
            )
        in
        
        while not (Queue.is_empty bfs_queue) do
          let ev = Queue.pop bfs_queue in
          
          if ev.id = last_node_id then
            ()
          else (
            (* Get current session type for this event *)
            let current_sty = match ev.session_type with
              | Some sty_node -> sty_node.d
              | None -> 
                  if config.verbose then
                    Printf.eprintf "Warning: Event %d has no session type, using initial\n" ev.id;
                  initial_sty
            in
            
            
            (* Check if this is a branch event - if so, just propagate type to successors *)
            let check_is_branch_event (ev : event) : bool =
              List.exists (fun src ->
                match src.source with
                | `Root(Some (_)) -> true
                | `Branch (_, _) -> true
                | `Later _ -> true
                | _ -> false
              ) ev.outs
            in
            
            
            if is_empty_branch ev then
              ()
            else if check_is_branch_event ev then (
              (* Branch event: just propagate current type to successors *)
              List.iter (fun succ_ev ->
                update_sty g succ_ev.id current_sty g.thread_codespan config.verbose
              ) ev.outs
            ) else (
              (* Run session judgement - it will update types internally *)
              let (_id, _continuation, error_opt) = session_judgement 
                {protocol_node with Lang.d = current_sty} 
                ev 
                config 
                g.thread_codespan 
                g 
              in
              
              (* Check for errors *)
              match error_opt with
              | Some (err_msg, err_span) ->
                  raise (Except.TypeError [
                    Text "Session type violation: ";
                    Text err_msg;
                    Except.codespan_local err_span
                  ])
              | None -> ()
            );

            
            (* Add unvisited successors to queue *)
            if is_empty_branch ev then
              ()
            else
            List.iter (fun succ_ev ->
              if not (IntHashtbl.mem visited succ_ev.id) then (
                IntHashtbl.add visited succ_ev.id true;
                Queue.add succ_ev bfs_queue
              )
            ) ev.outs
          )
        done;
        
        (* Verify that all events were visited *)
        List.iter (fun ev ->
          if not (IntHashtbl.mem visited ev.id) && ev.id <> last_node_id then
            Printf.eprintf "[Warning]: Event %d was not reachable during session type check\n" ev.id
        ) g.events;
        
        (* Check if final session type is satisfied at loop end *)
        let last_ev_opt = List.find_opt (fun e -> e.is_recurse) g.events in
        (match last_ev_opt with
        | Some last_ev ->
            let final_sty = last_ev.session_type in
            (match final_sty with
            | Some sty when sty.d <> protocol_node.Lang.d ->
                if config.verbose then
                  raise (Except.TypeError [
                    Text (Printf.sprintf "Session type not fully completed at loop end: %s" (Lang.string_of_protocol sty.d));
                    Except.codespan_local g.thread_codespan
                  ])
            | _ -> ()
            )
        | None -> ()
        )
      in
      
      let root_ev = List.find (fun e -> e.source = `Root None) g.events in
      explore_graph root_ev protocol_node.Lang.d ;
      if config.verbose then
        Printf.eprintf "[Session Type Check] Session type check completed successfully.\n";

      let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph.dot" module_name) in
      EventGraphOps.print_graph_with_session_types g file_handler;
      Out_channel.close file_handler