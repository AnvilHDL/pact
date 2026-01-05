open Lang
open EventGraph

module IntHashtbl = Hashtbl.Make(Int)


(* Replace session type variable with concrete session type in offerings *)
let substitute_session_type_in_session_type 
    (sty : session_type) 
    (id : string) 
    (sub_sty : session_type) 
    (default_span : code_span) : session_type =
  let aux (s : session_type) : session_type =
    match s with
    | StyXOffer offerings ->
        StyXOffer (List.map (fun o ->
          match o.trigger with
          | Lang.AtomTerminal styx ->
            (match styx with
             | StyVar vid when vid = id -> 
                 raise (Except.TypeError [
                   Text "Nested terminal substitution not supported"; 
                   Except.codespan_local default_span
                 ])
             | _ -> o)
          | _ -> o
        ) offerings)
    | StyOffer offerings ->
        StyOffer (List.map (fun o ->
          match o.trigger with
          | Lang.AtomTerminal styx ->
            (match styx with
             | StyVar vid when vid = id -> 
                 raise (Except.TypeError [
                   Text "Nested terminal substitution not supported"; 
                   Except.codespan_local default_span
                 ])
             | _ -> o)
          | _ -> o
        ) offerings)
    | StyVar vid when vid = id -> sub_sty
    | _ -> s
  in
  aux sty



(* Check if event is an empty branch (root to branch with no intermediate nodes) *)
let is_empty_branch (e : event) : bool = 
  let first_node = match e.source with
    | `Root (Some (__, _branch_side_info)) -> true
    | _ -> false
  in
  let last_node = List.exists (fun out_ev ->
    match out_ev.source with
    | `Branch (_, _) -> true
    | _ -> false
  ) e.outs in
  first_node && last_node

(* Check if event is special empty branch (from choice with TrueFalse condition) *)
let is_empty_branch_special_one (e : event) : bool = 
  let first_node = match e.source with
    | `Root (Some (ev, _branch_side_info)) 
      when _branch_side_info.branch_side_sel = 1 
        && _branch_side_info.owner_branch.branch_cond = TrueFalse  
        && match ev.source with `Seq (_, `Choice _) -> true | _ -> false ->
      true
    | _ -> false
  in
  let last_node = List.exists (fun out_ev ->
    match out_ev.source with
    | `Branch (_, _) -> true
    | _ -> false
  ) e.outs in
  first_node && last_node

(* Check if event is a wildcard branch (from choice construct) *)
let is_wildcard_branch (e : event) : bool =
  let e_source = match e.source with
    | `Root (Some (_ev, _branch_side_info)) -> Some _ev
    | _ -> None
  in
  match e_source with
  | Some _ev ->
      (match _ev.source with `Seq (_, `Choice _) -> true | _ -> false)
  | None -> false

(* Check if event is a branch point (has root, branch, or later successors) *)
let is_branch_event (ev : event) : bool =
  List.exists (fun src ->
    match src.source with
    | `Root(Some (_)) -> true
    | `Branch (_, _) -> true
    | `Later _ -> true
    | _ -> false
  ) ev.outs



(* Get event ID corresponding to an atomic action in the graph *)
let get_event_id_for_atomic_action 
    (ev : event) 
    (g : event_graph) 
    (atom : Lang.atomic_action_with_gap) : int =
  let atom_delay = match atom with
    | Lang.AtomicAct (Lang.AtomBMsg msg) -> Some msg
    | Lang.AtomicAct (Lang.AtomNBMsg msg) -> Some msg
    | Lang.AtomDelay _ -> None
    | _ -> 
        raise (Except.TypeError [
          Text (Printf.sprintf "Unsupported atomic action %s for event id retrieval" 
            (Lang.string_of_atomic_action_with_gap atom)); 
          Except.codespan_local g.thread_codespan
        ])
  in
  
  (* Handle delay actions *)
  if match atom with | Lang.AtomDelay _-> true | _ -> false then (
    let id = List.find_map (fun e ->
      match e.source with
      | `Seq (_, `Cycles _) -> Some e.id
      | _ -> None
    ) ev.outs in
    if Option.is_none id then
      raise (Except.TypeError [
        Text (Printf.sprintf "No event found for atomic action %s" 
          (Lang.string_of_atomic_action_with_gap atom)); 
        Except.codespan_local g.thread_codespan
      ])
    else
      Option.get id
  ) else (
    (* Handle send/recv actions *)
    let atom_delay = Option.get atom_delay in
    let ids = List.find_map (fun e ->
      match e.source with
      | `Seq (_, `Send msg) 
        when atom_delay.endpoint = msg.endpoint && atom_delay.msg = msg.msg -> 
          Some e.id
      | `Seq (_, `Recv msg) 
        when atom_delay.endpoint = msg.endpoint && atom_delay.msg = msg.msg -> 
          Some e.id
      | _ -> None
    ) ev.outs in
    if Option.is_none ids then
      raise (Except.TypeError [
        Text (Printf.sprintf "No event found for atomic action %s" 
          (Lang.string_of_atomic_action_with_gap atom)); 
        Except.codespan_local g.thread_codespan
      ])
    else
      Option.get ids
  )



(* Update event's session type by replacing it *)
let update_sty 
    (graph : event_graph) 
    (ev_id : int) 
    (new_sty : Lang.session_type) 
    (default_span : code_span) 
    (verbose : bool) =
  if ev_id < 0 then ()
  else
    let ev_opt = List.find_opt (fun e -> e.id = ev_id) graph.events in
    if Option.is_none ev_opt then
      raise (Except.TypeError [
        Text (Printf.sprintf "Event with id %d not found in graph during session type update" ev_id); 
        Except.codespan_local graph.thread_codespan
      ])
    else
      let ev = Option.get ev_opt in
      if verbose then 
        Printf.eprintf "Updating event %d session type to %s\n" 
          ev.id (Lang.string_of_protocol new_sty);
      ev.session_type <- Some {d= new_sty; span = default_span}

(* Update event's session type by sequencing with existing type *)
let update_sty_seq 
    (graph : event_graph) 
    (ev_id : int) 
    (new_sty : Lang.session_type) 
    (default_span : code_span) 
    (verbose : bool) =
  if ev_id < 0 then ()
  else
    let ev_opt = List.find_opt (fun e -> e.id = ev_id) graph.events in
    if Option.is_none ev_opt then
      raise (Except.TypeError [
        Text (Printf.sprintf "Event with id %d not found in graph during session type update" ev_id); 
        Except.codespan_local graph.thread_codespan
      ])
    else
      let ev = Option.get ev_opt in
      if Option.is_none ev.session_type then
        ev.session_type <- Some {d= new_sty; span = default_span}
      else
        let existing_sty = Option.get ev.session_type in
        if verbose then 
          Printf.eprintf "Updating event %d session type (%s) by sequencing with %s \n" 
            ev_id (Lang.string_of_protocol existing_sty.d) (Lang.string_of_protocol new_sty);
        ev.session_type <- Some {d = Lang.StySeq (existing_sty.d, new_sty); span = default_span}



(* Extract all atomic actions (send/recv/delay) from an event *)
let extract_atomic_actions 
    (ev : event) 
    (default_span : Lang.code_span) : (Lang.atomic_action_with_gap * Lang.code_span) list =
  (* Extract from immediate actions *)
  let extract_from_action (a_span : action Lang.ast_node) : (Lang.atomic_action_with_gap * Lang.code_span) option =
    match a_span.d with
    | ImmediateSend (msg, _) -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), a_span.span)
    | ImmediateRecv msg -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), a_span.span)
    | _ -> None
  in
  
  (* Extract from sustained actions *)
  let extract_from_sustained (sa_span : sustained_action Lang.ast_node) : (Lang.atomic_action_with_gap * Lang.code_span) option =
    match sa_span.d.ty with
    | Send (msg, _) -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), sa_span.span)
    | Recv msg -> Some (Lang.AtomicAct (Lang.AtomBMsg msg), sa_span.span)
  in
  
  let immediate_actions = List.filter_map extract_from_action ev.actions in
  let sustained_actions = List.filter_map extract_from_sustained ev.sustained_actions in

  (* Extract delay actions from outbound edges *)
  let out_acts = List.map (fun ev -> ev.source) ev.outs in
  let delay_actions = List.filter_map (fun (src : event_source) ->
    match src with
    | `Seq (_, `Cycles n) -> Some (Lang.AtomDelay n, default_span)
    | _ -> None
  ) out_acts in
  
  delay_actions @ immediate_actions @ sustained_actions

(* Check if two atomic actions are equivalent (returns match status and slack for delays) *)
let equivalence_of_action 
    (a1 : Lang.atomic_action_with_gap) 
    (a2 : Lang.atomic_action_with_gap) : (bool * (int option)) =
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

(* Check if event satisfies an atomic action (returns match, span, and slack) *)
let event_satisfies_atomic 
    (ev : event) 
    (atom : Lang.atomic_action_with_gap) 
    (verbose : bool) 
    (default_span : code_span) : (bool * Lang.code_span option * int option) =
  let actions = extract_atomic_actions ev default_span in
  let debug_action_list = List.map (fun (a, _) -> 
    Lang.string_of_atomic_action_with_gap a) actions in
  if verbose then 
    Printf.eprintf "Checking event %d for atomic action %s | present actions: %s\n" 
      ev.id (Lang.string_of_atomic_action_with_gap atom) (String.concat ", " debug_action_list); 

  match List.find_opt (fun (a, _) -> fst (equivalence_of_action a atom)) actions with
  | Some (a, span) -> (true, Some span, snd (equivalence_of_action a atom))
  | None -> (false, None, None)

(* Check if event has a conflicting action that doesn't match expected *)
let event_has_wrong_action 
    (ev : event) 
    (expected : Lang.atomic_action_with_gap) 
    (default_span : code_span) : (Lang.atomic_action_with_gap * Lang.code_span) option =
  let actions = extract_atomic_actions ev default_span in
  let satisfy_act = List.find_opt (fun (a, _) -> 
    fst (equivalence_of_action a expected)) actions in
  match satisfy_act with
  | Some _ -> None
  | None ->
      let conflicting_act = List.find_opt (fun (a, _) -> 
        not (fst (equivalence_of_action a expected))) actions in
      match conflicting_act with
      | Some (act, span) -> Some (act, span)
      | None -> None



(* Build choice session type from list of offerings *)
let rec build_choice_from_offerings (offerings : offering_session_type list) =
  if List.length offerings = 1 then
    let only = List.hd offerings in
    match only.trigger with
    | Lang.AtomicAct trig ->
        (match only.continuation with
        | Some sty -> Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty)
        | None -> Lang.StyAtom (Lang.AtomicAct trig)
        )
    | _ -> 
        match only.continuation with
        | Some sty -> sty
        | None -> Lang.StyTrue
  else
    let first = List.hd offerings in
    let rest = List.tl offerings in
    match first.trigger with
    | Lang.AtomicAct trig ->
        Lang.StyChoice(
          (match first.continuation with
          | Some sty -> Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty)
          | None -> Lang.StyAtom (Lang.AtomicAct trig)
          ),
          build_choice_from_offerings rest
        )
    | _ -> build_choice_from_offerings rest

(* SESSION TYPE JUDGEMENT (Core Type Checking Logic)*)

(* 
   Check if session type is satisfied by event and compute continuation.
   Returns: (next_event_id, continuation_type_option, error_option)
*)
let rec session_judgement 
    (st : Lang.session_type ast_node) 
    (ev : event) 
    (config : Config.compile_config) 
    (default_span : Lang.code_span) 
    (graph : event_graph) : (int * Lang.session_type option * (string * Lang.code_span) option) =
  let sty = st.d in

  (* Handle empty branches - propagate type to successor *)
  if ((not (is_wildcard_branch ev)) && (is_empty_branch ev)) then (
    if config.verbose then 
      Printf.eprintf "Empty branch event %d: propagating session type %s to successor\n" 
        ev.id (Lang.string_of_protocol sty);
    let ev_id = List.find (fun e ->
      match e.source with
      | `Branch (_, _) -> true
      | _ -> false
    ) ev.outs in
    (ev_id.id, Some sty, None)
  ) else
  
  match sty with
  (* Atomic action (send/recv) *)
  | Lang.StyAtom (Lang.AtomicAct atom) ->
      let (satisfied, _span, _) = event_satisfies_atomic ev (Lang.AtomicAct atom) config.verbose default_span in
      if satisfied then (
        let id = get_event_id_for_atomic_action ev graph (Lang.AtomicAct atom) in
        (id, None, None)
      ) else (
        match event_has_wrong_action ev (Lang.AtomicAct atom) default_span with
        | Some (wrong_act, span) ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but found '%s'"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom))
              (Lang.string_of_atomic_action_with_gap wrong_act) in
            (-1, Some sty, Some (err_msg, span))
        | None ->
            let err_msg = Printf.sprintf
              "Session type mismatch: expected '%s' but no matching action found"
              (Lang.string_of_atomic_action_with_gap (Lang.AtomicAct atom)) in
            (-1, Some sty, Some (err_msg, default_span))
      )
  
  (* Delay action *)
  | Lang.StyAtom (Lang.AtomDelay n) ->
      let satisfied, code_span, slack_opt = 
        event_satisfies_atomic ev (Lang.AtomDelay n) config.verbose default_span in
      let code_span = match code_span with
        | Some span -> span
        | None -> Lang.code_span_dummy in
      if satisfied then (
        let evid = get_event_id_for_atomic_action ev graph (Lang.AtomDelay n) in
        if Option.is_some slack_opt then (
          let slack = Option.get slack_opt in
          (evid, Some (Lang.StyAtom (Lang.AtomDelay slack)), None)
        ) else (
          (evid, None, None)
        )
      ) else (
        let err_msg = Printf.sprintf 
          "Session type mismatch: expected delay of at least %d cycles" n in
        (-1, Some sty, Some (err_msg, code_span))
      )
  
  (* True type (satisfied only at empty branches) *)
  | Lang.StyTrue ->
      if config.verbose then 
        Printf.eprintf "Session type true at event %d\n" ev.id;
      let child = List.find_opt (fun e ->
        match e.source with
        | `Branch (_, _) -> true
        | _ -> false
      ) ev.outs in
      if is_empty_branch ev then
        ((Option.get child).id, None, None)
      else (
        let err_msg = "Session type mismatch: true session type can only be at empty branch events" in
        (-1, Some sty, Some (err_msg, default_span))
      )
  
  (* Sequential composition s1; s2 *)
  | Lang.StySeq (s1, s2) ->
      if config.verbose then 
        Printf.eprintf "Checking sequence session type at event %d | s_1 = %s | s_2 = %s\n" 
          ev.id (Lang.string_of_protocol s1) (Lang.string_of_protocol s2);
      let (id, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      (match err1 with
      | Some _ -> (-1, Some sty, err1)
      | None ->
          (match s1_cont with
          | None ->
              (* s1 completed, propagate s2 *)
              if id < 0 then
                List.iter (fun succ_ev ->
                  update_sty_seq graph succ_ev.id s2 default_span config.verbose
                ) ev.outs
              else 
                update_sty graph id s2 default_span config.verbose;
              (id, Some s2, None)
          | Some s1' ->
              (* s1 partially completed, propagate seq(s1', s2) *)
              if config.verbose then 
                Printf.eprintf "Sequence continuation at event %d: s1' = %s, s2 = %s\n" 
                  ev.id (Lang.string_of_protocol s1') (Lang.string_of_protocol s2);
              let remaining = Lang.StySeq (s1', s2) in
              if id < 0 then
                List.iter (fun succ_ev ->
                  update_sty_seq graph succ_ev.id remaining default_span config.verbose
                ) ev.outs
              else
                update_sty graph id remaining default_span config.verbose;
              (id, Some remaining, None)
          )
      )
  
  (* Internal choice s1 + s2 *)
  | Lang.StyChoice (s1, s2) ->
      let (id1, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      let (id2, s2_cont, err2) = session_judgement {st with d = s2} ev config default_span graph in
      (match err1, err2 with
      | None, None ->
          (match s1_cont, s2_cont with
          | None, None -> (-1, None, None)
          | Some s1', None -> (id1, Some s1', None)
          | None, Some s2' -> (id2, Some s2', None)
          | Some s1', Some s2' ->
              let remaining = Lang.StyChoice (s1', s2') in
              if id1 != id2 then 
                let err_msg = "Session type mismatch in choice: different events for continuations" in
                (-1, Some sty, Some (err_msg, default_span))
              else
                (id1, Some remaining, None)
          )
      | Some _, None ->
          (match s2_cont with
          | None -> (id2, None, None)
          | Some s2' ->
              update_sty graph id2 s2' default_span config.verbose;
              (id2, Some s2', None)
          )
      | None, Some _ ->
          (match s1_cont with
          | None -> (id1, None, None)
          | Some s1' ->
              update_sty graph id1 s1' default_span config.verbose;
              (id1, Some s1', None)
          )
      | Some e1, Some e2 ->
          (-1, Some sty, Some (if Option.is_some err1 then e1 else e2))
      )
  
  (* Parallel composition s1 | s2 *)
  | Lang.StyParallel (s1, s2) ->
      let (id1, s1_cont, err1) = session_judgement {st with d = s1} ev config default_span graph in
      let (id2, s2_cont, err2) = session_judgement {st with d = s2} ev config default_span graph in
      (match err1, err2 with
      | None, None ->
          (match s1_cont, s2_cont with
          | None, None -> (-1, None, None)
          | None, Some s2' ->
              update_sty graph id2 s2' default_span config.verbose;
              (id2, Some s2', None)
          | Some s1', None ->
              update_sty graph id1 s1' default_span config.verbose;
              (id1, Some s1', None)
          | Some s1', Some s2' ->
              update_sty graph id1 s1' default_span config.verbose;
              update_sty graph id2 s2' default_span config.verbose;
              let ev_id = List.find_map (fun e ->
                match e.source with
                | `Later (id_a, id_b) 
                  when (id_a.id = id1 && id_b.id = id2) || (id_a.id = id2 && id_b.id = id1) -> 
                    Some e.id
                | _ -> None
              ) ev.outs in
              let ev_id = Option.value ev_id ~default:(-1) in
              (ev_id, None, None)
          )
      | _, _ ->
          let err_msg = "Session type mismatch in parallel composition" in
          (-1, Some sty, Some (err_msg, default_span))
      )
  
  (* Future/eventually type <>s *)
  | Lang.StyFuture s ->
      let actions = extract_atomic_actions ev default_span in
      let delay_act = match List.find_opt (fun (a, _) -> 
        match a with
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
          | None -> (-1, None, None)
          | Some s' -> (_id, Some s', None)
          )
  
  (* External choice (offering) - matches against graph choice edges *)
  | Lang.StyOffer offerings ->
      if List.length offerings < 2 then 
        raise (Except.TypeError [
          Text (Printf.sprintf "Not well formed choice dual session type | No of offerings = %d" 
            (List.length offerings)); 
          Except.codespan_local default_span
        ]);
      
      if config.verbose then
        Printf.eprintf "Checking event %d for dual choice with offerings: %s\n" ev.id 
          (String.concat ", " (List.map (fun (o:offering_session_type) -> 
            match o.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> Printf.sprintf "BMsg(%s, %s)" m.endpoint m.msg
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> Printf.sprintf "NBMsg(%s, %s)" m.endpoint m.msg
            | Lang.AtomDelay _ -> Printf.sprintf "Wildcard Delay"
            | _ -> raise (Except.TypeError [
                Text "Unsupported atomic action in offering session type"; 
                Except.codespan_local default_span
              ])
          ) offerings));
      
      (* Find choice messages in outbound edges *)
      let msg_list = List.find_map (fun (e : event) ->
        match e.source with 
        | `Seq (_ , `Choice msg_list) -> Some msg_list
        | _ -> None
      ) ev.outs in
      
      if Option.is_none msg_list then (
        let err_msg = Printf.sprintf 
          "Session type mismatch at event %d: expected choice messages but none found from event outbound edges event ids of outbounds = %s" 
          ev.id (String.concat ", " (List.map string_of_int (List.map (fun e -> e.id) ev.outs))) in
        (-1, Some sty, Some (err_msg, default_span))
      ) else (
        let msg_list = Option.get msg_list in
        let msg_list_offering = List.map (fun (o : offering_session_type) -> 
          match o.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg msg) -> msg
          | Lang.AtomicAct (Lang.AtomNBMsg msg) -> msg
          | Lang.AtomDelay _ -> {endpoint = "*"; msg = "*"}
          | _ -> raise (Except.TypeError [
              Text "Unsupported atomic action in offering session type"; 
              Except.codespan_local default_span
            ])
        ) offerings in
        
        if List.exists (fun m -> 
          List.exists (fun expected_m -> 
            m.endpoint = expected_m.endpoint && m.msg = expected_m.msg
          ) msg_list_offering
        ) msg_list then (
          let new_sty = build_choice_from_offerings offerings in
          let evid = List.find_map (fun e ->
            match e.source with
            | `Seq (_, `Choice msg_list_ev) ->
                if List.exists (fun m -> 
                  List.exists (fun expected_m -> 
                    m.endpoint = expected_m.endpoint && m.msg = expected_m.msg
                  ) msg_list_offering
                ) msg_list_ev then
                  Some e.id
                else None
            | _ -> None
          ) ev.outs in
          let evid = Option.value evid ~default:(-1) in
          update_sty graph evid new_sty default_span config.verbose;
          (evid, Some new_sty, None)
        ) else (
          let err_msg = "Session type mismatch: none of the offered messages match the expected choices" in
          (-1, Some sty, Some (err_msg, default_span))
        )
      )
  
  (* Exclusive External choice *)
  | Lang.StyXOffer offerings ->
      if List.length offerings < 2 then 
        raise (Except.TypeError [
          Text (Printf.sprintf "Not well formed choice dual session type | No of offerings = %d" 
            (List.length offerings)); 
          Except.codespan_local default_span
        ]);
      
      if config.verbose then
        Printf.eprintf "Checking event %d for dual choice with offerings: %s\n" ev.id 
          (String.concat ", " (List.map (fun (o:offering_session_type) -> 
            match o.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> Printf.sprintf "BMsg(%s, %s)" m.endpoint m.msg
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> Printf.sprintf "NBMsg(%s, %s)" m.endpoint m.msg
            | Lang.AtomDelay _ -> Printf.sprintf "Wildcard Delay"
            | _ -> raise (Except.TypeError [
                Text "Unsupported atomic action in offering session type"; 
                Except.codespan_local default_span
              ])
          ) offerings));
      
      (* Find choice messages in outbound edges *)
      let msg_list = List.find_map (fun (e : event) ->
        match e.source with 
        | `Seq (_ , `Choice msg_list) -> Some msg_list
        | _ -> None
      ) ev.outs in
      
      if Option.is_none msg_list then (
        let err_msg = Printf.sprintf 
          "Session type mismatch at event %d: expected choice messages but none found from event outbound edges event ids of outbounds = %s" 
          ev.id (String.concat ", " (List.map string_of_int (List.map (fun e -> e.id) ev.outs))) in
        (-1, Some sty, Some (err_msg, default_span))
      ) else (
        let msg_list = Option.get msg_list in
        let msg_list_offering = List.map (fun (o : offering_session_type) -> 
          match o.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg msg) -> msg
          | Lang.AtomicAct (Lang.AtomNBMsg msg) -> msg
          | Lang.AtomDelay _ -> {endpoint = "*"; msg = "*"}
          | _ -> raise (Except.TypeError [
              Text "Unsupported atomic action in offering session type"; 
              Except.codespan_local default_span
            ])
        ) offerings in
        
        if List.exists (fun m -> 
          List.exists (fun expected_m -> 
            m.endpoint = expected_m.endpoint && m.msg = expected_m.msg
          ) msg_list_offering
        ) msg_list then (
          Printf.eprintf "Exclusive choice matched at event %d\n" ev.id;
          let new_sty = build_choice_from_offerings offerings in
          let evid = List.find_map (fun e ->
            match e.source with
            | `Seq (_, `Choice msg_list_ev) ->
                if List.exists (fun m -> 
                  List.exists (fun expected_m -> 
                    m.endpoint = expected_m.endpoint && m.msg = expected_m.msg
                  ) msg_list_offering
                ) msg_list_ev then
                  Some e.id
                else None
            | _ -> None
          ) ev.outs in
          let evid = Option.value evid ~default:(-1) in
          update_sty graph evid new_sty default_span config.verbose;
          Printf.eprintf "Exclusive choice continuation session type at event %d: %s\n" 
            evid (Lang.string_of_protocol new_sty);
          (evid, Some new_sty, None)
        ) else (
          let err_msg = "Session type mismatch: none of the offered messages match the expected choices" in
          (-1, Some sty, Some (err_msg, default_span))
        )
      )
  
  (* Temp : Let binding: substitute and continue *)
  | StyLet (id, pdef, pbody) ->
      let sty = substitute_session_type_in_session_type pbody id pdef default_span in
      session_judgement {st with d = sty} ev config default_span graph
  
  (* Unimplemented session types *)
  | _ -> 
      raise (Except.UnimplementedError [
        Text (Printf.sprintf "Session judgement not implemented for session type %s" 
          (Lang.string_of_protocol sty)); 
        Except.codespan_local default_span
      ])



(* Check session type conformance for entire event graph using BFS traversal *)
let check_session 
    (config : Config.compile_config) 
    (g : event_graph) 
    module_name =
  let last_node_id = (List.length g.events) - 1 in
  
  if config.verbose then (
    Printf.eprintf "\n[Session Type Check] Starting session type check...\n";
    Printf.eprintf "Checking graph with %d events...\n" (List.length g.events);
    let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph_before.dot" module_name) in
    EventGraphOps.print_dot_graph g file_handler;
    Out_channel.close file_handler;
  );
  
  match g.interface_protocol with
  | None -> () (* No session type to check *)
  | Some protocol_node ->
      if config.verbose then
        Printf.eprintf "\n[Session Type Check] Checking protocol: %s\n" 
          (Lang.string_of_protocol protocol_node.Lang.d);
      
      (* Prepare graph for traversal *)
      GraphAnalysis.events_prepare_outs g.events;
      
      (* BFS traversal state *)
      let bfs_queue = Queue.create () in
      let visited = IntHashtbl.create (List.length g.events) in
      
      (* Explore graph starting from given event with initial session type *)
      let explore_graph start_ev initial_sty =
        Queue.add start_ev bfs_queue;
        IntHashtbl.add visited start_ev.id true;
        start_ev.session_type <- Some {protocol_node with Lang.d = initial_sty};
        
        while not (Queue.is_empty bfs_queue) do
          let ev = Queue.pop bfs_queue in
          if config.verbose then 
            Printf.eprintf "\n[Session Type Check] Exploring event %d | Current queue -> [%s]\n" 
              ev.id (String.concat ", " (List.map string_of_int (Queue.fold (fun acc x -> acc @ [x.id]) [] bfs_queue)));
          
          (* Skip last node (terminal event) *)
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
            
            (* Handle special empty branch case - skip processing *)
            if is_empty_branch_special_one ev then
              ()
            (* Branch events just propagate type to successors *)
            else if is_branch_event ev && (not (is_empty_branch ev)) then (
              if config.verbose then 
                Printf.eprintf "Branch event %d: propagating session type %s to successors\n" 
                  ev.id (Lang.string_of_protocol current_sty);
              List.iter (fun succ_ev ->
                update_sty g succ_ev.id current_sty g.thread_codespan config.verbose
              ) ev.outs
            ) else (
              (* Run session judgement - updates types internally *)
              let (_id, _continuation, error_opt) = session_judgement 
                {protocol_node with Lang.d = current_sty} 
                ev 
                config 
                g.thread_codespan 
                g 
              in
              
              (* Handle type checking errors *)
              match error_opt with
              | Some (err_msg, err_span) ->
                  if config.verbose then (
                    Printf.eprintf "Session type violation at event %d: %s\n" ev.id err_msg;
                    let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph_error.dot" module_name) in
                    EventGraphOps.print_graph_with_session_types g file_handler;
                    Out_channel.close file_handler
                  );
                  raise (Except.TypeError [
                    Text "Session type violation: ";
                    Text err_msg;
                    Except.codespan_local err_span
                  ])
              | None -> ()
            );
            
            (* Add unvisited successors to queue *)
            if is_empty_branch_special_one ev then
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
        
        (* Verify all events were reachable *)
        List.iter (fun ev ->
          if not (IntHashtbl.mem visited ev.id) && ev.id <> last_node_id then
            if config.verbose then 
              Printf.eprintf "[Warning]: Event %d was not reachable during session type check\n" ev.id
        ) g.events;
        
        (* Check if session type is satisfied at recursion point *)
        let last_ev_opt = List.find_opt (fun e -> e.is_recurse) g.events in
        (match last_ev_opt with
        | Some last_ev ->
            let final_sty = last_ev.session_type in
            (match final_sty with
            | Some sty when sty.d <> protocol_node.Lang.d ->
                if config.verbose then
                  raise (Except.TypeError [
                    Text (Printf.sprintf "Session type not fully completed at loop end: %s" 
                      (Lang.string_of_protocol sty.d));
                    Except.codespan_local g.thread_codespan
                  ])
            | _ -> ()
            )
        | None -> ()
        )
      in
      
      (* Start BFS from root event *)
      let root_ev = List.find (fun e -> e.source = `Root None) g.events in
      explore_graph root_ev protocol_node.Lang.d;
      
      if config.verbose then
        Printf.eprintf "[Session Type Check] Session type check completed successfully.\n";
      
      (* Output final graph with annotated session types *)
      let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph.dot" module_name) in
      EventGraphOps.print_graph_with_session_types g file_handler;
      Out_channel.close file_handler

type session_judgement_result = {
  judgement : bool;
  error_message : string option;
}

let default_session_judgement_result = {
  judgement = true;
  error_message = None;
}

let match_offerings_with_msgs
    (offerings : offering_session_type list)
    (msgs : Lang.message_specifier list) : bool =
    List.for_all (fun msg ->
      List.exists (fun offering ->
        match offering.trigger with
        | Lang.AtomicAct (Lang.AtomBMsg m) ->
            m.endpoint = msg.endpoint && m.msg = msg.msg
        | Lang.AtomicAct (Lang.AtomNBMsg m) ->
            m.endpoint = msg.endpoint && m.msg = msg.msg
        | Lang.AtomDelay _ -> msg.endpoint = "*" && msg.msg = "*"
        | _ -> false
      ) offerings
    ) msgs
  
  let rec delay_judgement
       (n : int) 
       (sty_node : session_type ast_node) : session_type option =
    match sty_node.d with
    | StyAtom (AtomDelay m) when n <= m -> 
        if n < m then (Some (Lang.StyAtom (Lang.AtomDelay (m - n)))) else (Some Lang.StyTrue)
    | StySeq (s1, s2) -> (
        let delay_judgement_opt = delay_judgement n {sty_node with d = s1} in
        match delay_judgement_opt with
        | Some new_sty ->
            let remaining_sty = match new_sty with
              | StyTrue -> s2
              | _ -> StySeq (new_sty, s2)
            in
            Some remaining_sty
        | None -> None
      )
    | StyParallel (s1, s2) -> (
        (* Try to satisfy delay in first branch *)
        let delay_judgement_opt1 = delay_judgement n {sty_node with d = s1} in
        match delay_judgement_opt1 with
        | Some new_sty1 -> Some (StyParallel (new_sty1, s2))
        | None ->
            let delay_judgement_opt2 = delay_judgement n {sty_node with d = s2} in
            match delay_judgement_opt2 with
            | Some new_sty2 -> Some (StyParallel (s1, new_sty2))
            | None -> None
      )
    | StyChoice (s1, s2) -> (
        (* Internal choice: try both branches, succeed if either matches *)
        let delay_judgement_opt1 = delay_judgement n {sty_node with d = s1} in
        match delay_judgement_opt1 with
        | Some new_sty1 -> Some new_sty1
        | None ->
            let delay_judgement_opt2 = delay_judgement n {sty_node with d = s2} in
            delay_judgement_opt2
      )
    | _ -> None
  
  let rec msg_judgement
      (msgs : Lang.message_specifier)
      (sty_node : session_type ast_node) : session_type option =
    match sty_node.d with
    | StyAtom (Lang.AtomicAct (Lang.AtomBMsg m)) when m.endpoint = msgs.endpoint && m.msg = msgs.msg -> Some Lang.StyTrue
    | StyAtom (Lang.AtomicAct (Lang.AtomNBMsg m)) when m.endpoint = msgs.endpoint && m.msg = msgs.msg -> Some Lang.StyTrue
    | StyParallel (s1, s2) -> (
        (* Try to satisfy message in first branch *)
        let msg_judgement_opt1 = msg_judgement msgs {sty_node with d = s1} in
        match msg_judgement_opt1 with
        | Some new_sty1 -> Some (StyParallel (new_sty1, s2))
        | None -> (
            (* Try second branch *)
            let msg_judgement_opt2 = msg_judgement msgs {sty_node with d = s2} in
            match msg_judgement_opt2 with
            | Some new_sty2 -> Some (StyParallel (s1, new_sty2))
            | None -> None
          )
      )
    | StySeq (s1, s2) -> (
        let msg_judgement_opt = msg_judgement msgs {sty_node with d = s1} in
        match msg_judgement_opt with
        | Some new_sty1 ->
            let remaining_sty = match new_sty1 with
              | StyTrue -> s2
              | _ -> StySeq (new_sty1, s2)
            in
            Some remaining_sty
        | None -> None
      )
    | StyChoice (s1, s2) -> (
        let msg_judgement_opt1 = msg_judgement msgs {sty_node with d = s1} in
        match msg_judgement_opt1 with
        | Some new_sty1 -> Some new_sty1
        | None ->
            let msg_judgement_opt2 = msg_judgement msgs {sty_node with d = s2} in
            msg_judgement_opt2
      )
    | _ -> None
  let rec join_judgement
      (sty_node1 : session_type)
      (sty_node2 : session_type) : session_type option =
    match (sty_node1, sty_node2) with
    | StyParallel (StyTrue, StyTrue), StyParallel (StyTrue, StyTrue) ->
        Some StyTrue
    | StyParallel (StyTrue, s1), StyParallel (StyTrue, s2) ->
        Some (StyParallel (s1, s2))
    | StyParallel (s1, StyTrue), StyParallel (s2, StyTrue) ->
        Some (StyParallel (s1, s2))
    | StyParallel(s1,StyTrue), StyParallel(StyTrue,s2) ->
        Some (StyParallel (s1, s2))
    | StyParallel(StyTrue,s1), StyParallel(s2,StyTrue) ->
        Some (StyParallel (s1, s2))
    | StyParallel (s1, s2), StyParallel (s3, s4) ->
      (
        let join1_opt = join_judgement s1 s3 in
        let join2_opt = join_judgement s2 s4 in
        match (join1_opt, join2_opt) with
        | Some j1, Some j2 -> Some (StyParallel (j1, j2))
        | _ -> None
      )
    | _ -> None
      
      
      
(* Generalized session type checking : traverse event graph and assign types to node for successors based on edges *)
let check_generalized_session 
    (config : Config.compile_config) 
    (g : event_graph) 
    module_name =
  
  if Option.is_none g.interface_protocol then
      Printf.eprintf "[Generalized Session Type Check] No interface protocol specified, skipping check.\n"
  
  else
    let protocol_node = Option.get g.interface_protocol in
    GraphAnalysis.events_prepare_outs g.events;

    if config.verbose then (
      Printf.eprintf "\n[Generalized Session Type Check] Starting generalized session type check...\n";
      Printf.eprintf "Checking graph with %d events...\n" (List.length g.events);
      let file_handler = Out_channel.open_text (Printf.sprintf "%sgraph_before.dot" module_name) in
      EventGraphOps.print_dot_graph g file_handler;
      Out_channel.close file_handler;
    );



    (* Visit the event graph DFS *)
    let rec generalized_session_judgement (ev : event) (visited : bool IntHashtbl.t) (context : session_judgement_result) : session_judgement_result  =
      if IntHashtbl.mem visited ev.id then context
      else begin
        IntHashtbl.add visited ev.id true;
        if config.verbose then
          Printf.eprintf "Visiting event %d in generalized session type check\n" ev.id;
        match ev.source with
        | `Root None ->
            ev.session_type <- Some protocol_node;
            {context with 
              judgement = List.for_all (fun succ_ev -> 
                let res = (generalized_session_judgement succ_ev visited context) in
                res.judgement
              )ev.outs
            }
        | `Root (Some (evt, _branch)) -> (
            match evt.session_type with
            | Some sty_node ->
                let rec distribute_seq_over_choice (s : session_type) (cont : session_type) : session_type =
                  match s with
                  | StyChoice (s1, s2) ->
                      StyChoice (distribute_seq_over_choice s1 cont, distribute_seq_over_choice s2 cont)
                  | StySeq (s1, s2) ->
                      (* (s1; s2); cont => s1; (s2; cont) - then recurse on s1 *)
                      distribute_seq_over_choice s1 (StySeq (s2, cont))
                  | StyParallel (s1, s2) ->
                      (* (s1 || s2); cont - keep parallel, append cont *)
                      StySeq (StyParallel (s1, s2), cont)
                  | _ ->
                      (* Base case: just sequence *)
                      StySeq (s, cont)
                in

                let rec branch_judgement (sty : session_type) : session_judgement_result =
                  match sty with
                  | StyChoice (s1, s2) ->
                      let visited_backup = IntHashtbl.copy visited in
                      ev.session_type <- Some {sty_node with d = s1};
                      let jud1 = List.for_all (fun succ_ev ->
                        let res = (generalized_session_judgement succ_ev visited context) in
                        res.judgement
                      ) ev.outs in
                      if jud1 then
                        { context with judgement = true }
                      else (
                        IntHashtbl.clear visited;
                        IntHashtbl.iter (fun k v -> IntHashtbl.add visited k v) visited_backup;
                        IntHashtbl.add visited ev.id true;
                        ev.session_type <- Some {sty_node with d = s2};
                        let jud2 = List.for_all (fun succ_ev ->
                          let res = (generalized_session_judgement succ_ev visited context) in
                          res.judgement
                        ) ev.outs in
                        { context with judgement = jud2 }
                      )
                  | StySeq (s1, s2) ->
                      let distributed = distribute_seq_over_choice s1 s2 in
                      (match distributed with
                      | StyChoice _ -> branch_judgement distributed
                      | _ ->
                          ev.session_type <- Some {sty_node with d = sty};
                          let jud = List.for_all (fun succ_ev ->
                            let res = (generalized_session_judgement succ_ev visited context) in
                            res.judgement
                          ) ev.outs in
                          { context with judgement = jud }
                      )
                  | StyParallel (s1, s2) ->
                      let rec flatten_choice (s : session_type) : session_type list =
                        match s with
                        | StyChoice (a, b) -> flatten_choice a @ flatten_choice b
                        | _ -> [s]
                      in
                      let s1_choices = flatten_choice s1 in
                      let s2_choices = flatten_choice s2 in
                      
                      (* Try all combinations of choices from s1 and s2 *)
                      let rec try_combinations s1_list s2_list =
                        match s1_list with
                        | [] -> { context with judgement = false }
                        | s1_opt :: s1_rest ->
                            let rec try_s2 s2_list =
                              match s2_list with
                              | [] -> try_combinations s1_rest s2_choices
                              | s2_opt :: s2_rest ->
                                  let visited_backup = IntHashtbl.copy visited in
                                  let combined = StyParallel (s1_opt, s2_opt) in
                                  ev.session_type <- Some {sty_node with d = combined};
                                  let jud = List.for_all (fun succ_ev ->
                                    let res = (generalized_session_judgement succ_ev visited context) in
                                    res.judgement
                                  ) ev.outs in
                                  if jud then
                                    { context with judgement = true }
                                  else (
                                    (* Restore and try next combination *)
                                    IntHashtbl.clear visited;
                                    IntHashtbl.iter (fun k v -> IntHashtbl.add visited k v) visited_backup;
                                    IntHashtbl.add visited ev.id true;
                                    try_s2 s2_rest
                                  )
                            in
                            try_s2 s2_list
                      in
                      try_combinations s1_choices s2_choices
                  | _ -> 
                      (* For other types (atoms, etc), assign directly *)
                      ev.session_type <- Some {sty_node with d = sty};
                      let jud = List.for_all (fun succ_ev ->
                        let res = (generalized_session_judgement succ_ev visited context) in
                        res.judgement
                      ) ev.outs in
                      { context with judgement = jud }
                in
                branch_judgement sty_node.d
            | None ->
                raise (Except.TypeError [
                  Text (Printf.sprintf "Unexpected missing session type at event %d" evt.id);
                  Except.codespan_local g.thread_codespan
                ])
          )
        | `Seq (evt, atmdelay) -> (
            match atmdelay with
            | `Cycles n -> (
                match evt.session_type with
                | Some sty_node -> (
                    let delay_judgement_opt = delay_judgement n sty_node in
                      match delay_judgement_opt with
                      | Some new_sty ->
                          ev.session_type <- Some {sty_node with d = new_sty}; 
                          let jud = List.for_all (fun succ_ev ->
                          let res = (generalized_session_judgement succ_ev visited context) in
                            res.judgement
                          ) ev.outs in
                          { context with judgement = jud }
                      | None ->
                          { context with judgement = false }
                    )
                | None ->
                    raise (Except.TypeError [
                      Text (Printf.sprintf "Unexpected missing session type at event %d" evt.id);
                      Except.codespan_local g.thread_codespan
                    ])
              )
            | `Send msg -> (
                match evt.session_type with
                | Some sty_node -> (
                    let msg_judgement_opt = msg_judgement msg sty_node in
                    match msg_judgement_opt with
                    | Some new_sty ->
                        ev.session_type <- Some {sty_node with d = new_sty};
                        let jud = List.for_all (fun succ_ev ->
                          let res = (generalized_session_judgement succ_ev visited context) in
                          res.judgement
                        ) ev.outs in
                        { context with judgement = jud }
                    | None ->
                        { context with judgement = false }
                )
                | None ->
                    raise (Except.TypeError [
                      Text (Printf.sprintf "Unexpected missing session type at event %d" evt.id);
                      Except.codespan_local g.thread_codespan
                    ])
            )
            | `Recv msg -> (
                match evt.session_type with
                | Some sty_node -> (
                    let msg_judgement_opt = msg_judgement msg sty_node in
                    match msg_judgement_opt with
                    | Some new_sty ->
                        ev.session_type <- Some {sty_node with d = new_sty};
                        let jud = List.for_all (fun succ_ev ->
                          let res = (generalized_session_judgement succ_ev visited context) in
                          res.judgement
                        ) ev.outs in
                        { context with judgement = jud }
                    | None ->
                        { context with judgement = false }
                )
                | None ->
                    raise (Except.TypeError [
                      Text (Printf.sprintf "Unexpected missing session type at event %d" evt.id);
                      Except.codespan_local g.thread_codespan
                    ])
            )
            | `Choice msg_list ->(
                match evt.session_type with
                | Some sty_node -> (
                  match sty_node.d with
                  | StyOffer offerings ->
                    (
                      if List.length offerings < List.length msg_list then
                        (
                        Printf.eprintf "Event %d: offerings length %d < msg_list length %d\n" ev.id (List.length offerings) (List.length msg_list);
                        { context with judgement = false }
                        )
                      else
                        if match_offerings_with_msgs offerings msg_list then
                          let new_sty = build_choice_from_offerings offerings in
                          ev.session_type <- Some {sty_node with d = new_sty};
                          let jud = List.for_all (fun succ_ev ->
                            let res = (generalized_session_judgement succ_ev visited context) in
                            res.judgement
                          ) ev.outs in
                          { context with judgement = jud }
                        else
                          { context with judgement = false }
                  )
                  | StyXOffer offerings ->
                    (
                      if List.length offerings < List.length msg_list then
                        ( Printf.eprintf "Event %d: offerings length %d < msg_list length %d\n" ev.id (List.length offerings) (List.length msg_list);
                          { context with judgement = false }
                        )
                      else
                        if match_offerings_with_msgs offerings msg_list then
                          let new_sty = build_choice_from_offerings offerings in
                          ev.session_type <- Some {sty_node with d = new_sty};
                          let jud = List.for_all (fun succ_ev ->
                            let res = (generalized_session_judgement succ_ev visited context) in
                            res.judgement
                          ) ev.outs in
                          { context with judgement = jud }
                        else
                          { context with judgement = false }
                    )
                  | StySeq (s1, s2) ->
                    (
                      let rec distribute_seq_over_offering (s : session_type) (cont : session_type) : session_type =
                        match s with
                        | StyOffer offerings ->
                            let new_offerings = List.map (fun o ->
                              { o with continuation = match o.continuation with | Some cont -> Some (distribute_seq_over_offering cont cont) | None -> None }
                            ) offerings in
                            StyOffer new_offerings
                        | StyXOffer offerings ->
                            let new_offerings = List.map (fun o ->
                              { o with continuation = match o.continuation with | Some cont -> Some (distribute_seq_over_offering cont cont) | None -> None }
                            ) offerings in
                            StyXOffer new_offerings
                        | _ ->
                            StySeq (s, cont)
                      in
                      let distributed = distribute_seq_over_offering s1 s2 in
                      (
                        match distributed with
                        | StyOffer offerings ->
                          (
                            if List.length offerings < List.length msg_list then
                              ( Printf.eprintf "Event %d: offerings length %d < msg_list length %d\n" ev.id (List.length offerings) (List.length msg_list);
                                { context with judgement = false }
                              )
                            else
                              if match_offerings_with_msgs offerings msg_list then
                                let new_sty = build_choice_from_offerings offerings in
                                ev.session_type <- Some {sty_node with d = new_sty};
                                let jud = List.for_all (fun succ_ev ->
                                  let res = (generalized_session_judgement succ_ev visited context) in
                                  res.judgement
                                ) ev.outs in
                                { context with judgement = jud }
                              else
                                { context with judgement = false }
                          )
                          | StyXOffer offerings ->
                            (
                              if List.length offerings < List.length msg_list then
                                ( Printf.eprintf "Event %d: offerings length %d < msg_list length %d\n" ev.id (List.length offerings) (List.length msg_list);
                                  { context with judgement = false }
                                )
                              else
                                if match_offerings_with_msgs offerings msg_list then
                                  let new_sty = build_choice_from_offerings offerings in
                                  ev.session_type <- Some {sty_node with d = new_sty};
                                  let jud = List.for_all (fun succ_ev ->
                                    let res = (generalized_session_judgement succ_ev visited context) in
                                    res.judgement
                                  ) ev.outs in
                                  { context with judgement = jud }
                                else
                                  { context with judgement = false }
                            )
                          | _ -> {context with judgement = false}                       
                        )
                  )
                  (* | StyParallel (s1, s2) ->
                    

                    context
                    ) *)
                  | _ -> {context with judgement = false}
                )
                | None ->
                    raise (Except.TypeError [
                      Text (Printf.sprintf "Unexpected missing session type at event %d" evt.id);
                      Except.codespan_local g.thread_codespan
                    ])
            )
            | _ -> 
                raise (Except.UnimplementedError [
                  Text  ("Generalized session type judgement not implemented for event id " ^ string_of_int ev.id);
                  Except.codespan_local g.thread_codespan
                ])
        )
        | `Later (evt_a, evt_b) -> (
          let sty_node_opt_a = evt_a.session_type in
          let sty_node_opt_b = evt_b.session_type in
          match (sty_node_opt_a, sty_node_opt_b) with
          | (Some sty_node_a, Some sty_node_b) -> (
              let join_judgement_opt = join_judgement sty_node_a.d sty_node_b.d in
              match join_judgement_opt with
              | Some new_sty ->
                  ev.session_type <- Some {sty_node_a with d = new_sty};
                  let jud = List.for_all (fun succ_ev ->
                    let res = (generalized_session_judgement succ_ev visited context) in
                    res.judgement
                  ) ev.outs in
                  { context with judgement = jud }
              | None ->
                  { context with judgement = false }
            )
          | _ ->
              raise (Except.TypeError [
                Text (Printf.sprintf "Unexpected missing session type at event ids %d or %d" evt_a.id evt_b.id);
                Except.codespan_local g.thread_codespan
              ])
        )
        | `Branch (_, branch) -> (
            (* find the branch parent who has a type and assign that type *)
            (*  *)
            let found = ref false in
            List.iter (
              fun parent_ev ->
                match parent_ev.session_type with
                | Some styd_node ->
                    if !found = true then raise (Except.TypeError [
                      Text (Printf.sprintf "Multiple branch parents with session types , should not happen");
                      Except.codespan_local g.thread_codespan
                    ]);
                    found := true;
                    ev.session_type <- Some styd_node
                | None -> ()
            ) branch.branches_val;
            if !found = false then
              raise (Except.TypeError [
                Text (Printf.sprintf "No branch parent with session type found for branch event %d | Should not happen" ev.id);
                Except.codespan_local g.thread_codespan
              ]);
            let jud = List.for_all (fun succ_ev ->
              let res = (generalized_session_judgement succ_ev visited context) in
              res.judgement
            ) ev.outs in
            { context with judgement = jud }            
        )
        | _ ->
            raise (Except.UnimplementedError [
              Text  ("Generalized session type judgement not implemented for event id " ^ string_of_int ev.id);
              Except.codespan_local g.thread_codespan
            ])
      end in

    let visited = IntHashtbl.create (List.length g.events) in
    let root_ev = List.find (fun e -> e.source = `Root None) g.events in
    let result  = generalized_session_judgement root_ev visited default_session_judgement_result in
    if result.judgement then begin
        Printf.eprintf "[Generalized Session Type Check] Generalized session type check completed successfully.\n";
        let file_name = Printf.sprintf "%sgraph.dot" module_name in
        let file_handler = Out_channel.open_text file_name in
        EventGraphOps.print_graph_with_session_types g file_handler;
        Out_channel.close file_handler
    end else
      let file_name = Printf.sprintf "%sgraph.dot" module_name in
      let file_handler = Out_channel.open_text file_name in
      EventGraphOps.print_graph_with_session_types g file_handler;
      Out_channel.close file_handler;
      raise (Except.TypeError [
        Text "Generalized session type violation detected in event graph.";
        Except.codespan_local g.thread_codespan
      ]);
    
    (* Output final graph with annotated session types *)
