open Lang
open EventGraph

module IntHashtbl = Hashtbl.Make(Int)


type big_atomic_action =
  | Atom of atomic_action_with_gap
  | Offers of offering_session_type list

type head_continuation_pair = {
  head : big_atomic_action;
  cont : session_type;
  mutable visited : bool;
  is_choice : bool;
}
let default_head_continuation_pair = {
  head = Atom (AtomicAct (AtomBMsg {endpoint = ""; msg = ""}));
  cont = StyTrue;
  visited = false;
  is_choice = false;
}


(* Helper functions for session type judgements *)

(* Match offerings with messages *)
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

(* Error handler that outputs the graph with session types before raising error *)
let error_handler g err_msg err_span module_name  =
  let file_handler = Out_channel.open_text (Printf.sprintf "%s_error.dot" module_name) in
  EventGraphOps.print_graph_with_session_types g file_handler;
  Out_channel.close file_handler;

  raise (Except.TypeError [
    Text "Session type violation: ";
    Text err_msg;
    Except.codespan_local err_span
  ])
  
    

(* Build choice session type from list of offerings *)
let rec build_choice_from_xofferings (offerings : offering_session_type list) =
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
          build_choice_from_xofferings rest
        )
    | _ -> build_choice_from_xofferings rest
  
let rec build_choice_from_offerings (offerings : offering_session_type list) =
    if List.length offerings = 1 then
    let only = List.hd offerings in
    match only.trigger with
    | Lang.AtomicAct trig ->
        (match only.continuation with
        | Some sty -> StyChoice(Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty), Lang.StyTrue)
        | None -> StyChoice(Lang.StyAtom (Lang.AtomicAct trig), Lang.StyTrue)
        )
    | _ -> 
        match only.continuation with
        | Some sty -> StyChoice(sty, Lang.StyTrue)
        | None -> Lang.StyTrue
  else
    let first = List.hd offerings in
    let rest = List.tl offerings in
    match first.trigger with
    | Lang.AtomicAct trig ->
        Lang.StyParallel(
          (match first.continuation with
          | Some sty -> StyChoice(Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty), Lang.StyTrue)
          | None -> StyChoice(Lang.StyAtom (Lang.AtomicAct trig), Lang.StyTrue)
          ),
          build_choice_from_offerings rest
        )
    | _ -> build_choice_from_offerings rest

let rec get_head_continuation_pair (sty_node : session_type) (sp : code_span) : head_continuation_pair list =
  match sty_node with
  | StyAtom (AtomicAct act) -> [{default_head_continuation_pair with head = Atom (AtomicAct act); cont = StyTrue}]
  | StyAtom (AtomDelay n) -> [{default_head_continuation_pair with head = Atom (AtomDelay n); cont = StyTrue}]
  | StySeq (s1, s2) -> (
      let head_conts = get_head_continuation_pair s1 sp in
      List.map (fun hc ->
        {hc with cont = 
          match hc.cont with
          | StyTrue -> s2
          | _ -> StySeq (hc.cont, s2)
        }
      ) head_conts
    )
  | StyParallel (s1, s2) -> (
      let head_conts1 = get_head_continuation_pair s1 sp in
      let head_conts2 = get_head_continuation_pair s2 sp in
      head_conts1 @ head_conts2
    )
  | StyChoice (s1, s2) -> (
      let head_conts1 = get_head_continuation_pair s1 sp in
      let head_conts2 = get_head_continuation_pair s2 sp in
      List.map (fun hc -> {hc with is_choice = true}) (head_conts1 @ head_conts2)
    )
  | StyFuture s -> 
    let head_conts = get_head_continuation_pair s sp in
    let possible_delay = {default_head_continuation_pair with head = Atom (AtomDelay 1); cont = StyFuture s; is_choice = true} in
    possible_delay :: head_conts
  | StyXOffer offerings ->
      let continuation = build_choice_from_xofferings offerings in
      [{default_head_continuation_pair with head = Offers offerings; cont = continuation}]
  | StyOffer offerings ->
      let continuation = build_choice_from_offerings offerings in
      [{default_head_continuation_pair with head = Offers offerings; cont = continuation}]
  | _ -> raise (Except.TypeError [
      Text (Printf.sprintf "Unsupported session type %s for head-continuation extraction"
        (Lang.string_of_protocol sty_node));
      Except.codespan_local sp
    ])

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

    (* Visit the event graph BFS *)
    let rec generalized_session_judgement
        (next_queue : event Queue.t)
        (visited : bool IntHashtbl.t) =
      if Queue.is_empty next_queue then
        ()
      else
        let ev = Queue.pop next_queue in
        if IntHashtbl.mem visited ev.id || ev.is_recurse then
          (
            IntHashtbl.add visited ev.id true;
            generalized_session_judgement next_queue visited
          )
        else begin
          IntHashtbl.add visited ev.id true;

          (* Process current event *)

          let current_sty = match ev.session_type with
            | Some sty_node -> if sty_node.d = Lang.StyTrue && not ev.is_recurse then
                protocol_node.d
              else
                sty_node.d
            | None -> 
              let err_msg = Printf.sprintf 
                "Event %d has no session type assigned during generalized session type check" ev.id in
              error_handler g err_msg g.thread_codespan module_name
            in
    

          let child_events = ev.outs in
          let head_conts = get_head_continuation_pair current_sty g.thread_codespan in
          let is_propogated = ref false in

          List.iter (fun child_ev ->
            match child_ev.source with
            | `Seq (_, `Choice msg_list) ->
                let found = List.exists (fun hc ->
                  match hc.head with
                  | Offers offerings ->
                      let msgs = msg_list in
                      let matches = match_offerings_with_msgs offerings msgs in
                      if matches then begin
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true
                      end;
                      matches
                  | _ -> false
                ) head_conts in
                if not found then
                  error_handler g (Printf.sprintf "Expected Offerings at event %d | However found %s"
                    child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name

            | `Seq (_, `Send msg) ->
                let found = List.exists (fun hc ->
                  match hc.head with
                  | Atom (AtomicAct (AtomBMsg m)) ->
                      if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true
                      end;
                      m.endpoint = msg.endpoint && m.msg = msg.msg
                  | Atom (AtomicAct (AtomNBMsg m)) ->
                      if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true
                      end;
                      m.endpoint = msg.endpoint && m.msg = msg.msg
                  | __ -> false
                ) head_conts in

                if not found then
                  error_handler g (Printf.sprintf "Expected Send message at event %d | However found %s"
                    child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name
                  
                  
            | `Seq (_, `Recv msg) ->
                let found = List.exists (fun hc ->
                  match hc.head with
                  | Atom (AtomicAct (AtomBMsg m)) ->
                      if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true
                      end;
                      m.endpoint = msg.endpoint && m.msg = msg.msg
                  | Atom (AtomicAct (AtomNBMsg m)) ->
                      if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true
                      end;
                      m.endpoint = msg.endpoint && m.msg = msg.msg
                  | __ -> false
                ) head_conts in

                if not found then
                  error_handler g (Printf.sprintf "Expected Send message at event %d | However found %s"
                      child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name
            | `Seq (_, `Cycles n) ->
              let found = List.exists (fun hc ->
                match hc.head with
                | Atom (AtomDelay m) ->
                    if n <= m then begin
                      let remaining_delay = if n < m then StyAtom (AtomDelay (m - n)) else StyTrue in
                      let new_cont = match remaining_delay with
                        | StyTrue -> hc.cont
                        | _ -> StySeq (remaining_delay, hc.cont)
                      in
                      child_ev.session_type <- Some {protocol_node with d = new_cont};
                      hc.visited <- true
                    end;
                    n <= m
                | _ -> false
              ) head_conts in
              if not found then
                error_handler g (Printf.sprintf "Expected Delay at event %d | However found %s"
                  child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name
            | `Root Some _ ->
                child_ev.session_type <- Some {protocol_node with d = current_sty};
            | `Later (ev_a, ev_b) ->
                (
                  match ev_a.session_type, ev_b.session_type with
                  | Some sty_a_node, Some sty_b_node ->
                      let cont_a = match sty_a_node.d with
                        | StyParallel (StyTrue, cont) -> cont
                        | StyParallel (cont, StyTrue) -> cont
                        | _ -> error_handler g (Printf.sprintf "Type mismatch at later event %d: expected parallel with terminated branch | Found %s"
                            child_ev.id (Lang.string_of_protocol sty_a_node.d)) g.thread_codespan module_name in
                      let cont_b = match sty_b_node.d with
                        | StyParallel (StyTrue, cont) -> cont
                        | StyParallel (cont, StyTrue) -> cont
                        | _ -> error_handler g (Printf.sprintf "Type mismatch at later event %d: expected parallel with terminated branch | Found %s"
                            child_ev.id (Lang.string_of_protocol sty_b_node.d)) g.thread_codespan module_name in
                      ev.session_type <- Some {protocol_node with d = StyParallel (cont_a, cont_b)}
                  | _ ->
                      raise (Except.TypeError [
                        Text (Printf.sprintf "Unexpected missing session type at later event %d"
                          child_ev.id);
                        Except.codespan_local g.thread_codespan
                      ])
              )
            | `Branch(_, branch) ->
                let true_cont_node = match ((List.hd branch.branches_val).session_type) with
                  | Some sty -> sty
                  | None -> raise (Except.TypeError [
                      Text (Printf.sprintf "Missing session type at branch event %d"
                        child_ev.id);
                      Except.codespan_local g.thread_codespan
                    ]) in
                List.iter (fun b ->
                  match b.session_type with
                  | Some sty ->
                      if sty.d <> true_cont_node.d then
                        error_handler g (Printf.sprintf "Mismatched session types in branch event %d"
                          child_ev.id) g.thread_codespan module_name
                  | None ->
                      error_handler g (Printf.sprintf "Missing session type in branch event %d"
                        child_ev.id) g.thread_codespan module_name
                ) branch.branches_val;
                is_propogated := true;
                child_ev.session_type <- Some true_cont_node
            | _ ->
                error_handler g (Printf.sprintf "Unsupported child event source at event %d during generalized session type\n  check" child_ev.id) g.thread_codespan module_name
          ) child_events;

          List.iter (fun hc ->
            if not hc.visited && not hc.is_choice && not !is_propogated then
              error_handler g (Printf.sprintf "No matching head-continuation found for event %d's children during generalized session type check | Head: %s | Cont: %s"
                ev.id (match hc.head with | Offers off -> string_of_protocol (StyOffer off) | Atom act -> string_of_atomic_action_with_gap act) (string_of_protocol hc.cont) ) g.thread_codespan module_name 
          ) head_conts;

          (* Enqueue unvisited child events *)
          List.iter (fun child_ev ->
            if not (IntHashtbl.mem visited child_ev.id) then
              Queue.add child_ev next_queue
          ) child_events;


          generalized_session_judgement next_queue visited
        end
    in


    let visited_tbl = IntHashtbl.create (List.length g.events) in
    let q = Queue.create () in
    let root_ev = List.find (fun e -> e.source = `Root None) g.events in

    root_ev.session_type <- Some protocol_node;
    Queue.add root_ev q;
    
    generalized_session_judgement q visited_tbl;
    let file_name = Printf.sprintf "%sgraph.dot" module_name in
    let file_handler = Out_channel.open_text file_name in
    EventGraphOps.print_graph_with_session_types g file_handler;
    Out_channel.close file_handler
    
    (* Output final graph with annotated session types *)
