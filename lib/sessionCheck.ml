open Lang
open EventGraph

module IntHashtbl = Hashtbl.Make(Int)


type big_atomic_action =
  | Atom of atomic_action_with_gap
  | Offers of offering_session_type list
  | XOffers of offering_session_type list
  | Terminal

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

let print_string_of_head_cont_pair hc =
  let head_str = match hc.head with
    | Atom act -> string_of_atomic_action_with_gap act
    | Offers off -> string_of_protocol (StyOffer off)
    | XOffers xoff -> string_of_protocol (StyXOffer xoff)
    | Terminal -> string_of_protocol StyTrue
  in
  let cont_str = string_of_protocol hc.cont in
  Printf.sprintf "[Head: %s | Cont: %s]" head_str cont_str

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
  | StyParallel (s1, s2) ->
  (
    match s1, s2 with
    | StyTrue, StyTrue -> [{default_head_continuation_pair with head = Terminal; cont = StyTrue}]
    | _ ->
     (
      let head_conts1 = get_head_continuation_pair s1 sp in
      let head_conts1 = List.map (fun hc -> {hc with cont = StyParallel (hc.cont, StyTrue)}) head_conts1 in
      let head_conts2 = get_head_continuation_pair s2 sp in
      let head_conts2 = List.map (fun hc -> {hc with cont = StyParallel (StyTrue, hc.cont)}) head_conts2 in
      head_conts1 @ head_conts2
    )
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
      (* let continuation = build_choice_from_xofferings offerings in *)
      [{default_head_continuation_pair with head = XOffers offerings; cont = StyTrue}]
  | StyOffer offerings ->
      (* let continuation = build_choice_from_offerings offerings in *)
      [{default_head_continuation_pair with head = Offers offerings; cont = StyTrue}]
  | StyTrue -> [{default_head_continuation_pair with head = Terminal; cont = StyTrue}]
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
          if config.verbose then
            Printf.eprintf "Processing event %d with session type %s\n"
              ev.id (Lang.string_of_protocol current_sty);

          let child_events = ev.outs in
          let head_conts = get_head_continuation_pair current_sty g.thread_codespan in
          if config.verbose then (
            Printf.eprintf "Extracted head-continuation pairs for event %d:\n" ev.id;
            List.iter (fun hc ->
              Printf.eprintf "  %s\n" (print_string_of_head_cont_pair hc)
            ) head_conts
          );
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
                        let co = match hc.cont with 
                        |StyTrue -> build_choice_from_offerings offerings 
                        | _-> StySeq (build_choice_from_offerings offerings, hc.cont) 
                      in
                        child_ev.session_type <- Some {protocol_node with d = co};
                        hc.visited <- true
                      end;
                      matches
                  | XOffers offerings ->
                      let msgs = msg_list in
                      let matches = match_offerings_with_msgs offerings msgs in
                      if matches then begin
                        let co = match hc.cont with 
                        |StyTrue -> build_choice_from_xofferings offerings 
                        | _-> StySeq (build_choice_from_xofferings offerings, hc.cont) 
                      in
                        child_ev.session_type <- Some {protocol_node with d = co};
                        hc.visited <- true
                      end;
                      matches
                  | _ -> false
                ) head_conts in
                if not found then
                  error_handler g (Printf.sprintf "Expected Offerings at event %d | However found %s"
                    child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                Queue.add child_ev next_queue


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
                  error_handler g (Printf.sprintf "Expected Send message (%s) at event %d | However found %s"
                   (string_of_msg_spec msg) child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                Queue.add child_ev next_queue
                  
                  
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
                      child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                Queue.add child_ev next_queue
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
                  child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                Queue.add child_ev next_queue
            | `Root Some (_, branches) ->
               if Option.is_none child_ev.session_type then begin
                let is_empty_branch = List.for_all( fun e ->
                  match e.source with
                  | `Branch _ -> true
                  | _ -> false
                )child_ev.outs in
                let has_immediate_actions = List.filter ( fun a ->
                  match a.d with
                  | ImmediateRecv _ | ImmediateSend _ -> true
                  | _ -> false
                ) child_ev.actions in
                let offer_atoms = List.filter_map (fun hc ->
                  match hc.head with
                  | Offers _ -> Some hc
                  | XOffers _ -> Some hc
                  | _ -> None
                ) head_conts in
                if List.length has_immediate_actions > 0 then begin
                  List.iter (fun ia ->
                    match ia.d with
                    | ImmediateRecv msg ->
                        let found_hc_opt =
                          List.find_opt (fun hc ->
                            match hc.head with
                            | XOffers offerings | Offers offerings ->
                                List.for_all (fun offering ->
                                  match offering.trigger with
                                  | Lang.AtomicAct (Lang.AtomBMsg m) ->
                                      m.endpoint = msg.endpoint && m.msg = msg.msg
                                  | Lang.AtomicAct (Lang.AtomNBMsg m) ->
                                      m.endpoint = msg.endpoint && m.msg = msg.msg
                                  | Lang.AtomDelay _ -> true
                                  | _ -> false
                                ) offerings
                            | _ -> false
                          ) offer_atoms
                        in
                        if Option.is_none found_hc_opt then
                          error_handler g (Printf.sprintf "Expected Offerings for ImmediateRecv at event %d | However found %s"
                            child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name
                        else
                          let hc = Option.get found_hc_opt in
                          Printf.eprintf "Found matching head-continuation for ImmediateRecv at event %d: %s\n"
                            child_ev.id (print_string_of_head_cont_pair hc);
                          List.iter (fun h ->
                            if h = hc then h.visited <- true
                          ) head_conts;
                          let cont = match hc.head with
                            | Offers offerings -> offerings
                            | XOffers offerings -> offerings
                            | _ -> []
                          in
                          if List.length cont > 2 then
                            error_handler g (Printf.sprintf "Multiple matching offerings for ImmediateRecv at event %d"
                              child_ev.id) g.thread_codespan module_name
                          else
                            let own_cont, other_cont = if (List.nth cont 0 ).trigger = Lang.AtomicAct (Lang.AtomBMsg msg)
                              || (List.nth cont 0 ).trigger = Lang.AtomicAct (Lang.AtomNBMsg msg) then
                                (List.nth cont 0, List.nth cont 1)
                              else
                                (List.nth cont 1, List.nth cont 0)
                      
                            in
                            let own_contin = match own_cont.continuation, hc.cont with
                              | None , StyTrue -> StyTrue
                              | Some st, StyTrue -> st
                              | Some st, st' -> StySeq (st, st')
                              | None, st' -> st' 
                            in
                            let other_contin = match other_cont.continuation, hc.cont with
                              | None , StyTrue -> StyTrue
                              | Some st, StyTrue -> st
                              | Some st, st' -> StySeq (st, st')
                              | None, st' -> st' 
                            in


                            child_ev.session_type <- Some {protocol_node with d = own_contin};
                            
                            let child_other_branch = List.filter (fun b -> b.id <> child_ev.id) branches.owner_branch.branches_to in
                            if List.length child_other_branch = 1 then
                              let other_ev = List.hd child_other_branch in
                              Printf.eprintf "Assigning session type %s to other branch event %d\n"
                                (Lang.string_of_protocol other_contin) other_ev.id;
                              other_ev.session_type <- Some {protocol_node with d = other_contin};
                              Queue.add child_ev next_queue;
                              Queue.add other_ev next_queue

                    | ImmediateSend (msg,_) -> (
                        let found_hc_opt =
                          List.find_opt (fun hc ->
                            match hc.head with
                            | XOffers offerings | Offers offerings ->
                                List.for_all (fun offering ->
                                  match offering.trigger with
                                  | Lang.AtomicAct (Lang.AtomBMsg m) -> m.endpoint = msg.endpoint && m.msg = msg.msg
                                  | Lang.AtomicAct (Lang.AtomNBMsg m) ->m.endpoint = msg.endpoint && m.msg = msg.msg
                                  | Lang.AtomDelay _ -> true
                                  | _ -> false
                                ) offerings
                            | _ -> false
                          ) offer_atoms
                        in
                        if Option.is_none found_hc_opt then
                          error_handler g (Printf.sprintf "Expected Offerings for ImmediateRecv at event %d | However found %s"
                            child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name
                        else
                          let hc = Option.get found_hc_opt in
                          Printf.eprintf "Found matching head-continuation for ImmediateSend at event %d: %s\n"
                            child_ev.id (print_string_of_head_cont_pair hc);
                          List.iter (fun h ->
                            if h = hc then h.visited <- true
                          ) head_conts;
                          let cont = match hc.head with
                            | XOffers offerings | Offers offerings -> offerings
                            | _ -> []
                          in
                          if List.length cont > 2 then
                            error_handler g (Printf.sprintf "Multiple matching offerings for ImmediateRecv at event %d"
                              child_ev.id) g.thread_codespan module_name
                          else
                            let own_cont, other_cont = if (List.nth cont 0 ).trigger = Lang.AtomicAct (Lang.AtomBMsg msg)
                              || (List.nth cont 0 ).trigger = Lang.AtomicAct (Lang.AtomNBMsg msg) then
                                (List.nth cont 0, List.nth cont 1)
                              else
                                (List.nth cont 1, List.nth cont 0)
                              in
                             let own_contin = match own_cont.continuation, hc.cont with
                              | None , StyTrue -> StyTrue
                              | Some st, StyTrue -> st
                              | Some st, st' -> StySeq (st, st')
                              | None, st -> st
                            in
                            let other_contin = match other_cont.continuation, hc.cont with
                              | Some st, StyTrue -> st
                              | Some st, st' -> StySeq (st, st')
                              | None, st -> st
                            in
                            
                            child_ev.session_type <- Some {protocol_node with d = own_contin};
                            let child_other_branch = List.filter (fun b -> b.id <> child_ev.id) branches.owner_branch.branches_to in

                            if List.length child_other_branch = 1 then
                              let other_ev = List.hd child_other_branch in
                              Printf.eprintf "Assigning session type %s to other branch event %d\n"
                                (Lang.string_of_protocol other_contin) other_ev.id;
                              other_ev.session_type <- Some {protocol_node with d = other_contin};
                              Queue.add child_ev next_queue;
                              Queue.add other_ev next_queue

                    )

                    | _ -> ()
                  ) has_immediate_actions
                end
                else if not is_empty_branch then
                  (
                  child_ev.session_type <- Some {protocol_node with d = current_sty} ;
                  Queue.add child_ev next_queue
                  )
                else begin
                  let found = List.exists (fun hc ->
                    match hc.head with
                    | Terminal ->
                        child_ev.session_type <- Some {protocol_node with d = hc.cont};
                        hc.visited <- true;
                        true
                    | _ -> false
                  ) head_conts in
                  if not found then
                    error_handler g (Printf.sprintf "Expected Terminal at event %d | However found %s"
                      child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name      
                    ;
                  Queue.add child_ev next_queue
              end;

            end;    
                
            | `Later (ev_a, ev_b) ->
              let all_parents_reached = match ev_a.session_type, ev_b.session_type with
                | Some _, Some _ -> true
                | _ -> false
              in
              if not all_parents_reached then begin
                ()
              end
              else
                (
                  (match ev_a.session_type, ev_b.session_type with
                  | Some sty_a_node, Some sty_b_node ->
                    let hd_cont_a = get_head_continuation_pair sty_a_node.d g.thread_codespan in
                    let hd_cont_b = get_head_continuation_pair sty_b_node.d g.thread_codespan in
                    let cont_a = List.find_opt (
                      fun hc -> match hc.head with
                        | Terminal -> true
                        | _ -> false
                    ) hd_cont_a in
                    let cont_b = List.find_opt (
                      fun hc -> match hc.head with
                        | Terminal -> true
                        | _ -> false
                    ) hd_cont_b in
                    (
                      match cont_a, cont_b with
                      | Some hc_a, Some hc_b ->
                          if hc_a.cont <> hc_b.cont then
                            error_handler g (Printf.sprintf "Mismatched session types at later event %d"
                              child_ev.id) g.thread_codespan module_name;
                            child_ev.session_type <- Some {protocol_node with d = hc_a.cont};
                      | _ ->
                        raise (Except.TypeError [
                          Text (Printf.sprintf "No terminal head-continuation found at later event %d"
                            child_ev.id);
                          Except.codespan_local g.thread_codespan
                        ])
                    )
                    | _ ->
                      raise (Except.TypeError [
                        Text (Printf.sprintf "Unexpected missing session type at later event %d"
                          child_ev.id);
                        Except.codespan_local g.thread_codespan
                      ])
                );

                Queue.add child_ev next_queue
              )
            | `Branch(_, branch) ->
              let all_branches_reached = List.for_all (fun b ->
                match b.session_type with
                | Some _ -> true
                | None -> false
              ) branch.branches_val in
              if not all_branches_reached then begin
                is_propogated := true;
              end
              else
                let true_cont_opt = List.find_opt(fun br ->
                  match br.session_type with
                  | Some _ -> true
                  | None -> false
                )branch.branches_val in

                let true_cont_node = match true_cont_opt with
                  | Some ev -> Option.get ev.session_type
                  | None ->
                      error_handler g (Printf.sprintf "No session types found in branches at event %d"
                        child_ev.id) g.thread_codespan module_name
                in
                List.iter (fun b ->
                  match b.session_type with
                  | Some sty ->
                      if sty.d <> true_cont_node.d then
                        error_handler g (Printf.sprintf "Mismatched session types in branch event %d"
                          child_ev.id) g.thread_codespan module_name
                  | None ->
                      error_handler g (Printf.sprintf "Missing session type in branch event %d"
                        b.id) g.thread_codespan module_name
                ) branch.branches_val;
                is_propogated := true;
                child_ev.session_type <- Some true_cont_node;
                if not (IntHashtbl.mem visited child_ev.id)then
                  Queue.add child_ev next_queue
                
            | _ ->
                error_handler g (Printf.sprintf "Unsupported child event source at event %d during generalized session type\n  check" child_ev.id) g.thread_codespan module_name
          ) child_events;

          List.iter (fun hc ->
            if not hc.visited && not hc.is_choice && not !is_propogated && not (hc.head = Terminal) then
              error_handler g (Printf.sprintf "No matching head-continuation found for event %d's children during generalized session type check | Head: %s | Cont: %s"
                ev.id (match hc.head with | Offers off -> string_of_protocol (StyOffer off) | Atom act -> string_of_atomic_action_with_gap act | Terminal  -> string_of_protocol StyTrue) (string_of_protocol hc.cont) ) g.thread_codespan module_name 
          ) head_conts;

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
