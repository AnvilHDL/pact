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
  recvar_map : (identifier * session_type) list;
}
let default_head_continuation_pair = {
  head = Atom (AtomicAct (AtomBMsg {endpoint = ""; msg = ""}));
  cont = StyTrue;
  visited = false;
  is_choice = false;
  recvar_map = [];
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

let rec remove_type_choice sty1 sty2 =
  (* remove sty2 from sty1 : as consumed *)
  match sty1 with
  | StyChoice (s1, s2) ->
      if s1 = sty2 then
        s2
      else if s2 = sty2 then
        s1
      else if s1 = StyTrue then
        s2
      else if s2 = StyTrue then
        s1
      else
        StyChoice (remove_type_choice s1 sty2, remove_type_choice s2 sty2)
      
  | StySeq (s1, s2) ->
      StySeq (remove_type_choice s1 sty2, s2)
  | _ -> sty1

let resolve_recvar (recvar_map : (identifier * session_type) list) sty =
  let rec aux seen st =
    match st with
    | StyVar id ->
        if List.mem id seen then
          st
        else
          (match List.find_opt (fun (var_id, _) -> var_id = id) recvar_map with
          | Some (_, bound_sty) -> aux (id :: seen) bound_sty
          | None -> st)
    | _ -> st
  in
  aux [] sty

let normalize_for_match (recvar_map : (identifier * session_type) list) sty =
  let rec aux st =
    let st' = resolve_recvar recvar_map st in
    match st' with
    | StySeq (head, tail) ->
        let head' = aux head in
        let tail' = aux tail in
        (match head', tail' with
        | StyTrue, tail'' -> tail''
        | head'', StyTrue -> head''
        | _ -> StySeq (head', tail'))
    | StyParallel (left, right) ->
        let left' = aux left in
        let right' = aux right in
        (match left', right' with
        | StyTrue, StyTrue -> StyTrue
        | StyTrue, right'' -> right''
        | left'', StyTrue -> left''
        | _ -> StyParallel (left', right'))
    | StyChoice (left, right) -> StyChoice (aux left, aux right)
    | _ -> st'
  in
  aux sty

let session_type_matches recvar_map lhs rhs =
  let lhs_norm = normalize_for_match recvar_map lhs in
  let rhs_norm = normalize_for_match recvar_map rhs in
  lhs_norm = rhs_norm
      
let event_has_immediate_session_action (ev : event) =
  List.exists (fun action ->
    match action.d with
    | ImmediateRecv _ | ImmediateSend _ -> true
    | _ -> false
  ) ev.actions

let msg_matches m1 m2 =
  m1.endpoint = m2.endpoint && m1.msg = m2.msg

let event_session_action_msgs (ev : event) =
  let immediate_msgs =
    List.filter_map (fun action ->
      match action.d with
      | ImmediateRecv msg | ImmediateSend (msg, _) -> Some msg
      | _ -> None
    ) ev.actions
  in
  let sustained_msgs =
    List.map (fun sustained_action ->
      match sustained_action.d.ty with
      | Send (msg, _) | Recv msg -> msg
    ) ev.sustained_actions
  in
  immediate_msgs @ sustained_msgs

let is_branch_root_of_parent (parent_ev : event) (child_ev : event) =
  match child_ev.source with
  | `Root (Some (branch_parent, _)) -> branch_parent.id = parent_ev.id
  | _ -> false

  

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
  
let  build_choice_from_offerings (offerings : offering_session_type list) =
  let rec aux offings =
    if List.length offings = 1 then
      let only = List.hd offings in
      match only.trigger with
      | Lang.AtomicAct trig ->
          (match only.continuation with
          | Some sty -> StyChoice(Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty), Lang.StyTrue)
          | None -> StyChoice(Lang.StyAtom (Lang.AtomicAct trig), Lang.StyTrue)
          )
      | _ -> 
        raise (Except.TypeError [
          Text "Unsupported offering trigger in build_choice_from_offerings | Should not happen";
        ])
    else
      let first = List.hd offings in
      let rest = List.tl offings in
      match first.trigger with
      | Lang.AtomicAct trig ->
          Lang.StyParallel(
            (match first.continuation with
            | Some sty -> StyChoice(Lang.StySeq(Lang.StyAtom (Lang.AtomicAct trig), sty), Lang.StyTrue)
            | None -> StyChoice(Lang.StyAtom (Lang.AtomicAct trig), Lang.StyTrue)
            ),
            aux rest
          )
      | _ -> raise (Except.TypeError [
          Text "Unsupported offering trigger in build_choice_from_offerings | Should not happen";
        ])
  in

  let offerings_list_filtered = List.filter (fun off ->
    match off.trigger with
    | Lang.AtomicAct (Lang.AtomBMsg _) -> true
    | Lang.AtomicAct (Lang.AtomNBMsg _) -> true
    | _ -> false
  ) offerings in 
  let wildcard = List.filter (fun off ->
    match off.trigger with
    | Lang.AtomDelay _ -> true
    | _ -> false
  ) offerings in

  let wildcard_cont = if List.length wildcard > 0 then Some (if Option.is_some ((List.hd wildcard).continuation) then Option.get ((List.hd wildcard).continuation) else StyTrue) else None in

  match wildcard_cont with
  | Some sty ->
      StyChoice(sty, aux offerings_list_filtered)
  | None -> aux offerings_list_filtered



let rec get_head_continuation_pair (sty_node : session_type) (sp : code_span) (rec_var_context : (identifier*session_type) list) : head_continuation_pair list =
  match sty_node with
  | StyAtom (AtomicAct act) -> [{default_head_continuation_pair with head = Atom (AtomicAct act); cont = StyTrue ; recvar_map = default_head_continuation_pair.recvar_map@rec_var_context}]
  | StyAtom (AtomDelay n) -> [{default_head_continuation_pair with head = Atom (AtomDelay n); cont = StyTrue; recvar_map = default_head_continuation_pair.recvar_map@rec_var_context}]
  | StySeq (s1, s2) -> (  
    let head_conts = get_head_continuation_pair s1 sp rec_var_context in
      List.map (fun hc ->
        {hc with cont = 
        (
          match hc.cont with
          | StyTrue -> s2
          | _ -> StySeq (hc.cont, s2)
        )
          ; recvar_map = hc.recvar_map @ rec_var_context
        }
      ) head_conts
    )
  | StyParallel (s1, s2) ->
  (
    match s1, s2 with
    | StyTrue, StyTrue -> [{default_head_continuation_pair with head = Terminal; cont = StyTrue; recvar_map = rec_var_context}]
    | _ ->
     (
      let head_conts1 = get_head_continuation_pair s1 sp rec_var_context in
      let head_conts2 = get_head_continuation_pair s2 sp rec_var_context in
      let has_same_hd hd_act other_pairs = List.exists (fun hc -> hc.head = hd_act) other_pairs in
      let head_conts_transform_1 = List.map (fun hc -> {hc with cont = if has_same_hd hc.head head_conts2 then StyParallel (hc.cont, s2) else hc.cont; recvar_map = hc.recvar_map @ rec_var_context}) head_conts1 in
      let head_conts_transform_2 = List.map (fun hc -> {hc with cont = if has_same_hd hc.head head_conts1 then StyParallel (s1, hc.cont) else hc.cont; recvar_map = hc.recvar_map @ rec_var_context}) head_conts2 in
      head_conts_transform_1 @ head_conts_transform_2
    )
  )
  | StyChoice (s1, s2) -> (
      let head_conts1 = get_head_continuation_pair s1 sp rec_var_context in
      let head_conts2 = get_head_continuation_pair s2 sp rec_var_context in
      List.map (fun hc -> {hc with is_choice = true; recvar_map = hc.recvar_map @ rec_var_context}) (head_conts1 @ head_conts2)
    )
  | StyFuture s -> 
    let head_conts = get_head_continuation_pair s sp rec_var_context in
    let possible_delay = {default_head_continuation_pair with head = Atom (AtomDelay 1); cont = StyFuture s; is_choice = true; recvar_map = rec_var_context} in
    possible_delay :: head_conts
  | StyXOffer offerings ->
      (* let continuation = build_choice_from_xofferings offerings in *)
      [{default_head_continuation_pair with head = XOffers offerings; cont = StyTrue; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StyOffer offerings ->
      (* let continuation = build_choice_from_offerings offerings in *)
      [{default_head_continuation_pair with head = Offers offerings; cont = StyTrue; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StyTrue -> [{default_head_continuation_pair with head = Terminal; cont = StyTrue; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StyRec(id,s') -> get_head_continuation_pair s' sp ((id, sty_node)::rec_var_context)
  | StyVar id -> 
    let sty' = List.filter_map (fun (var_id, var_sty) -> if var_id = id then Some var_sty else None) rec_var_context in
    (
    match sty' with
    | [sty''] -> [{default_head_continuation_pair with head = Terminal; cont = sty''; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
    | _ -> raise (Except.TypeError [
        Text (Printf.sprintf "Unbound or multiple bindings for recursive variable %s in head-continuation extraction" id);
        Except.codespan_local sp
      ])
    )
  | _ -> raise (Except.TypeError [
      Text (Printf.sprintf "Unsupported session type %s for head-continuation extraction"
        (Lang.string_of_protocol sty_node));
      Except.codespan_local sp
    ])

let restart_head_continuation_pairs protocol_sty sp =
  get_head_continuation_pair protocol_sty sp []
  |> List.map (fun hc -> {hc with is_choice = true})

let add_terminal_restart_heads protocol_sty sp recvar_map current_sty head_conts =
  if session_type_matches recvar_map current_sty StyTrue then
    head_conts @ restart_head_continuation_pairs protocol_sty sp
  else
    head_conts

let session_type_can_start_with_msg sp recvar_map sty msg =
  let rec search seen current_recvar_map current_sty =
    if List.mem current_sty seen then
      false
    else
      let heads = get_head_continuation_pair current_sty sp current_recvar_map in
      List.exists (fun hc ->
        match hc.head with
        | Atom (AtomicAct (AtomBMsg head_msg))
        | Atom (AtomicAct (AtomNBMsg head_msg)) ->
            msg_matches head_msg msg
        | Terminal ->
            search (current_sty :: seen) hc.recvar_map hc.cont
        | _ -> false
      ) heads
  in
  search [] recvar_map sty

let delay_continuation_after_terminal_closure protocol_sty n sp head_conts =
  let rec search seen hcs =
    List.find_map (fun hc ->
      match hc.head with
      | Atom (AtomDelay m) ->
          if n <= m then begin
            let remaining_delay = if n < m then StyAtom (AtomDelay (m - n)) else StyTrue in
            let new_cont = match remaining_delay with
              | StyTrue -> hc.cont
              | _ -> StySeq (remaining_delay, hc.cont)
            in
            hc.visited <- true;
            Some (new_cont, hc.recvar_map)
          end
          else None
      | Terminal ->
          if List.mem hc.cont seen then
            None
          else
            let cont_heads =
              get_head_continuation_pair hc.cont sp hc.recvar_map
              |> add_terminal_restart_heads protocol_sty sp hc.recvar_map hc.cont
            in
            (match search (hc.cont :: seen) cont_heads with
            | Some result ->
                hc.visited <- true;
                Some result
            | None -> None)
      | _ -> None
    ) hcs
  in
  search [] head_conts

(* Generalized session type checking : traverse event graph and assign types to node for successors based on edges *)
let check_generalized_session 
    (config : Config.compile_config) 
    (g : event_graph) 
    module_name =
  
  if Option.is_none g.interface_protocol then
      Printf.eprintf "[Warning] No interface protocol specified for thread %d in module %s, skipping check.\n " (g.thread_id+1) module_name
  
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
        (next_queue : (event * ((identifier*session_type) list)) Queue.t)
        (visited : bool IntHashtbl.t) =
      if Queue.is_empty next_queue then
        ()
      else
        let (ev : event), (rec_var_cont : (identifier*session_type) list) = Queue.pop next_queue in
        if IntHashtbl.mem visited ev.id || ev.is_recurse then
          (
            IntHashtbl.add visited ev.id true;
            generalized_session_judgement next_queue visited
          )
        else begin
          IntHashtbl.add visited ev.id true;

          (* Process current event *)

          let current_sty = match ev.session_type with
            | Some sty_node -> sty_node.d
            | None -> 
              let err_msg = Printf.sprintf 
                "Event %d has no session type assigned during generalized session type check" ev.id in
              error_handler g err_msg g.thread_codespan module_name
            in
          if config.verbose then
            Printf.eprintf "Processing event %d with session type %s\n"
              ev.id (Lang.string_of_protocol current_sty);

          let child_events = ev.outs in
          let head_conts =
            get_head_continuation_pair current_sty g.thread_codespan rec_var_cont
            |> add_terminal_restart_heads protocol_node.d g.thread_codespan rec_var_cont current_sty
          in
          if config.verbose then (
            Printf.eprintf "Extracted head-continuation pairs for event %d:\n" ev.id;
            List.iter (fun hc ->
              Printf.eprintf "  %s\n" (print_string_of_head_cont_pair hc)
            ) head_conts
          );
          let is_propogated = ref false in
          let mark_structural_propagation () = is_propogated := true in

          List.iter (fun child_ev ->
            match child_ev.session_type with
            | Some sty_node' -> 
              let should_skip_terminal_check =
                match child_ev.source with
                | `Branch _ -> true
                | _ when is_branch_root_of_parent ev child_ev -> true
                | _ -> false
              in
              if should_skip_terminal_check then
                mark_structural_propagation ()
              else begin
                let found = List.exists (fun hc ->
                  match hc.head with
                  | Terminal ->
                      if not hc.visited then begin
                        let cont = hc.cont in
                        if session_type_matches (hc.recvar_map @ rec_var_cont) sty_node'.d cont then(
                          hc.visited <- true;
                          true
                        )
                        else false
                      end
                      else false
                  | _ -> false
                )head_conts in
                if not found then
                  error_handler g (Printf.sprintf "Expected Terminal head-continuation for already assigned child event %d | However found %s"
                    child_ev.id (Lang.string_of_protocol sty_node'.d)) g.thread_codespan module_name
              end;
            | _ ->
              let rec assign_session_type src = 
              match src with
              | `Seq (_, `Choice msg_list) ->
                  
                  let found = List.fold_left (fun acc hc ->
                    match hc.head with
                    | Offers offerings ->
                        let msgs = msg_list in
                        let matches = match_offerings_with_msgs offerings msgs in
                        if matches then begin
                          let co = match hc.cont with 
                          |StyTrue -> build_choice_from_offerings offerings 
                          | _-> StySeq (build_choice_from_offerings offerings, hc.cont) 
                        in
                        let next_sty = match child_ev.session_type with
                        | Some sty' ->
                            StyChoice (sty'.d,co)
                        | None -> co
                        in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc@hc.recvar_map
                        end
                        else acc
                        
                    | XOffers offerings ->
                        let msgs = msg_list in
                        let matches = match_offerings_with_msgs offerings msgs in
                        if matches then begin
                          let co = match hc.cont with 
                          |StyTrue -> build_choice_from_xofferings offerings 
                          | _-> StySeq (build_choice_from_xofferings offerings, hc.cont) 
                        in
                          let next_sty = match child_ev.session_type with
                          | Some sty' ->
                              StyChoice (sty'.d,co)
                          | None -> co
                          in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc@hc.recvar_map
                        end
                        else acc
                    | _ -> acc
                  ) [] head_conts in 
                  if child_ev.session_type = None then
                    error_handler g (Printf.sprintf "Expected Offerings at event %d | However found %s"
                      child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                  if not (IntHashtbl.mem visited child_ev.id) then
                    Queue.add (child_ev, found) next_queue


              | `Seq (_, `Send msg) ->
                  let found = List.fold_left (fun acc hc ->
                    match hc.head with
                    | Atom (AtomicAct (AtomBMsg m)) ->
                        if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                          let next_sty = match child_ev.session_type with
                          | Some sty' ->
                              StyChoice (sty'.d, hc.cont)
                          | None -> hc.cont
                          in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc @ hc.recvar_map
                        end
                        else acc
                    | Atom (AtomicAct (AtomNBMsg m)) ->
                        if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                          let next_sty = match child_ev.session_type with
                          | Some sty' ->
                              StyChoice (sty'.d, hc.cont)
                          | None -> hc.cont
                            in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc @ hc.recvar_map
                        end
                        else acc                    
                    | __ -> acc
                  ) [] head_conts in

                  if child_ev.session_type = None then
                    error_handler g (Printf.sprintf "Expected Send message (%s) at event %d | However found %s"
                    (string_of_msg_spec msg) child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                  if not (IntHashtbl.mem visited child_ev.id) then
                    Queue.add (child_ev, found) next_queue
                    
                    
              | `Seq (_, `Recv msg) ->
                  let found = List.fold_left (fun acc hc ->
                    match hc.head with
                    | Atom (AtomicAct (AtomBMsg m)) ->
                        if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                          let next_sty = match child_ev.session_type with
                          | Some sty' ->
                              StyChoice (sty'.d, hc.cont)
                          | None -> hc.cont
                            in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc @ hc.recvar_map
                        end
                        else acc
                    | Atom (AtomicAct (AtomNBMsg m)) ->
                        if m.endpoint = msg.endpoint && m.msg = msg.msg then begin
                          let next_sty = match child_ev.session_type with
                          | Some sty' ->
                              StyChoice (sty'.d, hc.cont)
                          | None -> hc.cont
                            in
                          child_ev.session_type <- Some {protocol_node with d = next_sty};
                          hc.visited <- true;
                          acc @ hc.recvar_map
                        end
                        else acc
                    | __ -> acc
                  ) [] head_conts in

                  if child_ev.session_type = None then
                    error_handler g (Printf.sprintf "Expected Recv message at event %d | However found %s"
                        child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                  if not (IntHashtbl.mem visited child_ev.id) then
                    Queue.add (child_ev, found) next_queue
              | `Seq (_, `Cycles n) ->
                let found = match delay_continuation_after_terminal_closure protocol_node.d n g.thread_codespan head_conts with
                  | Some (new_cont, found_map) ->
                      let next_sty = match child_ev.session_type with
                        | Some sty' -> StyChoice (sty'.d, new_cont)
                        | None -> new_cont
                      in
                      child_ev.session_type <- Some {protocol_node with d = next_sty};
                      found_map
                  | None -> []
                in
                if child_ev.session_type = None then 
                  error_handler g (Printf.sprintf "Expected Delay at event %d | However found %s"
                    child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name;
                if not (IntHashtbl.mem visited child_ev.id) then
                  Queue.add (child_ev, found) next_queue
              | `Root Some (_, branches) ->
                if Option.is_none child_ev.session_type then begin
                  let is_empty_branch = List.for_all( fun e ->
                    match e.source with
                    | `Branch _ -> true
                    | _ -> false
                  )child_ev.outs in
                  let all_branches_empty = List.for_all (fun ex -> 
                    List.for_all (fun e ->
                      match e.source with
                      | `Branch _ -> true
                      | _ -> false
                    ) ex.outs
                  ) branches.owner_branch.branches_to in
          
                  let has_immediate_actions = List.filter ( fun a ->
                    match a.d with
                    | ImmediateRecv _ | ImmediateSend _ -> true
                    | _ -> false
                  ) child_ev.actions in
                  let has_immediate_sibling =
                    List.exists (fun sibling_ev ->
                      sibling_ev.id <> child_ev.id
                      && event_has_immediate_session_action sibling_ev
                    ) branches.owner_branch.branches_to
                  in
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
                            (* Printf.eprintf "Found matching head-continuation for ImmediateRecv at event %d: %s\n"
                              child_ev.id (print_string_of_head_cont_pair hc); *)
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
                                (* Printf.eprintf "Assigning session type %s to other branch event %d\n"
                                  (Lang.string_of_protocol other_contin) other_ev.id; *)
                                other_ev.session_type <- Some {protocol_node with d = other_contin};
                                Queue.add (child_ev, hc.recvar_map) next_queue;
                                Queue.add (other_ev, hc.recvar_map) next_queue

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
                            (* Printf.eprintf "Found matching head-continuation for ImmediateSend at event %d: %s\n"
                              child_ev.id (print_string_of_head_cont_pair hc); *)
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
                                (* Printf.eprintf "Assigning session type %s to other branch event %d\n"
                                  (Lang.string_of_protocol other_contin) other_ev.id; *)
                                other_ev.session_type <- Some {protocol_node with d = other_contin};
                                Queue.add (child_ev, hc.recvar_map) next_queue;
                                Queue.add (other_ev, hc.recvar_map) next_queue

                      )

                      | _ -> ()
                    ) has_immediate_actions
                  end
                  else if has_immediate_sibling then
                    mark_structural_propagation ()
                  else if (not is_empty_branch) || all_branches_empty then
                    (
                    mark_structural_propagation ();
                    child_ev.session_type <- Some {protocol_node with d = current_sty} ;
                    Queue.add (child_ev, rec_var_cont) next_queue
                    )
                  else begin
                    let sibling_action_msgs =
                      branches.owner_branch.branches_to
                      |> List.filter (fun sibling_ev -> sibling_ev.id <> child_ev.id)
                      |> List.concat_map event_session_action_msgs
                    in
                    let terminal_matches_branch hc =
                      match hc.head with
                      | Terminal ->
                          not hc.visited
                          && List.for_all (fun msg ->
                            not (session_type_can_start_with_msg g.thread_codespan hc.recvar_map hc.cont msg)
                          ) sibling_action_msgs
                      | _ -> false
                    in
                    let found = match List.find_opt (fun hc ->
                      if sibling_action_msgs = [] then
                        match hc.head with
                        | Terminal -> not hc.visited
                        | _ -> false
                      else
                        terminal_matches_branch hc
                    ) head_conts with
                    | Some hc ->
                            (* Printf.eprintf "Assigning Terminal continuation = %s to empty branch event %d\n" *)
                              (* (Lang.string_of_protocol hc.cont) child_ev.id; *)
                            child_ev.session_type <- Some {protocol_node with d = hc.cont};                              
                            hc.visited <- true;
                            let other_side_remaining_type = remove_type_choice current_sty hc.cont in
                            let other_child_branch = List.filter (fun b -> b.id <> child_ev.id) branches.owner_branch.branches_to in
                            List.iter (fun ob ->
                                (* Printf.eprintf "Assigning remaining choice continuation = %s to other branch event %d\n" *)
                                (* (Lang.string_of_protocol other_side_remaining_type) ob.id; *)
                              ob.session_type <- Some {protocol_node with d = other_side_remaining_type};
                              (* Printf.eprintf "Adding other branch event %d to queue | for empty branch %d\n" ob.id child_ev.id; *)
                              Queue.add (ob, hc.recvar_map) next_queue
                            ) other_child_branch;           
                            hc.recvar_map
                    | None -> [] in
                    if child_ev.session_type = None then
                      error_handler g (Printf.sprintf "Expected Terminal at event %d | However found %s"
                        child_ev.id (Lang.string_of_protocol current_sty)) g.thread_codespan module_name      
                      ;
                    if not (IntHashtbl.mem visited child_ev.id) then
                      Queue.add (child_ev, found) next_queue
                end;

              end;    
                  
              | `Later (ev_a, ev_b) ->
                (match ev_a.session_type, ev_b.session_type with
                  | Some sty_a_node, Some sty_b_node ->
                    let hd_cont_a = get_head_continuation_pair sty_a_node.d g.thread_codespan [] in
                    let hd_cont_b = get_head_continuation_pair sty_b_node.d g.thread_codespan [] in
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
                    
                      let match_cont_later sty1 sty2 = 
                        if sty1 = sty2 then begin
                          sty1
                        end
                        else begin
                          match sty1, sty2 with
                          | StySeq(StyParallel(StyTrue,StyTrue), s1), sty2 when s1 = sty2 -> StySeq(StyTrue, sty2)
                          | sty1, StySeq(StyParallel(StyTrue, StyTrue), s2) when sty1 = s2 -> StySeq(StyTrue, sty1)
                          | _ -> 
                            error_handler g (Printf.sprintf "Mismatched session types at later event %d | Types: %s vs %s"
                              child_ev.id (Lang.string_of_protocol sty1) (Lang.string_of_protocol sty2)) g.thread_codespan module_name;
                        end in

                      (match cont_a, cont_b with
                      | Some hc_a, Some hc_b ->
                        let new_cont = match_cont_later hc_a.cont hc_b.cont in
                        let merged_recvar_map = hc_a.recvar_map @ hc_b.recvar_map in
                          child_ev.session_type <- Some {protocol_node with d = new_cont};
                          Queue.add (child_ev, merged_recvar_map) next_queue
                      | _ ->
                        raise (Except.TypeError [
                          Text (Printf.sprintf "No terminal head-continuation found at later event %d | hc = \n%s"
                            child_ev.id (String.concat "\n" (List.map print_string_of_head_cont_pair head_conts)));
                          Except.codespan_local g.thread_codespan
                        ])
                      )
                  | _ -> ()  (* Wait for both parent events to be processed *)
                )
              | `Branch(_, branch) ->
                let all_branches_reached = List.for_all (fun b ->
                  match b.session_type with
                  | Some _ -> true
                  | None -> false
                ) branch.branches_val in
                if not all_branches_reached then begin
                  mark_structural_propagation ();
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
                  let true_node = match true_cont_node.d with
                  | StySeq(StyTrue, cont) -> cont
                  | _ -> true_cont_node.d
                  in
                  let branch_types =
                    List.map (fun b ->
                      match b.session_type with
                      | Some sty -> sty
                      | None ->
                          error_handler g (Printf.sprintf "Missing session type in branch event %d"
                            b.id) g.thread_codespan module_name
                    ) branch.branches_val
                  in
                  let branch_types_match =
                    List.for_all (fun sty ->
                      session_type_matches rec_var_cont sty.d true_node
                    ) branch_types
                  in
                  let branch_guards_session_action =
                    List.exists (fun branch_root ->
                      event_session_action_msgs branch_root <> []
                    ) branch.branches_to
                  in
                  let has_completed_branch =
                    List.exists (fun sty ->
                      session_type_matches rec_var_cont sty.d StyTrue
                    ) branch_types
                  in
                  let merged_branch_type =
                    if branch_types_match then
                      true_cont_node
                    else if branch_guards_session_action && has_completed_branch then
                      {protocol_node with d = StyTrue}
                    else
                      error_handler g (Printf.sprintf "Mismatched session types in branch event %d"
                        child_ev.id) g.thread_codespan module_name
                  in
                  mark_structural_propagation ();
                  child_ev.session_type <- Some merged_branch_type;
                  if not (IntHashtbl.mem visited child_ev.id)then
                    Queue.add (child_ev, rec_var_cont) next_queue
              | `Recurse(src',_) ->
                assign_session_type src';
              | _ ->
                  error_handler g (Printf.sprintf "Unsupported child event source at event %d during generalized session type\n  check" child_ev.id) g.thread_codespan module_name

              in 
              assign_session_type child_ev.source
          ) child_events;

          List.iter (fun hc ->
            if not hc.visited && not hc.is_choice && not !is_propogated && not (hc.head = Terminal) then
              error_handler g (Printf.sprintf "No matching head-continuation found for event %d's children during generalized session type check | Head: %s | Cont: %s"
                ev.id (match hc.head with | XOffers off | Offers off -> string_of_protocol (StyOffer off) | Atom act -> string_of_atomic_action_with_gap act | Terminal  -> string_of_protocol StyTrue) (string_of_protocol hc.cont) ) g.thread_codespan module_name 
          ) head_conts;

          generalized_session_judgement next_queue visited
        end
    in


    let visited_tbl = IntHashtbl.create (List.length g.events) in
    let q = Queue.create () in
    let root_ev = List.find (fun e -> e.source = `Root None) g.events in

    root_ev.session_type <- Some protocol_node;
Queue.add (root_ev, []) q;
    
    generalized_session_judgement q visited_tbl;
    let file_name = Printf.sprintf "%sgraph.dot" module_name in
    let file_handler = Out_channel.open_text file_name in
    EventGraphOps.print_graph_with_session_types g file_handler;
    Out_channel.close file_handler
    
    (* Output final graph with annotated session types *)
