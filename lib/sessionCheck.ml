open Lang
open EventGraph

module IntHashtbl = Hashtbl.Make(Int)


type big_atomic_action =
  | Atom of atomic_action_with_gap
  | Offers of offering_session_type list
  | XOffers of offering_session_type list
  | Terminal of terminal_kind

and terminal_kind =
  | ParallelDone
  | RecurseJump

type head_continuation_pair = {
  head : big_atomic_action;
  cont : session_type option;
  mutable visited : bool;
  is_choice : bool;
  is_parallel : bool;
  recvar_map : (identifier * session_type) list;
}
let default_head_continuation_pair = {
  head = Atom (AtomicAct (AtomBMsg {endpoint = ""; msg = ""}));
  cont = None;
  visited = false;
  is_choice = false;
  is_parallel = false;
  recvar_map = [];
}

let print_string_of_head_cont_pair hc =
  let head_str = match hc.head with
    | Atom act -> string_of_atomic_action_with_gap act
    | Offers off -> string_of_protocol (StyOffer off)
    | XOffers xoff -> string_of_protocol (StyXOffer xoff)
    | Terminal ParallelDone -> string_of_protocol StySkip
    | Terminal RecurseJump -> "recurse"
  in
  let cont_str = match hc.cont with
    | Some sty -> string_of_protocol sty
    | None -> "<>"
  in
  let tags =
    [ (hc.is_choice, "choice"); (hc.is_parallel, "parallel") ]
    |> List.filter_map (fun (enabled, tag) -> if enabled then Some tag else None)
  in
  let tag_str =
    match tags with
    | [] -> ""
    | _ -> Printf.sprintf " | Tags: %s" (String.concat "," tags)
  in
  Printf.sprintf "[Head: %s | Cont: %s%s]" head_str cont_str tag_str

let is_terminal_head = function
  | Terminal _ -> true
  | _ -> false

(* Helper functions for session type judgements *)

let wildcard_msg_spec = {endpoint = "*"; msg = "*"}

let msg_spec_equal a b =
  a.endpoint = b.endpoint && a.msg = b.msg

let same_msg_spec_set a b =
  let normalize = List.sort_uniq Stdlib.compare in
  normalize a = normalize b

let msg_spec_of_atomic_action = function
  | Lang.AtomBMsg m | Lang.AtomNBMsg m -> m

let is_blocking_atomic_action = function
  | Lang.AtomBMsg _ -> true
  | Lang.AtomNBMsg _ -> false

(* [AtomBMsg] describes a blocking action, [AtomNBMsg] an instantaneous one. *)
let atomic_action_matches_kind (kind : Lang.handshake_kind) = function
  | Lang.AtomBMsg _ -> kind = Lang.Blocking
  | Lang.AtomNBMsg _ -> kind = Lang.Instant

let string_of_handshake_kind = function
  | Lang.Blocking -> "blocking"
  | Lang.Instant -> "instantaneous"

let trigger_msg_group = function
  | Lang.AtomicAct act -> Some [msg_spec_of_atomic_action act]
  | Lang.AtomConjunction acts -> Some (List.map msg_spec_of_atomic_action acts)
  | Lang.AtomDelay _ -> Some [wildcard_msg_spec]
  | Lang.AtomTerminal _ -> None

(* When [kind] is given, the trigger's blocking-ness must agree with it. *)
let trigger_matches_msg ?kind trigger msg =
  let kind_ok =
    match kind, trigger with
    | None, _ -> true
    | Some k, Lang.AtomicAct act -> atomic_action_matches_kind k act
    | Some k, Lang.AtomConjunction acts ->
      List.for_all (atomic_action_matches_kind k) acts
    | Some _, _ -> true
  in
  kind_ok &&
  (match trigger_msg_group trigger with
   | Some msgs -> List.exists (msg_spec_equal msg) msgs
   | None -> false)

let trigger_matches_msg_group trigger msg_group =
  match trigger_msg_group trigger with
  | Some trigger_group -> same_msg_spec_set trigger_group msg_group
  | None -> false

let session_of_atomic_actions actions =
  match actions with
  | [] -> StySkip
  | first :: rest ->
      List.fold_left (fun acc act ->
        StyParallel (acc, StyAtom (AtomicAct act))
      ) (StyAtom (AtomicAct first)) rest

let seq_if_needed head cont =
  match head, cont with
  | StySkip, cont -> cont
  | head, StySkip -> head
  | _ -> StySeq (head, cont)

type session_residual = session_type option

let residual_with_head head cont : session_residual =
  match head, cont with
  | StySkip, None -> None
  | StySkip, Some cont -> Some cont
  | head, Some cont -> Some (seq_if_needed head cont)
  | head, None -> Some head

let continuation_or_true = function
  | Some sty -> sty
  | None -> StySkip

let offering_body_session (offering : offering_session_type) =
  match offering.trigger with
  | Lang.AtomicAct act ->
      seq_if_needed (StyAtom (AtomicAct act)) (continuation_or_true offering.continuation)
  | Lang.AtomConjunction actions ->
      let all_blocking = List.for_all is_blocking_atomic_action actions in
      let all_nonblocking = List.for_all (fun act -> not (is_blocking_atomic_action act)) actions in
      if not (all_blocking || all_nonblocking) then
        raise (Except.TypeError [Text "Mixed blocking and non-blocking actions in conjunctive offering"]);
      seq_if_needed (session_of_atomic_actions actions) (continuation_or_true offering.continuation)
  | Lang.AtomDelay _ | Lang.AtomTerminal _ ->
      continuation_or_true offering.continuation

let rec build_choice_from_xofferings offerings =
  match offerings with
  | [] -> StySkip
  | [only] -> offering_body_session only
  | first :: rest ->
      StyChoice (offering_body_session first, build_choice_from_xofferings rest)

let offering_session_after_msg ?kind (offering : offering_session_type) msg =
  let act_matches act =
    msg_spec_equal (msg_spec_of_atomic_action act) msg
    && (match kind with
        | None -> true
        | Some k -> atomic_action_matches_kind k act)
  in
  match offering.trigger with
  | Lang.AtomicAct act when act_matches act ->
      Some offering.continuation
  | Lang.AtomConjunction actions ->
      let matching, remaining =
        List.partition act_matches actions
      in
      if matching = [] then
        None
      else
        let remaining_session =
          match remaining with
          | [] -> StySkip
          | _ -> session_of_atomic_actions remaining
        in
        Some (residual_with_head remaining_session offering.continuation)
  | _ -> None

(* Match offerings with messages *)
(* [kind] is the handshake of the offer/xoffer in the event graph; when given,
   each matching offering's blocking-ness must agree with it. *)
let match_offerings_with_msgs ?kind
    (offerings : offering_session_type list)
    (msg_groups : Lang.message_specifier list list) : bool =
    let kind_ok trigger =
      match kind, trigger with
      | None, _ -> true
      | Some k, Lang.AtomicAct act -> atomic_action_matches_kind k act
      | Some k, Lang.AtomConjunction acts ->
        List.for_all (atomic_action_matches_kind k) acts
      | Some _, _ -> true
    in
    List.for_all (fun msg_group ->
      List.exists (fun offering ->
        kind_ok offering.trigger &&
        (match trigger_msg_group offering.trigger with
         | Some offering_group -> same_msg_spec_set offering_group msg_group
         | None -> false)
      ) offerings
    ) msg_groups

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
        | StySkip, tail'' -> tail''
        | head'', StySkip -> head''
        | _ -> StySeq (head', tail'))
    | StyParallel (left, right) ->
        let left' = aux left in
        let right' = aux right in
        (match left', right' with
        | StySkip, StySkip -> StySkip
        | StySkip, right'' -> right''
        | left'', StySkip -> left''
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

let event_session_action_msgs (ev : event) =
  let immediate_msgs =
    List.filter_map (fun action ->
      match action.d with
      | ImmediateRecv (msg, _) | ImmediateSend (msg, _, _) -> Some msg
      | _ -> None
    ) ev.actions
  in
  let sustained_msgs =
    List.map (fun sustained_action ->
      match sustained_action.d.ty with
      | Send (msg, _, _) | Recv (msg, _) -> msg
    ) ev.sustained_actions
  in
  let source_msgs =
    match ev.source with
    | `Seq (_, `Send (msg, _)) | `Seq (_, `Recv (msg, _)) -> [msg]
    | _ -> []
  in
  immediate_msgs @ sustained_msgs @ source_msgs

(* Error handler that outputs the graph with session types before raising error *)
let error_handler g err_msg err_span module_name  =
  Printf.eprintf "\nPrinting file %s with session types for debugging...\n" module_name;
  let file_handler = Out_channel.open_text (Printf.sprintf "%s_error.dot" module_name) in
  EventGraphOps.print_graph_with_session_types g file_handler;
  Out_channel.close file_handler;

  raise (Except.TypeError [
    Text "Session type violation: ";
    Text err_msg;
    Except.codespan_local err_span
  ])
  
    

let seq_of_sty_opt sty_opt cont_opt =
  match sty_opt, cont_opt with
  | Some sty, Some cont -> Some (StySeq (sty, cont))
  | None, Some cont -> Some cont
  | Some sty, None -> Some sty
  | None, None -> None

let string_of_residual = function
  | Some sty -> string_of_protocol sty
  | None -> "<>"

let residual_to_choice_arm = function
  | Some sty -> sty
  | None -> StySkip

let choice_of_residuals lhs rhs =
  Some (StyChoice (residual_to_choice_arm lhs, residual_to_choice_arm rhs))

let residual_of_head_cont hc =
  let head_sty =
    match hc.head with
    | Atom act -> Some (StyAtom act)
    | Offers offerings -> Some (StyOffer offerings)
    | XOffers offerings -> Some (StyXOffer offerings)
    | Terminal ParallelDone -> Some StySkip
    | Terminal RecurseJump -> None
  in
  match head_sty, hc.cont with
  | Some head, cont -> residual_with_head head cont
  | None, cont -> cont

let parallel_of_residuals residuals =
  let sessions =
    List.filter_map (function
      | None -> None
      | Some StySkip -> None
      | Some sty -> Some sty
    ) residuals
  in
  match sessions with
  | [] -> None
  | first :: rest ->
      Some (List.fold_left (fun acc sty -> StyParallel (acc, sty)) first rest)

let offerings_of_head = function
  | Offers offerings | XOffers offerings -> Some offerings
  | _ -> None

let choice_residual_for_head ?kind msg_list hc =
  match hc.head with
  | Offers offerings when match_offerings_with_msgs ?kind offerings msg_list ->
      Some (residual_of_head_cont hc)
  | XOffers offerings when match_offerings_with_msgs ?kind offerings msg_list ->
      Some (seq_of_sty_opt (Some (build_choice_from_xofferings offerings)) hc.cont)
  | _ -> None

let head_matches_offer_choice ?kind msg_list hc =
  match choice_residual_for_head ?kind msg_list hc with
  | Some _ -> true
  | None -> false

let choice_msg_lists_of_children child_events =
  List.filter_map (fun child_ev ->
    match child_ev.source with
    | `Seq (_, `Choice (msg_list, _)) -> Some msg_list
    | _ -> None
  ) child_events

let residual_for_non_choice_heads current_residual recvars choice_msg_lists head_conts =
  match choice_msg_lists with
  | [] -> (current_residual, recvars)
  | _ ->
      let is_choice_head hc =
        List.exists (fun msg_list -> head_matches_offer_choice msg_list hc)
          choice_msg_lists
      in
      let non_choice_heads =
        List.filter (fun hc ->
          (not (is_choice_head hc)) && not (is_terminal_head hc.head)
        ) head_conts
      in
      ( parallel_of_residuals (List.map residual_of_head_cont non_choice_heads),
        List.concat (List.map (fun hc -> hc.recvar_map) non_choice_heads) )

let rec normalize_residual_for_match recvar_map sty =
  let sty' = resolve_recvar recvar_map sty in
  match sty' with
  | StySeq (left, right) ->
      seq_if_needed
        (normalize_residual_for_match recvar_map left)
        (normalize_residual_for_match recvar_map right)
  | StyParallel (left, right) ->
      StyParallel
        ( normalize_residual_for_match recvar_map left,
          normalize_residual_for_match recvar_map right )
  | StyChoice (left, right) ->
      let left = normalize_residual_for_match recvar_map left in
      let right = normalize_residual_for_match recvar_map right in
      if left = right then left else StyChoice (left, right)
  | _ -> sty'


let combine_offering_continuation offering_cont head_cont =
  seq_of_sty_opt offering_cont head_cont

let node_of_residual protocol_node = function
  | Some sty -> Some {protocol_node with d = sty}
  | None -> None

let rec consume_parallel_done_from_sty = function
  | StySkip -> Some None
  | StySeq (StySkip, tail) -> Some (Some tail)
  | StySeq (head, tail) ->
      (match consume_parallel_done_from_sty head with
      | Some None -> Some (Some tail)
      | Some (Some head') -> Some (Some (StySeq (head', tail)))
      | None -> None)
  | _ -> None

let consume_parallel_done_marker = function
  | Some sty -> consume_parallel_done_from_sty sty
  | None -> None

let rec strip_parallel_done_markers residual =
  match consume_parallel_done_marker residual with
  | Some next_residual -> strip_parallel_done_markers next_residual
  | None -> residual

let residual_matches recvar_map lhs rhs init_ty =
  match strip_parallel_done_markers lhs, strip_parallel_done_markers rhs with
  | None, None -> true
  | Some lhs_sty, Some rhs_sty ->
      normalize_residual_for_match recvar_map lhs_sty
      = normalize_residual_for_match recvar_map rhs_sty
  | Some lhs_sty, None when lhs_sty = init_ty  -> true
  | None, Some rhs_sty when rhs_sty = init_ty -> true
  | _ -> false

let rec get_head_continuation_pair
    ?(inside_parallel=false)
    (sty_node : session_type)
    (sp : code_span)
    (rec_var_context : (identifier*session_type) list) : head_continuation_pair list =
  match sty_node with
  | StyAtom (AtomicAct act) ->
      [{default_head_continuation_pair with head = Atom (AtomicAct act); cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map@rec_var_context}]
  | StyAtom (AtomConjunction acts) ->
      [{default_head_continuation_pair with head = Atom (AtomConjunction acts); cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map@rec_var_context}]
  | StyAtom (AtomDelay n) ->
      [{default_head_continuation_pair with head = Atom (AtomDelay n); cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map@rec_var_context}]
  | StySeq (s1, s2) -> (  
    let head_conts = get_head_continuation_pair ~inside_parallel s1 sp rec_var_context in
      List.map (fun hc ->
        {hc with cont = seq_of_sty_opt hc.cont (Some s2)}
      ) head_conts
    )
  | StyParallel (s1, s2) ->
  (
    match s1, s2 with
    | StySkip, StySkip -> [{default_head_continuation_pair with head = Terminal ParallelDone; cont = None; recvar_map = rec_var_context}]
    | _ ->
     (
      let head_conts1 =
        get_head_continuation_pair ~inside_parallel:true s1 sp rec_var_context
      in
      let head_conts2 =
        get_head_continuation_pair ~inside_parallel:true s2 sp rec_var_context
      in
      (* let has_same_hd hd_act other_pairs = List.exists (fun hc -> hc.head = hd_act) other_pairs in *)
      let head_conts_transform_1 =
        List.map
          (fun hc ->
            {hc with cont = seq_of_sty_opt hc.cont (Some StySkip)})
          head_conts1
      in
      let head_conts_transform_2 =
        List.map
          (fun hc ->
            {hc with cont = seq_of_sty_opt hc.cont (Some StySkip)})
          head_conts2
      in
      head_conts_transform_1 @ head_conts_transform_2
    )
  )
  | StyChoice (s1, s2) -> (
      let head_conts1 = get_head_continuation_pair ~inside_parallel s1 sp rec_var_context in
      let head_conts2 = get_head_continuation_pair ~inside_parallel s2 sp rec_var_context in
      List.map (fun hc -> {hc with is_choice = true}) (head_conts1 @ head_conts2)
    )
  | StyFuture s -> 
    let head_conts = get_head_continuation_pair ~inside_parallel s sp rec_var_context in
    let possible_delay = {default_head_continuation_pair with head = Atom (AtomDelay 1); cont = Some (StyFuture s); is_choice = true; is_parallel = inside_parallel; recvar_map = rec_var_context} in
    let head_conts_transform = List.map (fun hc -> {hc with is_choice = true}) head_conts in
    possible_delay :: head_conts_transform
  | StyXOffer offerings ->
      [{default_head_continuation_pair with head = XOffers offerings; cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StyOffer offerings ->
      [{default_head_continuation_pair with head = Offers offerings; cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StySkip -> [{default_head_continuation_pair with head = Terminal ParallelDone; cont = None; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
  | StyRec(id,s') -> get_head_continuation_pair ~inside_parallel s' sp ((id, sty_node)::rec_var_context)
  | StyVar id -> 
    (
    match List.find_opt (fun (var_id, _) -> var_id = id) rec_var_context with
    | Some (_, sty'') -> [{default_head_continuation_pair with head = Terminal RecurseJump; cont = Some sty''; is_parallel = inside_parallel; recvar_map = default_head_continuation_pair.recvar_map @ rec_var_context}]
    | _ -> raise (Except.TypeError [
        Text (Printf.sprintf "Unbound recursive variable %s in head-continuation extraction" id);
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


let add_delay n_opt offset=
  match n_opt,offset with
  | Some n, Some o -> Some (n + o)
  | _ -> None



let gt n1_opt n2_opt =
  match n1_opt, n2_opt with
  | Some n1, Some n2 -> n1 > n2
  | None , _ -> true
  | _ , None -> false

let get_max n1_opt n2_opt =
  match n1_opt, n2_opt with
  | Some n1, Some n2 -> Some (max n1 n2)
  |_ -> None

let get_min n1_opt n2_opt =
  match n1_opt, n2_opt with
  | Some n1, Some n2 -> Some (min n1 n2)
  | Some n, None | None, Some n -> Some n
  | None, None -> None

let lt n1_opt n2_opt =
  match n1_opt, n2_opt with
  | Some n1, Some n2 -> n1 < n2
  | None , _ -> false
  | _ , None -> true


let create_cont del bound cont =
  match del, bound with
  | Some d, Some b when d < b -> seq_of_sty_opt (Some (StyAtom (AtomDelay (b - d)))) cont
  | Some _, None -> cont
  | None, None -> cont
  | _ -> raise (Except.TypeError [Text "Invalid delay comparison in continuation creation"])

let choice_of_sty_opt sty_opt cont_opt =
  match sty_opt, cont_opt with
  | Some sty, Some cont -> Some (StyChoice (sty, cont))
  | Some sty, None -> Some sty
  | None, Some cont -> Some cont
  | None, None -> None

let extract_delay_continuation init n' hc =
  let rec extract_delay st' acc =
  match st' with
  |Some st -> (
    match st with
    | StyAtom(AtomDelay n) ->  ((add_delay (Some n) acc),None)
    | StyAtom(_) ->  (acc, Some st)
    | StySeq(s1,s2) -> (
      match extract_delay (Some s1) acc with
      | (acc', None) -> let del, cont = extract_delay (Some s2) acc' in (del, cont)
      | (acc', cont) -> (acc', seq_of_sty_opt cont (Some s2))
    )
    | StyParallel(s1,s2) -> (
      let del1, cont1 = extract_delay (Some s1) acc in
      let del2, cont2 = extract_delay (Some s2) acc in
      match cont1, cont2 with
      | None, None -> (get_max del1 del2, None)
      | Some c1, None -> (add_delay del2 del1, Some c1)
      | None, Some c2 -> (add_delay del1 del2, Some c2)
      | Some c1, Some c2 -> (get_max del1 del2, Some (StyParallel(c1, c2)))
    )
    | StyChoice(s1,s2) -> (
      let del1, cont1 = extract_delay (Some s1) acc in
      let del2, cont2 = extract_delay (Some s2) acc in
      let max_del = get_min del1 del2 in
      let cont1' = if gt del1 max_del then create_cont max_del del1 cont1 else cont1 in
      let cont2' = if gt del2 max_del then create_cont max_del del2 cont2 else cont2 in
      (max_del, (choice_of_sty_opt cont1' cont2')) 
    )
    | StyFuture _ ->
        (None, st')
    | StyXOffer _ ->
        (acc, st')
    | StyOffer _ ->
        (acc, st')
    | StySkip -> (acc, st')
    | _ -> raise (Except.TypeError [Text "Unsupported session type for delay extraction"])
  )
  | _ -> extract_delay (Some init) acc
  in
  extract_delay (hc.cont) (Some n')

    
let delay_continuation_after_terminal_closure n sp head_conts init =
  let rec search seen hcs =
    List.concat_map (fun hc ->
      match hc.head with
      | Atom (AtomDelay m) ->
          if n <= m then begin
            let remaining_delay = if n < m then StyAtom (AtomDelay (m - n)) else StySkip in
            let new_cont = match remaining_delay with
              | StySkip -> hc.cont
              | _ -> seq_of_sty_opt (Some remaining_delay) hc.cont
            in
            hc.visited <- true;
            [new_cont, hc.recvar_map]
          end
          else(
            let delay,cont = extract_delay_continuation init m hc in
            match delay with
            | Some d when d > n -> 
                let remaining_delay = StyAtom (AtomDelay (d - n)) in
                let new_cont = seq_of_sty_opt (Some remaining_delay) cont in
                hc.visited <- true;
                [new_cont, hc.recvar_map]
            | None -> 
                hc.visited <- true;
                [cont, hc.recvar_map]
            | _ -> []
          )
      | Terminal terminal_kind ->
          (match hc.cont with
          | None -> []
          | Some cont ->
              if List.mem cont seen then
                []
              else
                let cont_heads = get_head_continuation_pair cont sp hc.recvar_map in
                let found = search (cont :: seen) cont_heads in
                List.map (fun (found_cont, found_map) ->
                    hc.visited <- true;
                    let delayed_cont =
                      match terminal_kind with
                      | ParallelDone -> seq_of_sty_opt (Some StySkip) found_cont
                      | RecurseJump -> found_cont
                    in
                    (delayed_cont, found_map)
                ) found)
      | _ -> []
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

    let event_residuals : session_residual IntHashtbl.t =
      IntHashtbl.create (List.length g.events)
    in
    let event_recvars : ((identifier * session_type) list) IntHashtbl.t =
      IntHashtbl.create (List.length g.events)
    in
    let event_from_structural_propagation : bool IntHashtbl.t =
      IntHashtbl.create (List.length g.events)
    in

    let get_event_residual ev =
      try Some (IntHashtbl.find event_residuals ev.id) with Not_found -> None
    in
    let get_event_recvars ev =
      try IntHashtbl.find event_recvars ev.id with Not_found -> []
    in
    let get_event_from_structural_propagation ev =
      try IntHashtbl.find event_from_structural_propagation ev.id
      with Not_found -> false
    in
    let set_event_residual ?(from_structural=false) ev recvars residual =
      IntHashtbl.replace event_residuals ev.id residual;
      IntHashtbl.replace event_recvars ev.id recvars;
      IntHashtbl.replace event_from_structural_propagation ev.id
        (from_structural || get_event_from_structural_propagation ev);
      ev.session_type <- node_of_residual protocol_node residual
    in

    (* Visit the event graph BFS *)
    let rec generalized_session_judgement
        (next_queue : event Queue.t)
        (processed_count : int IntHashtbl.t) =
      if Queue.is_empty next_queue then
        ()
      else
        let (ev : event) = Queue.pop next_queue in
        if ev.is_recurse then
          (
            generalized_session_judgement next_queue processed_count
          )
        else begin
          let count =
            try IntHashtbl.find processed_count ev.id with Not_found -> 0
          in
          if count > List.length g.events then
            error_handler g
              (Printf.sprintf
                "Session residual propagation did not reach a fixpoint at event %d"
                ev.id)
              g.thread_codespan module_name;
          IntHashtbl.replace processed_count ev.id (count + 1);

          let rec_var_cont = get_event_recvars ev in
          let current_from_structural_propagation =
            get_event_from_structural_propagation ev
          in
          let current_residual =
            match get_event_residual ev with
            | Some residual -> residual
            | None ->
                let err_msg = Printf.sprintf
                  "Event %d has no residual assigned during generalized session type check"
                  ev.id
                in
                error_handler g err_msg g.thread_codespan module_name
          in
          if config.verbose then
            Printf.eprintf "Processing event %d with residual %s\n"
              ev.id (string_of_residual current_residual);

          let child_events = ev.outs in
          let head_conts =
            match current_residual, child_events with
            | Some sty, _ -> get_head_continuation_pair sty g.thread_codespan rec_var_cont
            | None, [] -> []
            | None, _ -> restart_head_continuation_pairs protocol_node.d g.thread_codespan
          in
          if config.verbose then (
            Printf.eprintf "Extracted head-continuation pairs for event %d:\n" ev.id;
            List.iter (fun hc ->
              Printf.eprintf "  %s\n" (print_string_of_head_cont_pair hc)
            ) head_conts
          );

          let choice_msg_lists = choice_msg_lists_of_children child_events in
          let structural_residual, structural_recvars =
            residual_for_non_choice_heads
              current_residual rec_var_cont choice_msg_lists head_conts
          in

          let is_propogated = ref false in
          let mark_structural_propagation () = is_propogated := true in
          let enqueue_if_needed child_ev =
            if not child_ev.is_recurse then
              Queue.add child_ev next_queue
          in
          let assign_child_residual
              ?(allow_choice=false)
              ?(from_structural=false)
              child_ev recvars residual =
            match get_event_residual child_ev with
            | None ->
                set_event_residual ~from_structural child_ev recvars residual;
                enqueue_if_needed child_ev
            | Some existing ->
                let merged_recvars = get_event_recvars child_ev @ recvars in
                if residual_matches merged_recvars existing residual protocol_node.d then begin
                  if from_structural then
                    IntHashtbl.replace
                      event_from_structural_propagation child_ev.id true
                end
                else if allow_choice then begin
                  let merged_residual = choice_of_residuals existing residual in
                  set_event_residual
                    ~from_structural child_ev merged_recvars merged_residual;
                  enqueue_if_needed child_ev
                end
                else
                  error_handler g
                    (Printf.sprintf
                      "Event %d already has residual %s, but parent event %d produced %s"
                      child_ev.id
                      (string_of_residual existing)
                      ev.id
                      (string_of_residual residual))
                    g.thread_codespan module_name
          in
          (* [kind] is the handshake used at the event graph site; when given, the
             session type's blocking-ness must agree with it. *)
          let head_matches_msg ?kind msg = function
            | Atom (AtomicAct act) ->
              msg_spec_equal (msg_spec_of_atomic_action act) msg
              && (match kind with
                  | None -> true
                  | Some k -> atomic_action_matches_kind k act)
            | _ -> false
          in
          let assign_msg_from_heads ?kind child_ev msg err_label =
            let matched = ref false in
            List.iter (fun hc ->
              if head_matches_msg ?kind msg hc.head then begin
                matched := true;
                hc.visited <- true;
                assign_child_residual ~allow_choice:true child_ev hc.recvar_map hc.cont
              end else begin
                match offerings_of_head hc.head with
                | Some offerings ->
                    List.iter (fun offering ->
                      match offering_session_after_msg ?kind offering msg with
                      | Some offering_residual ->
                          matched := true;
                          hc.visited <- true;
                          let residual =
                            seq_of_sty_opt offering_residual hc.cont
                          in
                          assign_child_residual ~allow_choice:true
                            child_ev hc.recvar_map residual
                      | None -> ()
                    ) offerings
                | None -> ()
              end
            ) head_conts;
            if not !matched then
              error_handler g
                (Printf.sprintf "Expected %s%s message (%s) at event %d | However found %s"
                  (match kind with
                   | None -> ""
                   | Some k -> string_of_handshake_kind k ^ " ")
                  err_label
                  (string_of_msg_spec msg)
                  child_ev.id
                  (string_of_residual current_residual))
                g.thread_codespan module_name
          in
          let residual_after_msg recvars residual msg =
            match residual with
            | None -> None
            | Some sty ->
                get_head_continuation_pair sty g.thread_codespan recvars
                |> List.find_map (fun hc ->
                  if head_matches_msg msg hc.head then
                    Some hc.cont
                  else
                    None
                )
          in
          let rec residual_after_msgs recvars residual msgs =
            match msgs with
            | [] -> Some residual
            | msg :: rest ->
                (match residual_after_msg recvars residual msg with
                | Some residual' -> residual_after_msgs recvars residual' rest
                | None -> None)
          in
          let assign_immediate_msg ?kind branches child_ev msg =
            let offering_matches_immediate_msg offering =
              trigger_matches_msg ?kind offering.trigger msg
            in
            let found_hc_opt =
              List.find_opt (fun hc ->
                match offerings_of_head hc.head with
                | Some offerings ->
                    List.exists offering_matches_immediate_msg offerings
                | None -> false
              ) head_conts
            in
            match found_hc_opt with
            | Some hc ->
                hc.visited <- true;
                let offerings =
                  Option.get (offerings_of_head hc.head)
                in
                let matching, remaining =
                  List.partition offering_matches_immediate_msg offerings
                in
                (match matching with
                | own_cont :: _ ->
                    let own_residual =
                      combine_offering_continuation own_cont.continuation hc.cont
                    in
                    assign_child_residual child_ev hc.recvar_map own_residual;
                    (match remaining with
                    | other_cont :: _ ->
                        let other_residual =
                          combine_offering_continuation other_cont.continuation hc.cont
                        in
                        let other_branch =
                          List.filter (fun b -> b.id <> child_ev.id)
                            branches.owner_branch.branches_to
                        in
                        (match other_branch with
                        | [other_ev] ->
                            assign_child_residual other_ev hc.recvar_map other_residual
                        | _ -> ())
                    | [] -> ())
                | [] -> assign_msg_from_heads ?kind child_ev msg "Immediate")
            | None -> assign_msg_from_heads ?kind child_ev msg "Immediate"
          in
          let assign_select_arm child_ev msg_group =
            let matched = ref false in
            List.iter (fun hc ->
              match offerings_of_head hc.head with
              | Some offerings ->
                  List.iter (fun offering ->
                    if trigger_matches_msg_group offering.trigger msg_group then begin
                      matched := true;
                      hc.visited <- true;
                      let branch_residual =
                        seq_of_sty_opt (Some (offering_body_session offering)) hc.cont
                      in
                      assign_child_residual child_ev hc.recvar_map branch_residual
                    end
                  ) offerings
              | None -> ()
            ) head_conts;
            if not !matched then
              error_handler g
                (Printf.sprintf "Expected offer arm {%s} at event %d | However found %s"
                  (String.concat ", " (List.map string_of_msg_spec msg_group))
                  child_ev.id
                  (string_of_residual current_residual))
                g.thread_codespan module_name
          in

          List.iter (fun child_ev ->
            let rec assign_session_type src =
              match src with
              | `Seq (_, `Choice (msg_list, kind)) ->
                  let matched = ref false in
                  List.iter (fun hc ->
                    match choice_residual_for_head ~kind msg_list hc with
                    | Some residual ->
                      matched := true;
                      hc.visited <- true;
                      assign_child_residual child_ev hc.recvar_map residual
                    | None -> ()
                  ) head_conts;
                  if not !matched then
                    error_handler g
                      (Printf.sprintf "Expected Offerings at event %d | However found %s"
                        child_ev.id (string_of_residual current_residual))
                      g.thread_codespan module_name

              | `Seq (_, `Send (msg, kind)) ->
                  assign_msg_from_heads ~kind child_ev msg "Send"

              | `Seq (_, `Recv (msg, kind)) ->
                  assign_msg_from_heads ~kind child_ev msg "Recv"

              | `Seq (_, `Cycles n) ->
                  (match delay_continuation_after_terminal_closure
                      n g.thread_codespan head_conts protocol_node.d with
                  | [] ->
                      error_handler g
                        (Printf.sprintf "Expected Delay (%d) at event %d | However found %s"
                          n child_ev.id (string_of_residual current_residual))
                        g.thread_codespan module_name
                  | continuations ->
                      (* Equal delays can lead to different choices or parallel
                         arms; subsequent actions determine which path applies. *)
                      List.iter (fun (new_cont, found_map) ->
                        assign_child_residual ~allow_choice:true
                          child_ev found_map new_cont
                      ) continuations)

              | `Root Some (_, branches) ->
                  let has_immediate_actions =
                    List.filter (fun a ->
                      match a.d with
                      | ImmediateRecv _ | ImmediateSend _ -> true
                      | _ -> false
                    ) child_ev.actions
                  in
                  let has_immediate_sibling =
                    List.exists (fun sibling_ev ->
                      sibling_ev.id <> child_ev.id
                      && event_has_immediate_session_action sibling_ev
                    ) branches.owner_branch.branches_to
                  in
                  if has_immediate_actions <> [] then
                    List.iter (fun ia ->
                      match ia.d with
                      | ImmediateRecv (msg, kind)
                      | ImmediateSend (msg, _, kind) ->
                          assign_immediate_msg ~kind branches child_ev msg
                      | _ -> ()
                    ) has_immediate_actions
                  else if has_immediate_sibling then
                    mark_structural_propagation ()
                  else begin
                    mark_structural_propagation ();
                    assign_child_residual
                      ~from_structural:true
                      child_ev structural_recvars structural_residual
                  end

              | `Later (ev_a, ev_b) ->
                  (match get_event_residual ev_a, get_event_residual ev_b with
                  | Some residual_a, Some residual_b -> begin
                      let recvars_a = get_event_recvars ev_a in
                      let recvars_b = get_event_recvars ev_b in
                      let merged_recvars = recvars_a @ recvars_b in
                      let next_a = strip_parallel_done_markers residual_a in
                      let next_b = strip_parallel_done_markers residual_b in
                      let residual_pair =
                        if residual_matches merged_recvars next_a next_b protocol_node.d then
                          Some next_a
                        else
                          let msgs_a = event_session_action_msgs ev_a in
                          let msgs_b = event_session_action_msgs ev_b in
                          match
                            residual_after_msgs recvars_a next_a msgs_b,
                            residual_after_msgs recvars_b next_b msgs_a
                          with
                          | Some next_a', Some next_b'
                            when residual_matches merged_recvars next_a' next_b' protocol_node.d ->
                              Some next_a'
                          | _ -> None
                      in
                      match residual_pair with
                      | Some next_residual ->
                          mark_structural_propagation ();
                          assign_child_residual
                            ~from_structural:true
                            child_ev merged_recvars next_residual
                      | None ->
                        error_handler g
                          (Printf.sprintf
                            "Mismatched session residuals at later event %d | Types: %s vs %s"
                            child_ev.id
                            (string_of_residual next_a)
                            (string_of_residual next_b))
                          g.thread_codespan module_name
                  end
                  | _ ->
                      mark_structural_propagation ())

              | `Branch (_, branch) ->
                  let is_empty_branch_end branch_ev =
                    List.exists (fun branch_root ->
                      branch_root.id = branch_ev.id
                    ) branch.branches_to
                  in
                  let branch_residuals =
                    List.map (fun branch_ev ->
                      (branch_ev, is_empty_branch_end branch_ev, get_event_residual branch_ev)
                    ) branch.branches_val
                  in
                  let required_branch_residuals =
                    List.filter (fun (_, is_empty_branch, _) ->
                      not is_empty_branch
                    ) branch_residuals
                  in
                  if List.exists (fun (_, _, residual_opt) -> Option.is_none residual_opt)
                      required_branch_residuals then
                    mark_structural_propagation ()
                  else begin
                    let branch_residuals =
                      List.map (fun (branch_ev, _, residual_opt) ->
                        (branch_ev, Option.get residual_opt)
                      ) required_branch_residuals
                    in
                    match branch_residuals with
                    | [] ->
                        mark_structural_propagation ();
                        assign_child_residual
                          ~from_structural:true
                          child_ev rec_var_cont current_residual
                    | (first_ev, first_residual) :: rest ->
                        let merged_recvars =
                          List.concat
                            (List.map (fun (branch_ev, _) ->
                              get_event_recvars branch_ev
                            ) branch_residuals)
                        in
                        let branches_match =
                          List.for_all (fun (branch_ev, residual) ->
                            residual_matches
                              (get_event_recvars first_ev @ get_event_recvars branch_ev)
                              first_residual residual protocol_node.d
                          ) rest
                        in
                        if branches_match then begin
                          mark_structural_propagation ();
                          assign_child_residual
                            ~from_structural:true
                            child_ev merged_recvars first_residual
                        end
                        else
                          let branch_residual_str = String.concat "," (List.map(fun (_,res) -> string_of_residual res)rest) in
                          error_handler g
                            (Printf.sprintf "Mismatched session residuals {%s} in branch event %d"
                              branch_residual_str
                              child_ev.id)
                            g.thread_codespan module_name
                  end

              | `Select (_, msg_group) ->
                  assign_select_arm child_ev msg_group
              | `SelectJoin join_info ->
                  let join_residuals =
                    List.filter_map (fun join_ev ->
                      match get_event_residual join_ev with
                      | Some residual -> Some (join_ev, residual)
                      | None -> None
                    ) join_info.join_nodes
                  in
                  if List.length join_residuals <> List.length join_info.join_nodes then
                    mark_structural_propagation ()
                  else begin
                    match join_residuals with
                    | [] ->
                        mark_structural_propagation ();
                        assign_child_residual
                          ~from_structural:true
                          child_ev rec_var_cont current_residual
                    | (first_ev, first_residual) :: rest ->
                        let merged_recvars =
                          List.concat
                            (List.map (fun (join_ev, _) ->
                              get_event_recvars join_ev
                            ) join_residuals)
                        in
                        let join_residuals_match =
                          List.for_all (fun (join_ev, residual) ->
                            residual_matches
                              (get_event_recvars first_ev @ get_event_recvars join_ev)
                              first_residual residual protocol_node.d
                          ) rest
                        in
                        if join_residuals_match then begin
                          mark_structural_propagation ();
                          assign_child_residual
                            ~from_structural:true
                            child_ev merged_recvars first_residual
                        end
                        else
                          error_handler g
                            (Printf.sprintf "Mismatched session residuals in select join event %d"
                              child_ev.id)
                            g.thread_codespan module_name
                  end

              | `Recurse (src', _) ->
                  assign_session_type src'

              | _ ->
                  error_handler g
                    (Printf.sprintf
                      "Unsupported child event source at event %d during generalized session type check"
                      child_ev.id)
                    g.thread_codespan module_name
            in
            assign_session_type child_ev.source
          ) child_events;

          List.iter (fun hc ->
            if not hc.visited
               && not hc.is_choice
               && not (current_from_structural_propagation && hc.is_parallel)
               && not !is_propogated
               && not (is_terminal_head hc.head) then
              error_handler g
                (Printf.sprintf
                  "No matching head-continuation found for event %d's children during generalized session type check | Head: %s | Cont: %s"
                  ev.id
                  (match hc.head with
                  | XOffers off | Offers off -> string_of_protocol (StyOffer off)
                  | Atom act -> string_of_atomic_action_with_gap act
                  | Terminal ParallelDone -> string_of_protocol StySkip
                  | Terminal RecurseJump -> "recurse")
                  (string_of_residual hc.cont))
                g.thread_codespan module_name
          ) head_conts;

          generalized_session_judgement next_queue processed_count
        end
    in

    let processed_count_tbl = IntHashtbl.create (List.length g.events) in
    let q = Queue.create () in
    let root_ev = GraphAnalysis.find_graph_root g.events in

    set_event_residual root_ev [] (Some protocol_node.d);
    Queue.add root_ev q;

    generalized_session_judgement q processed_count_tbl;
    let unassigned_events =
      List.filter (fun ev ->
        (not ev.removed)
        && (not ev.is_recurse)
        && not (IntHashtbl.mem event_residuals ev.id)
      ) g.events
    in
    if unassigned_events <> [] then
      error_handler g
        (Printf.sprintf
          "Session residual propagation left events unassigned: %s"
          (String.concat ", "
            (List.map (fun ev -> string_of_int ev.id) unassigned_events)))
        g.thread_codespan module_name;

    (* check terminal to be empty *)
    let terminal_event = List.find_opt(fun e -> e.is_loop_terminal) g.events in
    (match terminal_event with
    | Some ev ->
        (
        match ev.session_type with
        | Some residual when residual <> protocol_node->
            error_handler g
              (Printf.sprintf "Terminal event %d has non-empty residual %s at end of generalized session type check"
                ev.id (string_of_protocol residual.d))
              g.thread_codespan module_name
        | _ -> ()
        )
    | None -> raise (Except.TypeError [
        Text "No terminal event found in event graph during generalized session type check";
        Except.codespan_local g.thread_codespan
      ])
    );
    let file_name = Printf.sprintf "%sgraph.dot" module_name in
    let file_handler = Out_channel.open_text file_name in
    EventGraphOps.print_graph_with_session_types g file_handler;
    Out_channel.close file_handler
    
    (* Output final graph with annotated session types *)
