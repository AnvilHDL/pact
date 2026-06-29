open Lang
open Except
open SessionAutomaton2

type rec_binding = {
  (* Recursion variables point back to their loop-entry state. *)
  rec_name : identifier;
  rec_state : int;
}

type let_binding = {
  let_name : identifier;
  let_body : session_type;
}

let msg_of_action = function
  | AtomBMsg msg | AtomNBMsg msg -> msg

let action_is_blocking = function
  | AtomBMsg _ -> true
  | AtomNBMsg _ -> false

let trigger_actions = function
  | AtomicAct act -> Some [ act ]
  | AtomConjunction acts -> Some acts
  | _ -> None

let trigger_msg_group trigger =
  Option.map (fun acts -> List.map msg_of_action acts |> msgset_of_list)
    (trigger_actions trigger)

let trigger_is_wildcard = function
  | AtomDelay _ -> true
  | _ -> false

let trigger_is_blocking trigger =
  match trigger_actions trigger with
  | Some acts -> List.for_all action_is_blocking acts
  | None -> false

let trigger_is_nonblocking trigger =
  match trigger_actions trigger with
  | Some acts -> List.for_all (fun act -> not (action_is_blocking act)) acts
  | None -> false

let continuation_or_true (offering : offering_session_type) =
  match offering.continuation with
  | Some cont -> cont
  | None -> StyTrue

let wildcard_continuation_opt offerings =
  offerings
  |> List.find_opt (fun off -> trigger_is_wildcard off.trigger)
  |> Option.map continuation_or_true

let parallel_of_list = function
  | [] -> StyTrue
  | first :: rest -> List.fold_left (fun acc ty -> StyParallel (acc, ty)) first rest

let powerset xs =
  let rec aux = function
    | [] -> [ [] ]
    | x :: rest ->
        let tail = aux rest in
        tail @ List.map (fun ys -> x :: ys) tail
  in
  aux xs

let xoffer_else_guard ?(require_clock = false) branch_groups head_set =
  (* Else resolves only after branch heads are absent now and later this cycle. *)
  {
    any_guard with
    missing_now_groups = branch_groups;
    future_disjoint = head_set;
    require_clock;
    forbid_clock = not require_clock;
  }

let add_blocking_retry auto current branch_groups head_set =
  (* Missing wildcard on blocking offers means wait one clock and retry. *)
  TypeAutomaton.add_transition auto current current Clock
    (xoffer_else_guard ~require_clock:true branch_groups head_set)

let infer_fair_choice left right =
  (* The parser has only StyChoice, so infer the fair-choice cases v3 recognizes. *)
  let rec first_messages sty =
    match sty with
    | StyAtom (AtomicAct act) -> [ msg_of_action act ]
    | StyAtom (AtomConjunction acts) -> List.map msg_of_action acts
    | StyAtom (AtomTerminal nested) -> first_messages nested
    | StySeq (prefix, _) -> first_messages prefix
    | StyChoice (a, b) | StyParallel (a, b) ->
        first_messages a @ first_messages b
    | StyOffer offerings | StyXOffer offerings ->
        List.concat_map
          (fun off ->
            match trigger_actions off.trigger with
            | Some acts -> List.map msg_of_action acts
            | None -> [])
          offerings
    | StyFuture body | StyRec (_, body) -> first_messages body
    | StyAtom (AtomDelay _) | StyTrue | StyVar _ | StyLet _ | StyForall _ -> []
  in
  let endpoint_set msgs =
    List.fold_left
      (fun acc msg -> StringSet.add msg.endpoint acc)
      StringSet.empty msgs
  in
  let left_eps = endpoint_set (first_messages left) in
  let right_eps = endpoint_set (first_messages right) in
  (not (StringSet.equal left_eps right_eps))
  || (StringSet.is_empty left_eps && StringSet.is_empty right_eps)

let validate_action_group default_span acts context =
  (* A conjunctive trigger must choose one timing discipline. *)
  let all_blocking = List.for_all action_is_blocking acts in
  let all_nonblocking = List.for_all (fun act -> not (action_is_blocking act)) acts in
  if not (all_blocking || all_nonblocking) then
    raise
      (TypeError
         [
           Text ("Mixed blocking and non-blocking actions in " ^ context);
           codespan_local default_span;
         ]);
  all_blocking

let validate_offerings default_span offerings context =
  (* Offer arms cannot mix blocking and nonblocking message branches. *)
  let msg_branches =
    List.filter_map
      (fun off ->
        match trigger_actions off.trigger with
        | Some acts -> Some (off, acts)
        | None -> None)
      offerings
  in
  List.iter
    (fun (_, acts) ->
      ignore (validate_action_group default_span acts context : bool))
    msg_branches;
  if msg_branches <> [] then (
    let all_blocking =
      List.for_all (fun (off, _) -> trigger_is_blocking off.trigger) msg_branches
    in
    let all_nonblocking =
      List.for_all
        (fun (off, _) -> trigger_is_nonblocking off.trigger)
        msg_branches
    in
    if not (all_blocking || all_nonblocking) then
      raise
        (TypeError
           [
             Text ("Mixed blocking and non-blocking offerings in " ^ context);
             codespan_local default_span;
           ]));
  msg_branches

let rec messages_of_session_type sty =
  (* Compute the closed-world synchronization alphabet for a session type. *)
  let from_action action = MsgSet.singleton (msg_of_action action) in
  let from_trigger trigger =
    match trigger with
    | AtomicAct act -> from_action act
    | AtomConjunction acts ->
        List.fold_left
          (fun acc act -> MsgSet.add (msg_of_action act) acc)
          MsgSet.empty acts
    | AtomDelay _ -> MsgSet.empty
    | AtomTerminal sty -> messages_of_session_type sty
  in
  let from_offering off =
    MsgSet.union (from_trigger off.trigger)
      (match off.continuation with
      | Some cont -> messages_of_session_type cont
      | None -> MsgSet.empty)
  in
  match sty with
  | StySeq (a, b) | StyChoice (a, b) | StyParallel (a, b) | StyLet (_, a, b)
    ->
      MsgSet.union (messages_of_session_type a) (messages_of_session_type b)
  | StyFuture body | StyRec (_, body) -> messages_of_session_type body
  | StyAtom (AtomicAct act) -> from_action act
  | StyAtom (AtomConjunction acts) ->
      List.fold_left
        (fun acc act -> MsgSet.add (msg_of_action act) acc)
        MsgSet.empty acts
  | StyAtom (AtomTerminal sty) -> messages_of_session_type sty
  | StyAtom (AtomDelay _) | StyTrue | StyVar _ -> MsgSet.empty
  | StyOffer offerings | StyXOffer offerings ->
      List.fold_left
        (fun acc off -> MsgSet.union acc (from_offering off))
        MsgSet.empty offerings
  | StyForall _ -> MsgSet.empty

let rec build_automaton (name : identifier option) (st : session_type)
    (default_span : code_span) =
  (* Build a v2 symbolic automaton directly from the parsed session type. *)
  let auto = TypeAutomaton.create () in
  Option.iter (fun id -> TypeAutomaton.change_name id auto) name;
  let st = SessionHelper.expand_session_type_quantifiers st in

  let rec build sty current rec_env let_env =
    let mark_nonfinal () = TypeAutomaton.set_accepting auto current false in
    match sty with
    | StyTrue ->
        TypeAutomaton.set_accepting auto current true;
        [ current ]
    | StyAtom (AtomicAct act) ->
        mark_nonfinal ();
        let msg = msg_of_action act in
        let msg_set = MsgSet.singleton msg in
        let next = TypeAutomaton.new_state auto true in
        TypeAutomaton.add_transition auto current next (Messages msg_set)
          { any_guard with require_now = msg_set; forbid_clock = true };
        if action_is_blocking act then
          (* Blocking messages may wait for a clock only while the peer is absent. *)
          TypeAutomaton.add_transition auto current current Clock
            (xoffer_else_guard ~require_clock:true [ msg_set ] msg_set);
        [ next ]
    | StyAtom (AtomConjunction acts) ->
        mark_nonfinal ();
        let all_blocking =
          validate_action_group default_span acts "conjunctive session atom"
        in
        let msg_set =
          List.fold_left
            (fun acc act -> MsgSet.add (msg_of_action act) acc)
            MsgSet.empty acts
        in
        let next = TypeAutomaton.new_state auto true in
        TypeAutomaton.add_transition auto current next (Messages msg_set)
          { any_guard with require_now = msg_set; forbid_clock = true };
        if all_blocking then
          (* Blocking conjunctions wait as a unit until the whole group is ready. *)
          TypeAutomaton.add_transition auto current current Clock
            (xoffer_else_guard ~require_clock:true [ msg_set ] msg_set);
        [ next ]
    | StyAtom (AtomDelay n) ->
        mark_nonfinal ();
        if n <= 0 then (
          TypeAutomaton.set_accepting auto current true;
          [ current ])
        else
          let last = ref current in
          for _ = 1 to n do
            let next = TypeAutomaton.new_state auto false in
            TypeAutomaton.add_transition auto !last next Clock
              { any_guard with require_clock = true };
            last := next
          done;
          TypeAutomaton.set_accepting auto !last true;
          [ !last ]
    | StyAtom (AtomTerminal sty) ->
        build sty current rec_env let_env
    | StySeq (left, right) ->
        mark_nonfinal ();
        let left_finals = build left current rec_env let_env in
        List.concat_map
          (fun final ->
            TypeAutomaton.set_accepting auto final false;
            build right final rec_env let_env)
          left_finals
    | StyChoice (left, right) ->
        mark_nonfinal ();
        TypeAutomaton.make_adversary auto current;
        if infer_fair_choice left right then TypeAutomaton.make_fair auto current;
        let left_start = TypeAutomaton.new_state auto false in
        let right_start = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current left_start Epsilon any_guard;
        TypeAutomaton.add_transition auto current right_start Epsilon any_guard;
        build left left_start rec_env let_env
        @ build right right_start rec_env let_env
    | StyFuture body ->
        mark_nonfinal ();
        (* Future represents a fair delay choice between waiting and entering body. *)
        TypeAutomaton.make_fair auto current;
        TypeAutomaton.make_adversary auto current;
        let body_start = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current body_start Epsilon any_guard;
        TypeAutomaton.add_transition auto current current Clock
          { any_guard with require_clock = true };
        build body body_start rec_env let_env
    | StyXOffer offerings ->
        build_xoffer offerings current rec_env let_env
    | StyOffer offerings ->
        build_offer offerings current rec_env let_env
    | StyParallel (left, right) ->
        mark_nonfinal ();
        (* Parallel inside one type is async; pool products handle synchronization. *)
        let left_auto = build_automaton None left default_span in
        let right_auto = build_automaton None right default_span in
        let product = async_product [| left_auto; right_auto |] in
        import_automaton_into ~dst:auto ~src:product ~at_start:current
    | StyRec (id, body) ->
        mark_nonfinal ();
        if List.exists (fun b -> b.rec_name = id) rec_env then
          raise
            (TypeError
               [
                 Text ("Duplicate recursion variable " ^ id);
                 codespan_local default_span;
               ]);
        build body current ({ rec_name = id; rec_state = current } :: rec_env)
          let_env
    | StyVar id -> (
        match List.find_opt (fun b -> b.rec_name = id) rec_env with
        | Some binding ->
            TypeAutomaton.add_transition auto current binding.rec_state Epsilon
              any_guard;
            TypeAutomaton.set_accepting auto current false;
            []
        | None -> (
            match List.find_opt (fun b -> b.let_name = id) let_env with
            | Some binding -> build binding.let_body current rec_env let_env
            | None ->
                raise
                  (TypeError
                     [
                       Text ("Unbound session type variable " ^ id);
                       codespan_local default_span;
                     ])))
    | StyLet (id, definition, body) ->
        build body current rec_env ({ let_name = id; let_body = definition } :: let_env)
    | StyForall _ ->
        raise
          (TypeError
             [
               Text "Quantifier should have been expanded before v2 automaton construction";
               codespan_local default_span;
             ])

  and build_xoffer offerings current rec_env let_env =
    (* Exclusive offer commits only after all branch heads are resolved. *)
    TypeAutomaton.set_accepting auto current false;
    TypeAutomaton.make_adversary auto current;
    let msg_branches =
      validate_offerings default_span offerings "exclusive offer"
      |> List.filter_map (fun (off, _) ->
             match trigger_msg_group off.trigger with
             | Some group -> Some (off, group)
             | None -> None)
    in
    let head_set =
      List.fold_left
        (fun acc (_, group) -> MsgSet.union acc group)
        MsgSet.empty msg_branches
    in
    let all_blocking =
      msg_branches <> []
      && List.for_all (fun (off, _) -> trigger_is_blocking off.trigger) msg_branches
    in
    let branch_groups = List.map snd msg_branches in
    let finals = ref [] in
    List.iter
      (fun (off, group) ->
        let target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current target (Messages group)
          {
            any_guard with
            require_now = group;
            future_disjoint = head_set;
            forbid_clock = true;
          };
        finals := build (continuation_or_true off) target rec_env let_env @ !finals)
      msg_branches;
    if not (MsgSet.is_empty head_set) then
      (* If any branch head may still arrive this cycle, xoffer keeps waiting. *)
      (* TypeAutomaton.add_transition auto current current Epsilon
        {
          any_guard with
          future_intersects = head_set;
          forbid_clock = true;
        }; *)
    (match wildcard_continuation_opt offerings with
    | Some else_ty ->
        let else_target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current else_target Epsilon
          (xoffer_else_guard branch_groups head_set);
        finals := build else_ty else_target rec_env let_env @ !finals
    | None ->
        if all_blocking && not (MsgSet.is_empty head_set) then
          add_blocking_retry auto current branch_groups head_set);
    !finals

  and build_offer offerings current rec_env let_env =
    (* Non-exclusive offer takes every enabled subset and leaves residual waiters. *)
    TypeAutomaton.set_accepting auto current false;
    let msg_branches =
      validate_offerings default_span offerings "non-exclusive offer"
      |> List.filter_map (fun (off, _) ->
             match trigger_msg_group off.trigger with
             | Some group -> Some (off, group)
             | None -> None)
    in
    let head_set =
      List.fold_left
        (fun acc (_, group) -> MsgSet.union acc group)
        MsgSet.empty msg_branches
    in
    let all_blocking =
      msg_branches <> []
      && List.for_all (fun (off, _) -> trigger_is_blocking off.trigger) msg_branches
    in
    let branch_groups = List.map snd msg_branches in
    let finals = ref [] in
    let branch_subsets =
      powerset msg_branches |> List.filter (fun subset -> subset <> [])
    in
    List.iter
      (fun enabled ->
        let residual =
          List.filter
            (fun branch -> not (List.exists (( = ) branch) enabled))
            msg_branches
        in
        let enabled_msgs =
          List.fold_left
            (fun acc (_, group) -> MsgSet.union acc group)
            MsgSet.empty enabled
        in
        let continuation_types =
          List.map (fun (off, _) -> continuation_or_true off) enabled
        in
        let residual_wait =
          if residual = [] then []
          else
            [
              StyOffer
                (List.map fst residual
                @ [ { trigger = AtomDelay 0; continuation = None } ]);
            ]
        in
        let target_ty = parallel_of_list (continuation_types @ residual_wait) in
        let target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current target (Messages enabled_msgs)
          {
            any_guard with
            require_now = enabled_msgs;
            missing_now_groups = List.map snd residual;
            forbid_clock = true;
          };
        finals := build target_ty target rec_env let_env @ !finals)
      branch_subsets;
    if not (MsgSet.is_empty head_set) then
      TypeAutomaton.add_transition auto current current Epsilon
        {
          any_guard with
          missing_now_groups = List.map snd msg_branches;
          future_intersects = head_set;
          forbid_clock = true;
        };
    (match wildcard_continuation_opt offerings with
    | Some else_ty ->
        let else_target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current else_target Epsilon
          (xoffer_else_guard branch_groups head_set);
        finals := build else_ty else_target rec_env let_env @ !finals
    | None ->
        if all_blocking && not (MsgSet.is_empty head_set) then
          add_blocking_retry auto current branch_groups head_set);
    !finals
  in
  ignore (build st auto.start_state [] [] : int list);
  recompute_state_summaries auto;
  auto
