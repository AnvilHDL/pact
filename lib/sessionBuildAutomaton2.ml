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
  | None -> StySkip

let wildcard_continuation_opt offerings =
  offerings
  |> List.find_opt (fun off -> trigger_is_wildcard off.trigger)
  |> Option.map continuation_or_true

(* Fresh recursion variables for desugared blocking actions. *)
(* A blocking offer with no else arm is mu X . offer(B) else #;X. The inner
   offer keeps the same branches but stops being blocking. *)
let nonblocking_trigger = function
  | AtomicAct act -> AtomicAct (AtomNBMsg (msg_of_action act))
  | AtomConjunction acts ->
      AtomConjunction (List.map (fun a -> AtomNBMsg (msg_of_action a)) acts)
  | other -> other

let offer_is_blocking_without_else offerings =
  let msg_offs = List.filter (fun off -> not (trigger_is_wildcard off.trigger)) offerings in
  msg_offs <> []
  && List.for_all (fun off -> trigger_is_blocking off.trigger) msg_offs
  && not (List.exists (fun off -> trigger_is_wildcard off.trigger) offerings)

let blocking_offer_expansion rec_var offerings =
  let inner =
    List.map (fun off -> { off with trigger = nonblocking_trigger off.trigger })
      offerings
  in
  fun wrap ->
    StyRec (rec_var,
      wrap (inner @ [ { trigger = AtomDelay 1; continuation = Some (StyVar rec_var) } ]))

let blocking_rec_counter = ref 0
let fresh_blocking_rec_var () =
  incr blocking_rec_counter;
  Printf.sprintf "__blocking_%d" !blocking_rec_counter

let future_rec_counter = ref 0
let fresh_future_rec_var () =
  incr future_rec_counter;
  Printf.sprintf "__future_%d" !future_rec_counter

let parallel_of_list = function
  | [] -> StySkip
  | first :: rest -> List.fold_left (fun acc ty -> StyParallel (acc, ty)) first rest

let delay_then ticks residual =
  if ticks <= 0 then residual else StySeq (StyAtom (AtomDelay ticks), residual)

let xoffer_else_guard ?(require_clock = false) branch_acts head_set =
  (* Else resolves only after branch heads are absent now and later this cycle. *)
  {
    any_guard with
    forbid_now = branch_acts;
    future_disjoint = head_set;
    require_clock;
    forbid_clock = false;
  }

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
    | StyAtom (AtomDelay _) | StySkip | StyEnd _ | StyVar _ | StyLet _ | StyForall _ -> []
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
  | StyAtom (AtomDelay _) | StySkip | StyEnd _ | StyVar _ -> MsgSet.empty
  | StyOffer offerings | StyXOffer offerings ->
      List.fold_left
        (fun acc off -> MsgSet.union acc (from_offering off))
        MsgSet.empty offerings
  | StyForall _ -> MsgSet.empty

let rec build_automaton (name : identifier option) (st : session_type)
    (default_span : code_span) =
  (* Build a v2 symbolic automaton directly from the parsed session type. *)
  let total_messages = messages_of_session_type st in
  let auto = TypeAutomaton.create total_messages in
  Option.iter (fun id -> TypeAutomaton.change_name id auto) name;
  let st = SessionHelper.expand_session_type_quantifiers st in

  let rec build sty current rec_env let_env =
    set_residual_type auto current sty;
    let mark_nonfinal () = TypeAutomaton.set_accepting auto current false in
    match sty with
    | StySkip -> (*skip*)
      TypeAutomaton.set_accepting auto current true;
      TypeAutomaton.add_transition auto current current epsilon {any_guard with forbid_clock = true} MsgSet.empty;
        [ current ]
    | StyEnd id -> (*end*)
      mark_nonfinal ();
      let final = TypeAutomaton.new_state auto true in
      set_residual_type auto final StySkip;
      let prog_act = progress_action id in
      TypeAutomaton.add_transition auto current final prog_act {any_guard with forbid_clock = true} MsgSet.empty;
        [ final ] 
    | StyAtom (AtomicAct act) when action_is_blocking act ->
        (* A blocking action is mu X . xoffer(a, #;X). *)
        let msg = msg_of_action act in
        let rec_var = fresh_blocking_rec_var () in
        let retry = StyVar rec_var in
        let expansion =
          StyRec (rec_var,
            StyXOffer [
              { trigger = AtomicAct (AtomNBMsg msg); continuation = None };
              { trigger = AtomDelay 1; continuation = Some retry };
            ])
        in
        build expansion current rec_env let_env
    | StyAtom (AtomicAct act) ->
        mark_nonfinal ();
        let msg = msg_of_action act in
        let msg_set = MsgSet.singleton msg in
        let action = message_action msg in
        let next = TypeAutomaton.new_state auto true in
        set_residual_type auto next StySkip;
        TypeAutomaton.add_transition auto current next action
          { any_guard with require_now = msg_set; forbid_clock = false } msg_set;
        TypeAutomaton.add_transition auto current current epsilon
          {any_guard with forbid_now = msg_set} msg_set;
        [ next ]
    | StyAtom (AtomConjunction _) ->
      raise (Except.UnimplementedError ([Text "conjunctive triggers are not yet implemented"]))
    | StyAtom (AtomDelay n) ->
        mark_nonfinal ();
        if n <= 0 then (
          TypeAutomaton.set_accepting auto current true;
          [ current ])
        else
          let last = ref current in
          for i = 1 to n do
            let next = TypeAutomaton.new_state auto false in
            set_residual_type auto next (delay_then (n - i) StySkip);
            TypeAutomaton.add_transition auto !last next Clock
              { any_guard with require_clock = true; forbid_clock = false }
              MsgSet.empty;
            TypeAutomaton.add_transition auto !last !last epsilon
              { any_guard with forbid_clock = true } MsgSet.empty;
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
        if infer_fair_choice left right then
          TypeAutomaton.make_fair auto current;
        let left_start = TypeAutomaton.new_state auto false in
        let right_start = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current left_start epsilon
          { any_guard with forbid_clock = true } MsgSet.empty;
        TypeAutomaton.add_transition auto current right_start epsilon
          { any_guard with forbid_clock = true } MsgSet.empty;
        build left left_start rec_env let_env
        @ build right right_start rec_env let_env
    | StyFuture body ->
        (* F tau is mu X . (tau + #;X). *)
        let rec_var = fresh_future_rec_var () in
        let expansion =
          StyRec (rec_var,
            StyChoice (body, StySeq (StyAtom (AtomDelay 1), StyVar rec_var)))
        in
        build expansion current rec_env let_env
    | StyXOffer offerings ->
        build_xoffer offerings current rec_env let_env
    | StyOffer offerings ->
        build_offer offerings current rec_env let_env
    | StyParallel (left, right) ->
        mark_nonfinal ();
        let left_auto = build_automaton None left default_span in
        let right_auto = build_automaton None right default_span in
        SessionAutomaton2.add_final_state_epsilon_loops left_auto;
        SessionAutomaton2.add_final_state_epsilon_loops right_auto;
        (* Internal parallel: ALL messages are boundary (no sync pairing required);
           use the environment so guarded waits still resolve against the partner. *)
        let all_messages =
          SessionAutomaton2.MsgSet.union
            (left_auto.total_message_set)
            (right_auto.total_message_set)
        in
        let product =
          SessionAutomaton2.unified_product [| left_auto; right_auto |]
            ~boundary_messages:all_messages ~use_env:true
        in
        (* Remove only the unguarded epsilon self-loops on accepting states of the product.
           These are the ones we added for preprocessing; product-generated epsilons have guards. *)
        SessionAutomaton2.remove_final_state_epsilon_loops product;
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
            TypeAutomaton.add_transition auto current binding.rec_state epsilon
              { any_guard with forbid_clock = true } MsgSet.empty;
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
    if offer_is_blocking_without_else offerings then
      build (blocking_offer_expansion (fresh_blocking_rec_var ()) offerings
               (fun offs -> StyXOffer offs))
        current rec_env let_env
    else
    (* Exclusive offer commits only after all branch heads are resolved. *)
    (TypeAutomaton.set_accepting auto current false;
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
    let branch_groups = List.map (fun (_, g) -> MsgSet.elements g) msg_branches in
    let branch_groups = List.concat branch_groups in
    let finals = ref [] in
    List.iter
      (fun (off, group) ->
        let target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current target (message_actions group)
          {
            any_guard with
            future_disjoint = head_set;
            forbid_clock = false;
            require_now = group;
          }
          group;
        finals := build (continuation_or_true off) target rec_env let_env @ !finals)
      msg_branches;
    (* Wait, offering the branch heads the environment still promises. *)
    if not (MsgSet.is_empty head_set) then
      TypeAutomaton.add_transition auto current current epsilon
        { any_guard with forbid_clock = true }
        MsgSet.empty
        ~offers_pending:head_set;
    (match wildcard_continuation_opt offerings with
    | Some else_ty ->
        let else_target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current else_target epsilon
          (xoffer_else_guard (MsgSet.of_list branch_groups) head_set)
          MsgSet.empty;
        finals := build else_ty else_target rec_env let_env @ !finals
    | None ->
        ());
    !finals)

  and build_offer offerings current rec_env let_env =
    if offer_is_blocking_without_else offerings then
      build (blocking_offer_expansion (fresh_blocking_rec_var ()) offerings
               (fun offs -> StyOffer offs))
        current rec_env let_env
    else
    (TypeAutomaton.set_accepting auto current false;
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
    let branch_groups = List.map (fun (_, g) -> MsgSet.elements g) msg_branches in
    let branch_groups = List.concat branch_groups in
    (* Wait while a branch head is still promised later, offering the heads. *)
    if not (MsgSet.is_empty head_set) then
      TypeAutomaton.add_transition auto current current epsilon
        { any_guard with forbid_now = MsgSet.of_list branch_groups;
                         forbid_clock = true }
        head_set;
    let finals = ref [] in
    (match wildcard_continuation_opt offerings with
     | Some else_ty ->
         let else_target = TypeAutomaton.new_state auto false in
         TypeAutomaton.add_transition auto current else_target epsilon
           (xoffer_else_guard (MsgSet.of_list branch_groups) head_set)
           head_set;
         finals := build else_ty else_target rec_env let_env @ !finals
     | None -> ());

    (* Each branch is the product where that branch fires and the others keep
       their default; unified_product builds the product itself. *)
    List.iteri
      (fun j (off_j, group_j) ->
        let committed =
          List.mapi
            (fun k (off_k, _) ->
              if k = j then
                StyXOffer [ off_k; { trigger = AtomDelay 0; continuation = None } ]
              else
                StyXOffer [ { off_k with continuation = None };
                            { trigger = AtomDelay 0; continuation = None } ])
            msg_branches
        in
        let target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current target epsilon
          { any_guard with require_now = group_j; forbid_clock = false }
          group_j;
        let after = build (parallel_of_list committed) target rec_env let_env in
        let cont = continuation_or_true off_j in
        finals :=
          List.concat_map (fun f ->
            TypeAutomaton.set_accepting auto f false;
            build cont f rec_env let_env) after
          @ !finals)
      msg_branches;
    if not (MsgSet.is_empty head_set) then
      TypeAutomaton.add_transition auto current current epsilon
        { any_guard with future_members =  head_set ; forbid_now =  head_set }
        head_set;
    !finals)
  in
  ignore (build st auto.start_state [] [] : int list);
  recompute_state_summaries auto;
  auto
