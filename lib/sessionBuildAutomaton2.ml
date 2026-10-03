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

let delay_then ticks residual =
  if ticks <= 0 then residual else StySeq (StyAtom (AtomDelay ticks), residual)

let wildcard_continuation_opt offerings =
  (* Plain wildcards have delay zero; blocking defaults retain their tick. *)
  List.find_map
    (fun off ->
      match off.trigger with
      | AtomDelay ticks -> Some (delay_then ticks (continuation_or_true off))
      | _ -> None)
    offerings

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

(* Wrap a top-level type once: mu X . ((body; $member_id); X). *)
let repeat_with_progress member_id body =
  let rec variables acc = function
    | StyVar id -> StringSet.add id acc
    | StyRec (id, body) | StyForall (_, id, _, body, _) ->
        variables (StringSet.add id acc) body
    | StyLet (id, definition, body) ->
        variables (variables (StringSet.add id acc) definition) body
    | StySeq (a, b) | StyChoice (a, b) | StyParallel (a, b) ->
        variables (variables acc a) b
    | StyFuture body | StyAtom (AtomTerminal body) -> variables acc body
    | StyOfferMatch (offerings, cases) ->
        List.fold_left (fun acc c -> variables acc c.match_body)
          (variables acc (StyOffer offerings)) cases
    | StyOffer offerings | StyXOffer offerings ->
        List.fold_left (fun acc off ->
          let acc = match off.trigger with
            | AtomTerminal body -> variables acc body
            | _ -> acc
          in
          match off.continuation with
          | Some body -> variables acc body
          | None -> acc) acc offerings
    | StySkip | StyEnd _ | StyAtom _ -> acc
  in
  let used = variables StringSet.empty body in
  let rec fresh n =
    let id = Printf.sprintf "__repeat_%d" n in
    if StringSet.mem id used then fresh (n + 1) else id
  in
  let rec_var = fresh 0 in
  StyRec (rec_var, StySeq (StySeq (body, StyEnd member_id), StyVar rec_var))

let parallel_of_list = function
  | [] -> StySkip
  | first :: rest -> List.fold_left (fun acc ty -> StyParallel (acc, ty)) first rest

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
    | StyOffer offerings | StyXOffer offerings | StyOfferMatch (offerings, _) ->
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
  | StyOfferMatch (offerings, cases) ->
      List.fold_left
        (fun acc c -> MsgSet.union acc (messages_of_session_type c.match_body))
        (messages_of_session_type (StyOffer offerings)) cases
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
    | StyAtom (AtomicAct act) ->
        mark_nonfinal ();
        let msg = msg_of_action act in
        let msg_set = MsgSet.singleton msg in
        let blocking = action_is_blocking act in
        let action = message_action msg in
        let next = TypeAutomaton.new_state auto true in
        set_residual_type auto next StySkip;
        TypeAutomaton.add_transition auto current next action
          { any_guard with require_now = msg_set; forbid_clock = false } msg_set;
        (* Atomic messages advertise their head even while waiting. *)
        TypeAutomaton.add_transition auto current current epsilon
          { any_guard with
            forbid_now = msg_set;
            forbid_clock = true;
            future_members = if blocking then msg_set else MsgSet.empty }
          msg_set;
        if blocking then (
          (* Once absence is resolved, tick before retrying the same action. *)
          let retry = TypeAutomaton.new_state auto false in
          TypeAutomaton.add_transition auto current retry epsilon
            { any_guard with
              forbid_now = msg_set;
              future_disjoint = msg_set;
              forbid_clock = true }
            msg_set;
          let rec_var = fresh_blocking_rec_var () in
          let rec_env = { rec_name = rec_var; rec_state = current } :: rec_env in
          ignore (build (delay_then 1 (StyVar rec_var)) retry rec_env let_env
                  : int list));
        [ next ]
    | StyAtom (AtomConjunction acts) ->
        if validate_action_group default_span acts "conjunctive action" then
          raise (Except.UnimplementedError
            [Text "blocking conjunctive actions are not yet implemented"]);
        mark_nonfinal ();
        let group = msgset_of_list (List.map msg_of_action acts) in
        let next = TypeAutomaton.new_state auto true in
        set_residual_type auto next StySkip;
        TypeAutomaton.add_transition auto current next (message_actions group)
          { any_guard with require_now = group; forbid_clock = true } group;
        (* A committed group waits until every message is immediate. *)
        MsgSet.iter (fun msg ->
          TypeAutomaton.add_transition auto current current epsilon
            { any_guard with forbid_now = MsgSet.singleton msg; forbid_clock = true }
            group) group;
        [ next ]
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
        let final_states = IntSet.of_list left_finals in
        (* Grafting the continuation replaces the left fragment's terminal idling. *)
        auto.transitions <- List.filter (fun t ->
          not (IntSet.mem t.from_state final_states
               && t.from_state = t.to_state && t.action = epsilon))
          auto.transitions;
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
    | StyOfferMatch (offerings, cases) ->
        build_offer_match offerings cases current rec_env let_env
    | StyParallel (left, right) ->
        mark_nonfinal ();
        let rec collect acc = function
          | StyParallel (a, b) -> collect (collect acc b) a
          | body -> body :: acc
        in
        let components = collect (collect [] right) left in
        let automata = List.mapi (fun i body ->
          let child = build_automaton None body default_span in
          SessionAutomaton2.add_final_state_epsilon_loops child;
          (Printf.sprintf "component%d" i, child)) components in
        (* Local parallel shares a symbolic boundary and has no internal messages. *)
        let all_messages =
          List.fold_left (fun messages (_, child) ->
            SessionAutomaton2.MsgSet.union messages child.total_message_set)
            SessionAutomaton2.MsgSet.empty automata
        in
        let product =
          SessionAutomaton2.unified_product false automata all_messages
            SessionAutomaton2.MsgSet.empty
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
    (* A singleton surface offer advertises its head on wait and default edges. *)
    let singleton_head = match msg_branches with
      | [(_, group)] when MsgSet.cardinal group = 1 -> group
      | _ -> MsgSet.empty
    in
    let pending_heads = MsgSet.diff head_set singleton_head in
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
    (* One alternative per head expresses F intersect heads <> empty. *)
    MsgSet.iter
      (fun head ->
        TypeAutomaton.add_transition auto current current epsilon
          { any_guard with
            forbid_now = singleton_head;
            forbid_clock = true;
            future_members = MsgSet.singleton head }
          singleton_head
          ~offers_pending:pending_heads)
      head_set;
    (match wildcard_continuation_opt offerings with
    | Some else_ty ->
        let else_target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current else_target epsilon
          (xoffer_else_guard (MsgSet.of_list branch_groups) head_set)
          singleton_head;
        finals := build else_ty else_target rec_env let_env @ !finals
    | None ->
        ());
    !finals)

  (* An offer match is a conjunctive offer that also records the arms taken.
     As in a conjunctive offer, an arm is taken as soon as its message is
     immediate, and each remaining arm resolves like an exclusive offer of its
     own. Once none can be taken this cycle, the case for exactly the arms
     taken follows their bodies. Bodies must start with a delay, so running
     them after that point loses no same-cycle behaviour. *)
  and build_offer_match offerings cases current rec_env let_env =
    if offer_is_blocking_without_else offerings then
      build (blocking_offer_expansion (fresh_blocking_rec_var ()) offerings
               (fun offs -> StyOfferMatch (offs, cases)))
        current rec_env let_env
    else
    (let arms =
      validate_offerings default_span offerings "offer match"
      |> List.filter_map (fun (off, _) ->
             match trigger_msg_group off.trigger with
             | Some group -> Some (off, group)
             | None -> None)
      |> Array.of_list
    in
    let case_list = List.map (fun c -> (c.match_on, c.match_body)) cases in
    (match check_offer_match_cases
             (Array.to_list arms |> List.map (fun (_, g) -> MsgSet.elements g)) case_list with
     | Some err -> raise (TypeError [ Text err; codespan_local default_span ])
     | None -> ());
    (match check_offer_match_arms offerings with
     | Some err -> raise (TypeError [ Text err; codespan_local default_span ])
     | None -> ());
    let n = Array.length arms in
    let group_of mask =
      Array.to_list arms
      |> List.filteri (fun k _ -> mask land (1 lsl k) <> 0)
      |> List.fold_left (fun acc (_, g) -> MsgSet.union acc g) MsgSet.empty
    in
    let all = (1 lsl n) - 1 in
    let head_set = group_of all in
    let states = Hashtbl.create 8 in
    Hashtbl.replace states 0 current;
    let pending = Queue.create () in
    Queue.add 0 pending;
    let state_for mask =
      match Hashtbl.find_opt states mask with
      | Some s -> s
      | None ->
          let s = TypeAutomaton.new_state auto false in
          Hashtbl.replace states mask s;
          Queue.add mask pending;
          s
    in
    let finals = ref [] in
    while not (Queue.is_empty pending) do
      let mask = Queue.take pending in
      let st = Hashtbl.find states mask in
      TypeAutomaton.set_accepting auto st false;
      let remaining = group_of (all land lnot mask) in
      (* Take one more arm. *)
      for k = 0 to n - 1 do
        if mask land (1 lsl k) = 0 then begin
          let group = snd arms.(k) in
          TypeAutomaton.add_transition auto st (state_for (mask lor (1 lsl k)))
            (message_actions group)
            { any_guard with require_now = group; forbid_clock = false } group
        end
      done;
      (* Wait while a remaining arm may still be taken this cycle. Before any
         arm the offer offers every arm; afterwards each remaining arm offers
         itself only while it is still possible this cycle. *)
      MsgSet.iter (fun head ->
        let guard = { any_guard with
                      forbid_now = remaining;
                      forbid_clock = true;
                      future_members = MsgSet.singleton head } in
        if mask = 0 then TypeAutomaton.add_transition auto st st epsilon guard remaining
        else TypeAutomaton.add_transition ~offers_pending:remaining auto st st epsilon guard MsgSet.empty)
        remaining;
      (* No further arm this cycle: continue with the case for the arms taken. *)
      if mask <> 0 then begin
        let taken = Array.to_list arms |> List.filteri (fun k _ -> mask land (1 lsl k) <> 0) in
        let body = Option.get (offer_match_lookup case_list (MsgSet.elements (group_of mask))) in
        let arm_bodies = List.filter_map (fun (off, _) ->
          match off.continuation with
          | None | Some StySkip -> None
          | Some cont -> Some cont) taken in
        let after = match arm_bodies with
          | [] -> body
          | conts -> StySeq (parallel_of_list conts, body)
        in
        let target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto st target epsilon
          { any_guard with forbid_now = remaining; future_disjoint = remaining; forbid_clock = true }
          MsgSet.empty;
        finals := build after target rec_env let_env @ !finals
      end
    done;
    (match wildcard_continuation_opt offerings with
    | Some else_ty ->
        let else_target = TypeAutomaton.new_state auto false in
        TypeAutomaton.add_transition auto current else_target epsilon
          (xoffer_else_guard head_set head_set)
          head_set;
        finals := build else_ty else_target rec_env let_env @ !finals
    | None -> ());
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
    (* Wait only when no head is immediate and at least one is still future. *)
    MsgSet.iter
      (fun head ->
        TypeAutomaton.add_transition auto current current epsilon
          { any_guard with
            forbid_now = head_set;
            forbid_clock = true;
            future_members = MsgSet.singleton head }
          head_set)
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

    (* Commit one head; the other branches retain their continuations and defaults. *)
    List.iteri
      (fun j (_, group_j) ->
        let committed =
          List.mapi
            (fun k (off_k, _) ->
              if k = j then
                StySeq (StyAtom (nonblocking_trigger off_k.trigger),
                        continuation_or_true off_k)
              else
                StyXOffer [ off_k; { trigger = AtomDelay 0; continuation = None } ])
            msg_branches
        in
        let target = TypeAutomaton.new_state auto false in
        (* Commitment exposes the target's future menu without firing a message. *)
        TypeAutomaton.add_transition auto current target epsilon
          { any_guard with require_now = group_j; forbid_clock = true }
          MsgSet.empty;
        finals :=
          build (parallel_of_list committed) target rec_env let_env @ !finals)
      msg_branches;
    !finals)
  in
  ignore (build st auto.start_state [] [] : int list);
  recompute_state_summaries auto;
  auto
