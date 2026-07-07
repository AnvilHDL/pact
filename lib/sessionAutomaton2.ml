open Lang

module MsgOrd = struct
  type t = message_specifier
  let compare a b = String.compare (string_of_msg_spec a) (string_of_msg_spec b)
end

module MsgSet = Set.Make (MsgOrd)

module StringSet = Set.Make (String)

module IntSet = Set.Make (Int)

let msgset_of_list msgs =
  List.fold_left (fun acc msg -> MsgSet.add msg acc) MsgSet.empty msgs

let msgset_to_list set = MsgSet.elements set

let string_of_msgset set =
  set
  |> MsgSet.elements
  |> List.map string_of_msg_spec
  |> String.concat ","

(* Observable labels used by the closed compatibility game. *)
type action =
  | Epsilon
  | Messages of MsgSet.t
  | Clock
  | Progress of StringSet.t
  | FairBranch of identifier * bool

let string_of_action = function
  | Epsilon -> "alpha = epsilon"
  | Messages msgs ->
      "alpha = {" ^ string_of_msgset msgs ^ "}"
  | Clock -> "alpha = {#}"
  | Progress ids ->
      "alpha = {$" ^ (ids |> StringSet.elements |> String.concat ",$") ^ "}"
  | FairBranch (id, branch) ->
      "alpha = {" ^ id ^ (if branch then "_true" else "_false") ^ "}"

(* Symbolic one-step environment constraints for a transition. *)
type guard = {
  require_now : MsgSet.t; (* require_now = Imm(E) *)
  forbid_now : MsgSet.t; (* forbid_now ∩ Imm(E) = ∅ *)
  subset_now : MsgSet.t; (* subset_now ⊆ Imm(E) *)
  missing_now_groups : MsgSet.t list; (* ∀G. G ∈ missing_now_groups ⇒ G ⊄ Imm(E) *)
  exists_now_groups : MsgSet.t list; (* ∃G ∈ exists_now_groups. G ∩ Imm(E) ≠ ∅ *)
  require_clock : bool; (* require_clock ⇒ # ∈ Imm(E) *)
  forbid_clock : bool; (* forbid_clock ⇒ # ∉ Imm(E) *)
  future_disjoint : MsgSet.t; (* future_disjoint ∩ F = ∅ *)
  future_intersects : MsgSet.t list; (* ∀G ∈ future_intersects. G ∩ F ≠ ∅ *)
}

let any_guard = {
  require_now = MsgSet.empty;
  forbid_now = MsgSet.empty;
  subset_now = MsgSet.empty;
  missing_now_groups = [];
  exists_now_groups = [];
  require_clock = false;
  forbid_clock = false;
  future_disjoint = MsgSet.empty;
  future_intersects = [];
}

let guard_is_any g =
  MsgSet.is_empty g.require_now
  && MsgSet.is_empty g.forbid_now
  && MsgSet.is_empty g.subset_now
  && g.missing_now_groups = []
  && g.exists_now_groups = []
  && not g.require_clock
  && not g.forbid_clock
  && MsgSet.is_empty g.future_disjoint
  && g.future_intersects = []

(* Local view of what is immediate now and possible later in this cycle. *)
type env = {
  imm : MsgSet.t;
  future : MsgSet.t;
  clock : bool;
}

let empty_env = { imm = MsgSet.empty; future = MsgSet.empty; clock = false }

let clock_guard_env env =
  env

(* A transition is enabled exactly when its symbolic guard matches the local view. *)
let guard_satisfied env g =
  if guard_is_any g then true
  else
    let missing_group group = not (MsgSet.subset group env.imm) in
    let exists_group group = not (MsgSet.disjoint group env.imm) in
    let future_group group = not (MsgSet.disjoint group env.future) in
    let now_ok =
      if not (MsgSet.is_empty g.require_now) then
        MsgSet.equal g.require_now env.imm
      else if not (MsgSet.is_empty g.subset_now) then
        MsgSet.subset g.subset_now env.imm
      else true
    in
    now_ok
    && MsgSet.disjoint g.forbid_now env.imm
    && List.for_all missing_group g.missing_now_groups
    && (g.exists_now_groups = [] || List.exists exists_group g.exists_now_groups)
    && ((not g.require_clock) || env.clock)
    && ((not g.forbid_clock) || not env.clock)
    && MsgSet.disjoint g.future_disjoint env.future
    && List.for_all future_group g.future_intersects

(* Project a guard onto a message universe: keep only conditions about those messages.
   Boundary conditions are dropped (they concern the outside environment, not partners). *)
let project_guard_to universe g =
  let inter s = MsgSet.inter s universe in
  let inter_groups groups =
    groups
    |> List.map inter
    |> List.filter (fun s -> not (MsgSet.is_empty s))
  in
  (* future_intersects and exists_now_groups are DISJUNCTIONS (∃G. G ∩ F/Imm(E)
     ≠ ∅ = some message of G is present). Unlike missing_now_groups'
     conjunction, a disjunctive group must not be split per-message across the
     projection: keeping only G ∩ universe would turn one OR into a stricter
     condition and could drop the disjunct entirely once its witnessing
     message is outside the universe, even though the group is still
     satisfiable by a message that IS in the universe. So a group is kept
     WHOLE when it has any message in the universe, and dropped entirely when
     none of its messages are in the universe. *)
  let keep_disjunctive_groups groups =
    groups |> List.filter (fun group -> not (MsgSet.disjoint group universe))
  in
  {
    require_now = inter g.require_now;
    forbid_now = inter g.forbid_now;
    subset_now = inter g.subset_now;
    missing_now_groups = inter_groups g.missing_now_groups;
    exists_now_groups = keep_disjunctive_groups g.exists_now_groups;
    require_clock = g.require_clock;
    forbid_clock = g.forbid_clock;
    future_disjoint = inter g.future_disjoint;
    future_intersects = keep_disjunctive_groups g.future_intersects;
  }

let string_of_guard g =
  let parts = ref [] in
  let fmt_msgset msgs = "{" ^ string_of_msgset msgs ^ "}" in
  let add pred =
    parts := pred :: !parts
  in
  let add_msg pred msgs =
    if not (MsgSet.is_empty msgs) then
      add (pred (fmt_msgset msgs))
  in
  add_msg (fun s -> s ^ "= Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " cap Imm(E) = empty") g.forbid_now;
  add_msg (fun s -> s ^ " subset Imm(E)") g.subset_now;
  if g.missing_now_groups <> [] then
    add
      ("forall G in ["
       ^ (g.missing_now_groups
          |> List.map fmt_msgset
          |> String.concat ";")
       ^ "]. not (G subset Imm(E))");
  if g.exists_now_groups <> [] then
    add
      ("exists G in ["
       ^ (g.exists_now_groups
          |> List.map fmt_msgset
          |> String.concat ";")
       ^ "]. G cap Imm(E) <> empty");
  if g.require_clock then add "# in Imm(E)";
  if g.forbid_clock then add "# notin Imm(E)";
  add_msg (fun s -> s ^ " cap F = empty") g.future_disjoint;
  if g.future_intersects <> [] then
    add
      ("forall G in ["
       ^ (g.future_intersects
          |> List.map fmt_msgset
          |> String.concat ";")
       ^ "]. G cap F <> empty");
  match List.rev !parts with
  | [] -> "true"
  | xs -> String.concat " && " xs

type product_component = {
  pc_name : identifier;
  pc_state : int;
  pc_residual : string option;
}

(* Head and maybe_ready cache the formal Head/MaybeReady sets.
   head_clock records whether the clock (#) is in this state's Head  *)
type state = {
  id : int;
  mutable accepting : bool;
  mutable is_winning : bool;
  mutable is_fair : bool;
  mutable adversary : bool;
  mutable head : MsgSet.t;
  mutable head_clock : bool;
  mutable maybe_ready : MsgSet.t;
  mutable residual_type : string option;
  mutable product_components : product_component list;
  mutable debug_info : string option;
}

type transition = {
  from_state : int;
  to_state : int;
  action : action;
  guard : guard; (*Env*)
  boundary_now : MsgSet.t;
  boundary_future : MsgSet.t;
  (* Pending (boundary-projected) guard: the part of the merged product guard
     that concerns boundary messages and is left for the environment to
     discharge. guard holds the FULL merged guard (closed game/dead-end
     analysis rely on it), not just the internal-projected part. Debug only. *)
  boundary_guard : guard;
  (* The combined action's message set projected onto internal_messages —
     i.e. the union of component labels that actually synchronized to
     satisfy the (internal-projected) guard, as opposed to `action`, which
     carries the full combined label including boundary messages. Debug
     only; empty/Epsilon when the picked action has no internal component. *)
  internal_action : action;
  offers : MsgSet.t;
  mutable maybe_offers : MsgSet.t;
  mutable in_winning : bool;
  transition_debug_info : string option;
}

type message_choice = {
  mc_to_state : int;
  mc_actions : MsgSet.t;
  mc_changed : bool;
}

type transition_outgoing_index = (int, transition list) Hashtbl.t

type typeAutomaton = {
  mutable name : identifier;
  mutable states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  mutable start_state : int;
  mutable next_state_id : int;
}

let action_messages = function
  | Messages msgs -> msgs
  | _ -> MsgSet.empty

let transition_is_clock t =
  match t.action with
  | Clock -> true
  | _ -> false

let transition_keeps_cycle_future t =
  (* MaybeReady_A closes over every non-clock transition. *)
  match t.action with
  | Clock -> false
  | _ -> true

let transition_has_progress t req_id =
  match t.action with
  | Progress ids -> StringSet.mem req_id ids
  | _ -> false

let build_outgoing_index transitions =
  let index = Hashtbl.create 16 in
  List.iter
    (fun t ->
      let existing =
        match Hashtbl.find_opt index t.from_state with
        | Some ts -> ts
        | None -> []
      in
      Hashtbl.replace index t.from_state (t :: existing))
    transitions;
  index

let get_outgoing_from_index index state_id =
  match Hashtbl.find_opt index state_id with
  | Some ts -> ts
  | None -> []

module TypeAutomaton = struct
  type t = typeAutomaton

  let create () =
    let states = Hashtbl.create 16 in
    Hashtbl.add states 0
      {
        id = 0;
        accepting = false;
        is_winning = false;
        is_fair = false;
        adversary = false;
        head = MsgSet.empty;
        head_clock = false;
        maybe_ready = MsgSet.empty;
        residual_type = None;
        product_components = [];
        debug_info = None;
      };
    {
      name = "";
      states;
      transitions = [];
      start_state = 0;
      next_state_id = 1;
    }

  let change_name id auto = auto.name <- id

  let new_state auto accepting =
    let id = auto.next_state_id in
    auto.next_state_id <- id + 1;
    Hashtbl.add auto.states id
      {
        id;
        accepting;
        is_winning = false;
        is_fair = false;
        adversary = false;
        head = MsgSet.empty;
        head_clock = false;
        maybe_ready = MsgSet.empty;
        residual_type = None;
        product_components = [];
        debug_info = None;
      };
    id

  let set_accepting auto state_id accepting =
    (Hashtbl.find auto.states state_id).accepting <- accepting

  let make_fair auto state_id =
    (Hashtbl.find auto.states state_id).is_fair <- true

  let make_adversary auto state_id =
    (Hashtbl.find auto.states state_id).adversary <- true

  let add_transition_full ?(boundary_now = MsgSet.empty)
      ?(boundary_future = MsgSet.empty) ?(boundary_guard = any_guard)
      ?internal_action ?(offers = MsgSet.empty) ?transition_debug_info auto
      from_state to_state action guard =
    let trans =
      {
        from_state;
        to_state;
        action;
        guard;
        boundary_now;
        boundary_future;
        boundary_guard;
        internal_action = Option.value internal_action ~default:action;
        maybe_offers = MsgSet.empty;
        offers;
        in_winning = false;
        transition_debug_info;
      }
    in
    if not (List.exists (( = ) trans) auto.transitions) then
      auto.transitions <- trans :: auto.transitions

  let add_transition auto from_state to_state action guard offer =
    add_transition_full auto from_state to_state  action guard ~offers:offer

  let accepting_states auto =
    Hashtbl.fold
      (fun id st acc -> if st.accepting then id :: acc else acc)
      auto.states []
end

let set_residual_type auto state_id residual =
  (* Residual metadata is debug-only; it does not participate in transitions. *)
  let st = Hashtbl.find auto.states state_id in
  st.residual_type <- Some (string_of_protocol residual)

let residual_debug_text = function
  | Some residual -> residual
  | None -> "?"

let string_of_product_component component =
  Printf.sprintf "%s:s%d = %s" component.pc_name component.pc_state
    (residual_debug_text component.pc_residual)

let string_of_product_components components =
  components
  |> List.map string_of_product_component
  |> String.concat "\n"

let state_debug_summary state =
  if state.product_components <> [] then
    "Product state map:\n" ^ string_of_product_components state.product_components
  else
    "Residual type: " ^ residual_debug_text state.residual_type

let component_name index auto =
  if auto.name = "" then Printf.sprintf "component%d" index else auto.name

let product_components_for_vector automata current_arr =
  Array.mapi
    (fun i state_id ->
      let component_state = Hashtbl.find automata.(i).states state_id in
      {
        pc_name = component_name i automata.(i);
        pc_state = state_id;
        pc_residual = component_state.residual_type;
      })
    current_arr
  |> Array.to_list

let product_residual_from_components components =
  let residuals =
    components
    |> List.filter_map (fun component -> component.pc_residual)
  in
  match residuals with
  | [] -> None
  | [ only ] -> Some only
  | _ -> Some ("(" ^ String.concat " || " residuals ^ ")")

let set_product_state_debug prod state_id components =
  let state = Hashtbl.find prod.states state_id in
  state.product_components <- components;
  state.residual_type <- product_residual_from_components components;
  state.debug_info <- Some (state_debug_summary state)

let append_state_debug state text =
  state.debug_info <-
    Some
      (match state.debug_info with
      | None -> text
      | Some existing -> existing ^ "\n" ^ text)

let product_state_map_debug auto =
  let ids =
    Hashtbl.fold (fun id _ acc -> id :: acc) auto.states []
    |> List.sort compare
  in
  ids
  |> List.map (fun id ->
         let st = Hashtbl.find auto.states id in
         if st.product_components = [] then
           Printf.sprintf "State %d: %s" id
             (residual_debug_text st.residual_type)
         else
           Printf.sprintf "State %d:\n%s" id
             (string_of_product_components st.product_components))
  |> String.concat "\n"

(* Recompute Head and MaybeReady from outgoing paths. *)
let recompute_state_summaries auto =
  Hashtbl.iter
    (fun _ st ->
      st.head <- MsgSet.empty;
      st.head_clock <- false;
      st.maybe_ready <- MsgSet.empty)
    auto.states;
  List.iter
    (fun t ->
      let offered =
        if MsgSet.is_empty t.offers then action_messages t.action else t.offers
      in
      if not (MsgSet.is_empty offered) then (
        let st = Hashtbl.find auto.states t.from_state in
        st.head <- MsgSet.union st.head offered;
        st.maybe_ready <- MsgSet.union st.maybe_ready offered);
      match t.action with
      | Clock ->
          (* The clock is part of Head. *)
          let st = Hashtbl.find auto.states t.from_state in
          st.head_clock <- true
      | _ -> ())
    auto.transitions;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun t ->
        if transition_keeps_cycle_future t then (
          let from_st = Hashtbl.find auto.states t.from_state in
          let to_st = Hashtbl.find auto.states t.to_state in
          let next_ready = MsgSet.union from_st.maybe_ready to_st.maybe_ready in
          if not (MsgSet.equal next_ready from_st.maybe_ready) then (
            from_st.maybe_ready <- next_ready;
            changed := true)))
      auto.transitions
  done;
  List.iter
    (fun t ->
      let to_st = Hashtbl.find auto.states t.to_state in
      t.maybe_offers <- to_st.maybe_ready)
    auto.transitions

let messages_of_transition t =
  MsgSet.union (action_messages t.action)
    (MsgSet.union t.offers (MsgSet.union t.guard.require_now t.guard.forbid_now))
  |> fun acc ->
  List.fold_left MsgSet.union acc t.guard.missing_now_groups

(* Collect every message mentioned by states, actions, and guards. *)
let messages_of_automaton auto =
  recompute_state_summaries auto;
  let from_states =
    Hashtbl.fold
      (fun _ st acc ->
        MsgSet.union acc (MsgSet.union st.head st.maybe_ready))
      auto.states MsgSet.empty
  in
  List.fold_left
    (fun acc t -> MsgSet.union acc (messages_of_transition t))
    from_states auto.transitions

(* Splice a separately built automaton into an existing builder graph. *)
let import_automaton_into ~dst ~src ~at_start =
  recompute_state_summaries src;
  let state_map = Hashtbl.create 16 in
  Hashtbl.add state_map src.start_state at_start;
  Hashtbl.iter
    (fun src_id src_st ->
      if src_id <> src.start_state then
        let dst_id = TypeAutomaton.new_state dst src_st.accepting in
        Hashtbl.add state_map src_id dst_id)
    src.states;
  Hashtbl.iter
    (fun src_id src_st ->
      let dst_id = Hashtbl.find state_map src_id in
      let dst_st = Hashtbl.find dst.states dst_id in
      dst_st.accepting <- src_st.accepting;
      dst_st.is_fair <- src_st.is_fair;
      dst_st.adversary <- src_st.adversary;
      dst_st.head <- src_st.head;
      dst_st.head_clock <- src_st.head_clock;
      dst_st.maybe_ready <- src_st.maybe_ready;
      dst_st.residual_type <- src_st.residual_type;
      dst_st.product_components <- src_st.product_components;
      dst_st.debug_info <- src_st.debug_info)
    src.states;
  List.iter
    (fun t ->
      TypeAutomaton.add_transition_full
        ~boundary_now:t.boundary_now
        ~boundary_future:t.boundary_future
        ~boundary_guard:t.boundary_guard
        ~offers:t.offers
        ?transition_debug_info:t.transition_debug_info dst
        (Hashtbl.find state_map t.from_state)
        (Hashtbl.find state_map t.to_state)
        t.action t.guard)
    src.transitions;
  Hashtbl.fold
    (fun src_id src_st acc ->
      if src_st.accepting then Hashtbl.find state_map src_id :: acc else acc)
    src.states []

let cartesian_product lists =
  let rec aux = function
    | [] -> [ [] ]
    | xs :: rest ->
        let tails = aux rest in
        List.concat
          (List.map (fun x -> List.map (fun tail -> x :: tail) tails) xs)
  in
  aux lists

(* Combine component guards for simultaneous local product transitions. *)
let merge_guards guards =
  List.fold_left
    (fun acc guard ->
      {
        require_now = MsgSet.union acc.require_now guard.require_now;
        forbid_now = MsgSet.union acc.forbid_now guard.forbid_now;
        missing_now_groups = acc.missing_now_groups @ guard.missing_now_groups;
        exists_now_groups = acc.exists_now_groups @ guard.exists_now_groups;
        require_clock = acc.require_clock || guard.require_clock;
        forbid_clock = acc.forbid_clock || guard.forbid_clock;
        future_disjoint = MsgSet.union acc.future_disjoint guard.future_disjoint;
        subset_now = MsgSet.union acc.subset_now guard.subset_now;
        future_intersects = acc.future_intersects @ guard.future_intersects;
      })
    any_guard guards

let add_progress_transition auto from_state to_state ids =
  let id_set =
    List.fold_left (fun acc id -> StringSet.add id acc) StringSet.empty ids
  in
  TypeAutomaton.add_transition auto from_state to_state (Progress id_set)
    any_guard  MsgSet.empty

(* Closed product: all sync_messages must be consumed internally. *)
(* Unified synchronous product for internal parallel, closed, and open compositions.
   - boundary_messages: messages visible to the environment (open boundary); empty for internal/closed.
   - internal_messages = all_messages - boundary_messages must be paired (≥2 components).
   - use_env: if true, compute environments from partner components' Head/MaybeReady (closed/open).
     if false, use simple cartesian product (internal parallel). *)
let unified_product ?progress_ids ?(verbose = false) automata ~boundary_messages
    ~use_env =
  let _ = progress_ids in
  Array.iter recompute_state_summaries automata;
  let product_debug_enabled = SessionAutomaton2Debug.enabled ~verbose in
  let prod = TypeAutomaton.create () in
  let state_map = Hashtbl.create 32 in
  let start_vector = Array.to_list (Array.map (fun auto -> auto.start_state) automata) in
  Hashtbl.add state_map start_vector prod.start_state;
  let outgoing =
    Array.map (fun auto -> build_outgoing_index auto.transitions) automata
  in
  let own_messages = Array.map messages_of_automaton automata in
  (* Compute internal messages: all messages except boundary. *)
  let all_messages =
    Array.fold_left (fun acc msgs -> MsgSet.union acc msgs) MsgSet.empty own_messages
  in
  let internal_messages = MsgSet.diff all_messages boundary_messages in
  let get_product_state states =
    match Hashtbl.find_opt state_map states with
    | Some id -> id
    | None ->
        let id = TypeAutomaton.new_state prod false in
        Hashtbl.add state_map states id;
        id
  in
  let queue = Queue.create () in
  let visited = Hashtbl.create 32 in
  Queue.add start_vector queue;
  let enqueue states =
    if not (Hashtbl.mem visited states) then Queue.add states queue
  in
  let add_product_transition ?(boundary_now = MsgSet.empty)
      ?(boundary_future = MsgSet.empty) ?(boundary_guard = any_guard)
      ?internal_action from_vec to_vec action guard offer =
    let from_id = get_product_state from_vec in
    let to_id = get_product_state to_vec in
    TypeAutomaton.add_transition_full ~boundary_now ~boundary_future
      ~boundary_guard ?internal_action ~offers:offer prod from_id to_id action
      guard;
    if to_vec <> from_vec then enqueue to_vec
  in
  let debug_env env =
    SessionAutomaton2Debug.format_env ~imm:(string_of_msgset env.imm)
      ~future:(string_of_msgset env.future) ~clock:env.clock
  in
  let sync_ok component_msgs combined =
    (* Check that internal messages are paired (≥2 components for each internal msg). *)
    let internal_in_combined = MsgSet.inter combined internal_messages in
    MsgSet.for_all
      (fun msg ->
        let count =
          Array.fold_left
            (fun acc msgs -> if MsgSet.mem msg msgs then acc + 1 else acc)
            0 component_msgs
        in
        count >= 2)
      internal_in_combined
  in
  while not (Queue.is_empty queue) do
    let current = Queue.take queue in
    if not (Hashtbl.mem visited current) then (
      Hashtbl.add visited current ();
      let prod_state = get_product_state current in
      let current_arr = Array.of_list current in
      let prod_state_info = Hashtbl.find prod.states prod_state in
      set_product_state_debug prod prod_state
        (product_components_for_vector automata current_arr);
      prod_state_info.is_fair <-
        Array.mapi
          (fun i st_id -> (Hashtbl.find automata.(i).states st_id).is_fair)
          current_arr
        |> Array.to_list
        |> List.exists (fun x -> x);
      prod_state_info.adversary <-
        Array.mapi
          (fun i st_id -> (Hashtbl.find automata.(i).states st_id).adversary)
          current_arr
        |> Array.to_list
        |> List.exists (fun x -> x);
      let all_accepting =
        Array.mapi
          (fun i st_id -> (Hashtbl.find automata.(i).states st_id).accepting)
          current_arr
        |> Array.to_list
        |> List.for_all (fun x -> x)
      in
      if all_accepting then prod_state_info.accepting <- true;
        (* Unified sync product: every component picks exactly ONE outgoing transition
           (its real transitions, including guarded self-loops — no synthetic passive).
           We take the cartesian product, then for each combo:
             - combine the actions (union messages; clock must be unanimous),
             - merge the component guards,
             - in use_env mode, drop the combo if any component's INTERNAL-message
               guard is not satisfied by its local environment,
             - apply the sync check (internal messages paired; clock all-or-none),
           then group combos by (next_state, action) and merge their guards. *)

        (* Per-component outgoing choices: only transitions already present in the
           component automata are allowed. *)
        let component_choices =
          Array.mapi
            (fun i st_id -> (i, st_id, get_outgoing_from_index outgoing.(i) st_id))
            current_arr
          |> Array.to_list
          |> List.map (fun (i, _, outs) ->
                 List.map
                   (fun t ->
                     (i, t.to_state, t.action, t.guard, t.offers, t.maybe_offers))
                   outs)
        in

        if List.for_all (fun choices -> choices <> []) component_choices then (
          let combos = cartesian_product component_choices in
          (* Group by (next_state_vector, action); merge guards of grouped combos. *)
          let grouped = Hashtbl.create 16 in
          List.iter
            (fun combo ->
              (* combo : (component_index, to_state, action, guard, offers, maybe_offers) list, one per component. *)
              let next =
                combo
                |> List.map (fun (i, to_state, _, _, _, _) -> (i, to_state))
                |> List.sort (fun (a, _) (b, _) -> compare a b)
                |> List.map snd
              in
              let actions = List.map (fun (_, _, act, _, _, _) -> act) combo in
              let guards = List.map (fun (_, _, _, g, _, _) -> g) combo in

              let all_partners_clock = ref true in
              let has_partner = ref false in
              let local_envs =
                Array.mapi
                  (fun i _st_id ->
                    let imm = ref MsgSet.empty in
                    let future = ref MsgSet.empty in
                    List.iter
                      (fun (j, _, _, _, offers, _maybe_offers) ->
                        if i <> j then (
                          has_partner := true;
                          let other =
                            Hashtbl.find automata.(j).states current_arr.(j)
                          in
                          imm := MsgSet.union !imm offers;
                          future :=
                            MsgSet.union !future
                              (MsgSet.diff other.maybe_ready offers);
                          if not other.head_clock then
                            all_partners_clock := false))
                      combo;
                    let imm =
                      !imm
                      |> MsgSet.inter internal_messages
                      |> MsgSet.inter own_messages.(i)
                    in
                    let future =
                      !future
                      |> MsgSet.inter internal_messages
                      |> MsgSet.inter own_messages.(i)
                    in
                    (* clock resolved per hypothesis below. *)
                    { imm; future; clock = false })
                  current_arr
              in
              let partners_offer_clock = !has_partner && !all_partners_clock in

              (* Clock treatment during guard satisfaction.

                 Closed (no boundary messages): the clock is internal. Partners must
                 all tick, so the environment clock is exactly partners_offer_clock
                 and the clock conditions (require_clock/forbid_clock) are checked
                 against it internally.

                 Open (some boundary messages): the clock is decided by the current
                 environment. If the environment HAS the clock (all internal partners
                 offer it) we treat the clock as a BOUNDARY action: its conditions are
                 dropped from the internal check and instead ride the boundary env
                 (be_clock below), so the game/player resolves provide-vs-withhold. If
                 the environment does NOT have the clock, we treat it as internal and
                 check the guard against an environment without the clock (clock=false). *)
              let clock_is_boundary =
                (not (MsgSet.is_empty boundary_messages)) && partners_offer_clock
              in
              let internal_env_clock =
                if clock_is_boundary then false else partners_offer_clock
              in
              let strip_clock g =
                if clock_is_boundary then
                  { g with require_clock = false; forbid_clock = false }
                else g
              in
              let guard_checks =
                List.map
                  (fun (i, _, _act, g, _, _) ->
                    let env = { local_envs.(i) with clock = internal_env_clock } in
                    let projected_guard =
                      strip_clock (project_guard_to internal_messages g)
                    in
                    (i, guard_satisfied env projected_guard, projected_guard, env))
                  combo
              in
              let step1_ok =
                (not use_env)
                || List.for_all (fun (_, ok, _, _) -> ok) guard_checks
              in

              (* STEP 2: sync check on actions.
                 - Clock: all components pick clock, or none do.
                 - Internal messages: each must be picked by >= 2 components.
                 - Boundary messages: no constraint. *)
              let clock_count =
                List.fold_left
                  (fun acc act -> match act with Clock -> acc + 1 | _ -> acc)
                  0 actions
              in
              let clock_ok = clock_count = 0 || clock_count = List.length actions in

              let component_msgs =
                actions
                |> List.map (function Messages m -> m | _ -> MsgSet.empty)
                |> Array.of_list
              in
              let combined_msgs =
                Array.fold_left MsgSet.union MsgSet.empty component_msgs
              in
              let combined_progress =
                actions
                |> List.fold_left
                     (fun acc -> function
                       | Progress ids -> StringSet.union acc ids
                       | _ -> acc)
                     StringSet.empty
              in
              let combined_action =
                if clock_count = List.length actions && clock_count > 0 then Clock
                else if not (MsgSet.is_empty combined_msgs) then
                  Messages combined_msgs
                else if not (StringSet.is_empty combined_progress) then
                  Progress combined_progress
                else Epsilon
              in
              let sync_ok_msgs =
                match combined_action with
                | Messages _ -> sync_ok component_msgs combined_msgs
                | _ -> true
              in
              let combined_offers =
                combo
                |> List.map (fun (_, _, _, _, offers, _) -> offers)
                |> List.fold_left MsgSet.union MsgSet.empty
              in
              let combined_maybe_offers =
                combo
                |> List.map (fun (_, _, _, _, _, maybe_offers) -> maybe_offers)
                |> List.fold_left MsgSet.union MsgSet.empty
              in

              (* Boundary projection E_B = (U, F): the mirror of STEP 1's internal
                 projection. The same merged combo guard is projected onto the
                 boundary messages (the pending part left for the environment).
                 U = the boundary messages this round genuinely requires now
                 (guard.require_now ∪ guard.subset_now on the boundary side —
                 both express "the environment must be offering this now",
                 exact vs subset; a transition guarded only by subset_now, e.g.
                 a plain message-firing edge, must still surface its message in
                 U or two boundary-distinct transitions collapse into the same
                 θ move and the choice between them wrongly becomes the
                 system's instead of the environment's); F = boundary messages
                 that may still arrive this cycle (guard.future_intersects plus
                 the components' maybe_offers), minus U. Offers presented now do
                 NOT force a boundary message into U — only require_now/subset_now
                 does, so a combo that fires just m1 does not spuriously demand m2
                 from the environment. Empty when boundary_messages = ∅ (closed). *)
              let merged_guard = merge_guards guards in
              let boundary_guard =
                project_guard_to boundary_messages merged_guard
              in
              let be_now =
                MsgSet.union boundary_guard.require_now boundary_guard.subset_now
              in
              let be_future =
                boundary_guard.future_intersects
                |> List.fold_left MsgSet.union
                     (MsgSet.inter combined_maybe_offers boundary_messages)
                |> fun set -> MsgSet.diff set be_now
              in

              (* Suppress the trivial all-epsilon self-loop that changes nothing and has no
                 guard (it carries no information); keep guarded epsilon waits. *)
              let changed = next <> current in
              let keep =
                match combined_action with
                | Epsilon -> changed || not (guard_is_any (merge_guards guards))
                | _ -> true
              in
              let picked = step1_ok && clock_ok && sync_ok_msgs && keep in
              (if product_debug_enabled then (
                let component_lines =
                  List.map
                    (fun (i, to_state, action, guard, offers, maybe_offers) ->
                      SessionAutomaton2Debug.component_pick_line
                        ~component:(component_name i automata.(i))
                        ~from_state:current_arr.(i)
                        ~action:(string_of_action action)
                        ~offers:(string_of_msgset offers)
                        ~maybe_offers:(string_of_msgset maybe_offers)
                        ~guard:(string_of_guard guard)
                        ~env:(debug_env local_envs.(i))
                        ~to_state)
                    combo
                in
                let guard_lines =
                  List.map
                    (fun (i, ok, projected_guard, env) ->
                      SessionAutomaton2Debug.guard_check_line
                        ~component:(component_name i automata.(i))
                        ~state_id:current_arr.(i) ~ok
                        ~guard:(string_of_guard projected_guard)
                        ~env:(debug_env env))
                    guard_checks
                in
                SessionAutomaton2Debug.print_combo_verdict
                  ~verbose:product_debug_enabled
                  {
                    picked;
                    from_state =
                      current_arr |> Array.to_list |> List.map string_of_int
                      |> String.concat ",";
                    action = string_of_action combined_action;
                    next_state =
                      next |> List.map string_of_int |> String.concat ",";
                    step1_ok;
                    use_env;
                    clock_ok;
                    clock_count;
                    component_count = List.length combo;
                    sync_ok = sync_ok_msgs;
                    changed;
                      keep;
                      combined_msgs = string_of_msgset combined_msgs;
                      component_lines;
                      guard_lines;
                  }));

              if picked then (
                (* The transition carries the FULL merged guard (the closed game
                   and dead-end analysis rely on it). The boundary (pending) part
                   is kept separately in boundary_guard for the residual/next-step
                   composition; the internal part is what STEP 1 already checked. *)
                let guard = merged_guard in
                let state_key = String.concat "," (List.map string_of_int next) in
                let action_key = string_of_action combined_action in
                let key = state_key ^ "|" ^ action_key in
                match Hashtbl.find_opt grouped key with
                | Some
                    ( stored_next,
                      stored_action,
                      stored_offers,
                      existing_guard,
                      stored_be_now,
                      stored_be_future,
                      stored_boundary_guard ) ->
                    (* Merging combos into one grouped edge: union the boundary
                       availabilities and merge the pending guards, matching how
                       offers/guards already merge here. *)
                    Hashtbl.replace grouped key
                      ( stored_next,
                        stored_action,
                        MsgSet.union stored_offers combined_offers,
                        merge_guards [ existing_guard; guard ],
                        MsgSet.union stored_be_now be_now,
                        MsgSet.union stored_be_future be_future,
                        merge_guards [ stored_boundary_guard; boundary_guard ] )
                | None ->
                    Hashtbl.add grouped key
                      ( next,
                        combined_action,
                        combined_offers,
                        guard,
                        be_now,
                        be_future,
                        boundary_guard )
              ))
            combos;
          (* Emit one transition per grouped (next_state, action). *)
          Hashtbl.iter
            (fun _key
                 ( next,
                   combined_action,
                   combined_offers,
                   guard,
                   be_now,
                   be_future,
                   boundary_guard ) ->
              let internal_action =
                match combined_action with
                | Messages msgs ->
                    let internal_msgs = MsgSet.inter msgs internal_messages in
                    if MsgSet.is_empty internal_msgs then Epsilon
                    else Messages internal_msgs
                | other -> other
              in
              add_product_transition ~boundary_now:be_now
                ~boundary_future:be_future ~boundary_guard ~internal_action
                current next combined_action guard combined_offers)
            grouped))
  done;
  recompute_state_summaries prod;
  prod

let closed_product ?progress_ids ?(verbose = false) automata sync_messages =
  (* Closed product: all messages except those explicitly in sync_messages are boundary. *)
  let all_messages =
    Array.fold_left
      (fun acc auto -> MsgSet.union acc (messages_of_automaton auto))
      MsgSet.empty automata
  in
  let boundary_messages = MsgSet.diff all_messages sync_messages in
  unified_product ?progress_ids ~verbose automata ~boundary_messages ~use_env:true

(* Local parallel product exposes component messages instead of synchronizing them. *)
(* Add unguarded epsilon self-loops to all accepting states (for internal parallel preprocessing). *)
let add_final_state_epsilon_loops auto =
  let states_to_update = ref [] in
  Hashtbl.iter
    (fun _id state ->
      if state.accepting then states_to_update := state.id :: !states_to_update)
    auto.states;
  List.iter
    (fun state_id ->
      TypeAutomaton.add_transition auto state_id state_id Epsilon any_guard
        MsgSet.empty)
    !states_to_update

(* Remove unguarded epsilon self-loops only from the product's final states.
   These are the preprocessing epsilons added before the product. *)
let remove_final_state_epsilon_loops auto =
  (* Find which states are final (accepting) in the product. *)
  let final_states = ref [] in
  Hashtbl.iter
    (fun _id state ->
      if state.accepting then final_states := state.id :: !final_states)
    auto.states;
  let final_state_set =
    List.fold_left (fun acc id -> IntSet.add id acc) IntSet.empty !final_states
  in
  auto.transitions <-
    List.filter
      (fun t ->
        match t.action with
        | Epsilon when t.from_state = t.to_state && guard_is_any t.guard ->
            (* Remove only if it's an unguarded epsilon self-loop on a final state *)
            not (IntSet.mem t.from_state final_state_set)
        | _ -> true)
      auto.transitions


let escape_dot s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let escape_html s =
  let b = Buffer.create (String.length s) in
  String.iter
    (function
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '"' -> Buffer.add_string b "&quot;"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let html_of_msgset set =
  "{"
  ^ (set
    |> MsgSet.elements
    |> List.map (fun msg -> escape_html (string_of_msg_spec msg))
    |> String.concat ", ")
  ^ "}"

let html_of_string_set set =
  "{"
  ^ (set
    |> StringSet.elements
    |> List.map (fun id -> "$" ^ escape_html id)
    |> String.concat ", ")
  ^ "}"

let html_of_residual residual =
  residual_debug_text residual |> escape_html

let html_of_text_block text =
  text
  |> String.split_on_char '\n'
  |> List.map escape_html
  |> String.concat "<BR/>"

let html_of_action = function
  | Epsilon -> "α = ε"
  | Messages msgs -> "α = " ^ html_of_msgset msgs
  | Clock -> "α = {#}"
  | Progress ids -> "α = " ^ html_of_string_set ids
  | FairBranch (id, branch) ->
      "α = {" ^ escape_html id ^ (if branch then "_true" else "_false") ^ "}"

let html_of_guard g =
  let parts = ref [] in
  let add pred = parts := pred :: !parts in
  let add_msg pred msgs =
    if not (MsgSet.is_empty msgs) then add (pred (html_of_msgset msgs))
  in
  add_msg (fun s -> s ^ " = Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " ∩ Imm(E) = ∅") g.forbid_now;
  add_msg (fun s -> s ^ " ⊆ Imm(E)") g.subset_now;
  if g.missing_now_groups <> [] then
    add
      ("∀G ∈ ["
       ^ (g.missing_now_groups |> List.map html_of_msgset |> String.concat "; ")
       ^ "]. ¬(G ⊆ Imm(E))");
  if g.exists_now_groups <> [] then
    add
      ("∃G ∈ ["
       ^ (g.exists_now_groups |> List.map html_of_msgset |> String.concat "; ")
       ^ "]. G ∩ Imm(E) ≠ ∅");
  if g.require_clock then add "# ∈ Imm(E)";
  if g.forbid_clock then add "# ∉ Imm(E)";
  add_msg (fun s -> s ^ " ∩ F = ∅") g.future_disjoint;
  if g.future_intersects <> [] then
    add
      ("∀G ∈ ["
       ^ (g.future_intersects |> List.map html_of_msgset |> String.concat "; ")
       ^ "]. G ∩ F ≠ ∅");
  match List.rev !parts with
  | [] -> "true"
  | xs -> String.concat "<BR/>" xs

let html_of_boundary_projection ?(show_empty = false) t =
  if
    (not show_empty)
    && MsgSet.is_empty t.boundary_now
    && MsgSet.is_empty t.boundary_future
  then
    ""
  else
    "<BR/>E_B: U = " ^ html_of_msgset t.boundary_now ^ "; F = "
    ^ html_of_msgset t.boundary_future

(* Render the v2 metadata directly in DOT for debugging the formal construction. *)
let print_automaton_dot ?(show_guards = true) ?(show_transition_debug = true)
    ?(show_empty_boundary = false) auto out =
  recompute_state_summaries auto;
  Printf.fprintf out "digraph TypeAutomaton2 {\n";
  Printf.fprintf out "  rankdir=LR;\n";
  Printf.fprintf out "  __start [shape=none,label=\"\"];\n";
  Printf.fprintf out "  __start -> %d [color=grey];\n" auto.start_state;
  let ids =
    Hashtbl.fold (fun id _ acc -> id :: acc) auto.states []
    |> List.sort compare
  in
  List.iter
    (fun id ->
      let st = Hashtbl.find auto.states id in
      let shape =
        if st.accepting then "doublecircle"
        else if st.adversary then "square"
        else "circle"
      in
      let color =
        if st.is_winning then "darkgreen"
        else if st.is_fair then "orange"
        else "black"
      in
      let label =
        Printf.sprintf "%d<BR/>H = %s<BR/>F = %s<BR/>R = %s" id
          (html_of_msgset st.head)
          (html_of_msgset st.maybe_ready)
          (html_of_residual st.residual_type)
      in
      Printf.fprintf out "  %d [shape=%s,color=%s,label=<%s>];\n" id shape
        color label)
    ids;
  List.iter
    (fun t ->
      let label =
        let base =
          if (not show_guards) || guard_is_any t.guard then
            html_of_action t.action
          else
            html_of_action t.action ^ "<BR/>satisfied: " ^ html_of_guard t.guard
        in
        (* The internal label is the combined action projected onto
           internal_messages — what actually synchronized to satisfy the
           guard, as opposed to `action`'s full (possibly boundary-mixed)
           label. Only shown when it differs, so closed-product transitions
           (where every message is internal) stay unchanged. *)
        let internal_label =
          if (not show_guards) || t.internal_action = t.action then ""
          else "<BR/>internal: " ^ html_of_action t.internal_action
        in
        (* The pending (boundary-projected) guard is what the environment still
           has to discharge; show it separately from the satisfied guard. *)
        let pending =
          if (not show_guards) || guard_is_any t.boundary_guard then ""
          else "<BR/>pending: " ^ html_of_guard t.boundary_guard
        in
        let boundary =
          html_of_boundary_projection ~show_empty:show_empty_boundary t
        in
        let offers =
          if MsgSet.is_empty t.offers then "" else "<BR/>O = " ^ html_of_msgset t.offers
        in
        let debug =
          match show_transition_debug, t.transition_debug_info with
          | false, _ -> ""
          | true, None -> ""
          | true, Some info -> "<BR/>" ^ html_of_text_block info
        in
        base ^ internal_label ^ pending ^ offers ^ boundary ^ debug
      in
      Printf.fprintf out "  %d -> %d [label=<%s>];\n" t.from_state
        t.to_state label)
    (List.rev auto.transitions);
  Printf.fprintf out "}\n"
