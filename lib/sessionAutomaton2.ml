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
  require_now : MsgSet.t; (* require_now ⊆ Imm(E) *)
  forbid_now : MsgSet.t; (* forbid_now ∩ Imm(E) = ∅ *)
  missing_now_groups : MsgSet.t list; (* ∀G. G ∈ missing_now_groups ⇒ G ⊄ Imm(E) *)
  require_clock : bool; (* require_clock ⇒ # ∈ Imm(E) *)
  forbid_clock : bool; (* forbid_clock ⇒ # ∉ Imm(E) *)
  future_disjoint : MsgSet.t; (* future_disjoint ∩ F = ∅ *)
}

let any_guard = {
  require_now = MsgSet.empty;
  forbid_now = MsgSet.empty;
  missing_now_groups = [];
  require_clock = false;
  forbid_clock = false;
  future_disjoint = MsgSet.empty;
}

let guard_is_any g =
  MsgSet.is_empty g.require_now
  && MsgSet.is_empty g.forbid_now
  && g.missing_now_groups = []
  && not g.require_clock
  && not g.forbid_clock
  && MsgSet.is_empty g.future_disjoint

(* Local view of what is immediate now and possible later in this cycle. *)
type env = {
  imm : MsgSet.t;
  future : MsgSet.t;
  clock : bool;
}

let empty_env = { imm = MsgSet.empty; future = MsgSet.empty; clock = false }

let clock_guard_env env =
  (* Clock actions still inspect the resolved message/future side conditions. *)
  { env with clock = true }

(* A transition is enabled exactly when its symbolic guard matches the local view. *)
let guard_satisfied env g =
  let missing_group group = not (MsgSet.subset group env.imm) in
  MsgSet.subset g.require_now env.imm
  && MsgSet.disjoint g.forbid_now env.imm
  && List.for_all missing_group g.missing_now_groups
  && ((not g.require_clock) || env.clock)
  && ((not g.forbid_clock) || not env.clock)
  && MsgSet.disjoint g.future_disjoint env.future

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
  add_msg (fun s -> s ^ " subset Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " cap Imm(E) = empty") g.forbid_now;
  if g.missing_now_groups <> [] then
    add
      ("forall G in ["
       ^ (g.missing_now_groups
          |> List.map fmt_msgset
          |> String.concat ";")
       ^ "]. not (G subset Imm(E))");
  if g.require_clock then add "# in Imm(E)";
  if g.forbid_clock then add "# notin Imm(E)";
  add_msg (fun s -> s ^ " cap F = empty") g.future_disjoint;
  match List.rev !parts with
  | [] -> "true"
  | xs -> String.concat " && " xs

(* Head and maybe_ready cache the formal Head/MaybeReady sets. *)
type state = {
  id : int;
  mutable accepting : bool;
  mutable is_winning : bool;
  mutable is_fair : bool;
  mutable adversary : bool;
  mutable head : MsgSet.t;
  mutable maybe_ready : MsgSet.t;
  mutable debug_info : string option;
}

type transition = {
  from_state : int;
  to_state : int;
  action : action;
  guard : guard;
  mutable maybe_offers : MsgSet.t;
  mutable in_winning : bool;
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
        maybe_ready = MsgSet.empty;
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
        maybe_ready = MsgSet.empty;
        debug_info = None;
      };
    id

  let set_accepting auto state_id accepting =
    (Hashtbl.find auto.states state_id).accepting <- accepting

  let make_fair auto state_id =
    (Hashtbl.find auto.states state_id).is_fair <- true

  let make_adversary auto state_id =
    (Hashtbl.find auto.states state_id).adversary <- true

  let add_transition auto from_state to_state action guard =
    let trans =
      {
        from_state;
        to_state;
        action;
        guard;
        maybe_offers = MsgSet.empty;
        in_winning = false;
      }
    in
    if not (List.exists (( = ) trans) auto.transitions) then
      auto.transitions <- trans :: auto.transitions

  let accepting_states auto =
    Hashtbl.fold
      (fun id st acc -> if st.accepting then id :: acc else acc)
      auto.states []
end

(* Recompute Head and MaybeReady from outgoing non-clock paths. *)
let recompute_state_summaries auto =
  Hashtbl.iter
    (fun _ st ->
      st.head <- MsgSet.empty;
      st.maybe_ready <- MsgSet.empty)
    auto.states;
  List.iter
    (fun t ->
      match t.action with
      | Messages msgs ->
          let st = Hashtbl.find auto.states t.from_state in
          st.head <- MsgSet.union st.head msgs;
          st.maybe_ready <- MsgSet.union st.maybe_ready msgs
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
    (MsgSet.union t.guard.require_now t.guard.forbid_now)
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
      dst_st.maybe_ready <- src_st.maybe_ready;
      dst_st.debug_info <- src_st.debug_info)
    src.states;
  List.iter
    (fun t ->
      TypeAutomaton.add_transition dst
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
        require_clock = acc.require_clock || guard.require_clock;
        forbid_clock = acc.forbid_clock || guard.forbid_clock;
        future_disjoint = MsgSet.union acc.future_disjoint guard.future_disjoint;
      })
    any_guard guards

let add_progress_transition auto from_state to_state ids =
  let id_set =
    List.fold_left (fun acc id -> StringSet.add id acc) StringSet.empty ids
  in
  TypeAutomaton.add_transition auto from_state to_state (Progress id_set) any_guard

(* Closed product: all sync_messages must be consumed internally. *)
let closed_product ?progress_ids automata sync_messages =
  Array.iter recompute_state_summaries automata;
  let prod = TypeAutomaton.create () in
  let state_map = Hashtbl.create 32 in
  let start_vector = Array.to_list (Array.map (fun auto -> auto.start_state) automata) in
  Hashtbl.add state_map start_vector prod.start_state;
  let outgoing =
    Array.map (fun auto -> build_outgoing_index auto.transitions) automata
  in
  let own_messages = Array.map messages_of_automaton automata in
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
  let add_product_transition from_vec to_vec action guard =
    let from_id = get_product_state from_vec in
    let to_id = get_product_state to_vec in
    TypeAutomaton.add_transition prod from_id to_id action guard;
    if to_vec <> from_vec then enqueue to_vec
  in
  let sync_ok component_msgs combined =
    MsgSet.for_all
      (fun msg ->
        let count =
          Array.fold_left
            (fun acc msgs -> if MsgSet.mem msg msgs then acc + 1 else acc)
            0 component_msgs
        in
        count >= 2)
      combined
  in
  while not (Queue.is_empty queue) do
    let current = Queue.take queue in
    if not (Hashtbl.mem visited current) then (
      Hashtbl.add visited current ();
      let prod_state = get_product_state current in
      let current_arr = Array.of_list current in
      let prod_state_info = Hashtbl.find prod.states prod_state in
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
      if all_accepting then (
        (Hashtbl.find prod.states prod_state).accepting <- true;
        match progress_ids with
        | Some ids -> add_progress_transition prod prod_state prod.start_state ids
        | None ->
            if
              not
                (List.exists
                   (fun t -> t.from_state = prod_state)
                   prod.transitions)
            then
              prod_state_info.debug_info <-
                Some
                  "All components are accepting, but no product progress transition was configured.")
      else (
        Array.iteri
          (fun i st_id ->
            let outs = get_outgoing_from_index outgoing.(i) st_id in
            List.iter
              (fun t ->
                match t.action with
                | Epsilon | Progress _ | FairBranch _ when guard_is_any t.guard ->
                    let next =
                      List.mapi
                        (fun j s -> if i = j then t.to_state else s)
                        current
                    in
                    add_product_transition current next t.action t.guard
                | _ -> ())
              outs)
          current_arr;

        (* Partners' Head/MaybeReady sets become each component's local environment. *)
        let local_envs =
          Array.mapi
            (fun i _st_id ->
              let imm = ref MsgSet.empty in
              let future = ref MsgSet.empty in
              Array.iteri
                (fun j other_id ->
                  if i <> j then (
                    let other = Hashtbl.find automata.(j).states other_id in
                    imm := MsgSet.union !imm other.head;
                    future := MsgSet.union !future other.maybe_ready))
                current_arr;
              let imm =
                !imm
                |> MsgSet.inter sync_messages
                |> MsgSet.inter own_messages.(i)
              in
              let future =
                !future
                |> MsgSet.inter sync_messages
                |> MsgSet.inter own_messages.(i)
                |> fun f -> MsgSet.diff f imm
              in
              { imm; future; clock = false })
            current_arr
        in
        let env_choices =
          Array.mapi
            (fun i st_id ->
              let outs = get_outgoing_from_index outgoing.(i) st_id in
              let passive =
                {
                  mc_to_state = st_id;
                  mc_actions = MsgSet.empty;
                  mc_changed = false;
                }
              in
              let transition_choices =
                outs
                |> List.filter_map (fun t ->
                       match t.action with
                       | Messages _ | Epsilon
                         when (not (guard_is_any t.guard))
                              && guard_satisfied local_envs.(i) t.guard ->
                           Some
                             {
                               mc_to_state = t.to_state;
                               mc_actions = action_messages t.action;
                               mc_changed =
                                 t.to_state <> st_id || t.action <> Epsilon;
                             }
                       | _ -> None)
              in
              passive :: transition_choices)
            current_arr
          |> Array.to_list
        in
        if List.for_all (fun choices -> choices <> []) env_choices then
          env_choices
          |> cartesian_product
          |> List.iter (fun combo ->
                 let next = List.map (fun choice -> choice.mc_to_state) combo in
                 let component_msgs =
                   combo |> List.map (fun choice -> choice.mc_actions) |> Array.of_list
                 in
                 let combined =
                   Array.fold_left MsgSet.union MsgSet.empty component_msgs
                 in
                 let changed = List.exists (fun choice -> choice.mc_changed) combo in
                 if
                   (changed || not (MsgSet.is_empty combined))
                   && (MsgSet.is_empty combined || sync_ok component_msgs combined)
                 then
                   let action =
                     if MsgSet.is_empty combined then Epsilon else Messages combined
                   in
                   add_product_transition current next action any_guard);

        let clock_choices =
          let clock_envs =
            Array.map clock_guard_env local_envs
          in
          Array.mapi
            (fun i st_id ->
              let outs = get_outgoing_from_index outgoing.(i) st_id in
              (* A product clock round exists only when every component clocks. *)
              outs
              |> List.filter (fun t ->
                     match t.action with
                     | Clock -> guard_satisfied clock_envs.(i) t.guard
                     | _ -> false)
              |> List.map (fun t -> t.to_state))
            current_arr
          |> Array.to_list
        in
        if List.for_all (fun choices -> choices <> []) clock_choices then
          clock_choices
          |> cartesian_product
          |> List.iter (fun next ->
                 add_product_transition current next Clock any_guard)))
  done;
  recompute_state_summaries prod;
  prod

(* Local parallel product exposes component messages instead of synchronizing them. *)
let async_product automata =
  Array.iter recompute_state_summaries automata;
  let prod = TypeAutomaton.create () in
  let state_map = Hashtbl.create 32 in
  let start_vector = Array.to_list (Array.map (fun auto -> auto.start_state) automata) in
  Hashtbl.add state_map start_vector prod.start_state;
  let outgoing =
    Array.map (fun auto -> build_outgoing_index auto.transitions) automata
  in
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
  let add_product_transition from_vec to_vec action guard =
    let from_id = get_product_state from_vec in
    let to_id = get_product_state to_vec in
    TypeAutomaton.add_transition prod from_id to_id action guard;
    if to_vec <> from_vec then enqueue to_vec
  in
  while not (Queue.is_empty queue) do
    let current = Queue.take queue in
    if not (Hashtbl.mem visited current) then (
      Hashtbl.add visited current ();
      let prod_state = get_product_state current in
      let current_arr = Array.of_list current in
      let prod_state_info = Hashtbl.find prod.states prod_state in
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
      if all_accepting then
        (Hashtbl.find prod.states prod_state).accepting <- true;
      Array.iteri
        (fun i st_id ->
          let outs = get_outgoing_from_index outgoing.(i) st_id in
          List.iter
            (fun t ->
              match t.action with
              | Clock -> ()
              | _ ->
                  let next =
                    List.mapi
                      (fun j s -> if i = j then t.to_state else s)
                      current
                  in
                  add_product_transition current next t.action t.guard)
            outs)
        current_arr;
      let message_choices =
        Array.mapi
          (fun i st_id ->
            let outs = get_outgoing_from_index outgoing.(i) st_id in
            let msg_transitions =
              outs
              |> List.filter_map (fun t ->
                     match t.action with
                     | Messages msgs -> Some (t.to_state, msgs, t.guard)
                     | _ -> None)
            in
            (st_id, MsgSet.empty, any_guard) :: msg_transitions)
          current_arr
        |> Array.to_list
      in
      message_choices
      |> cartesian_product
      |> List.iter (fun combo ->
             let selected =
               List.filter
                 (fun (_, msgs, _) -> not (MsgSet.is_empty msgs))
                 combo
             in
             if List.length selected >= 2 then
               let next = List.map (fun (st, _, _) -> st) combo in
               let combined =
                 List.fold_left
                   (fun acc (_, msgs, _) -> MsgSet.union acc msgs)
                   MsgSet.empty selected
               in
               let guard =
                 merge_guards (List.map (fun (_, _, guard) -> guard) selected)
               in
               add_product_transition current next (Messages combined) guard);
      let clock_choices =
        Array.mapi
          (fun i st_id ->
            let outs = get_outgoing_from_index outgoing.(i) st_id in
            (* A product clock round exists only when every component clocks. *)
            outs
            |> List.filter (fun t ->
                   match t.action with
                   | Clock -> true
                   | _ -> false)
            |> List.map (fun t -> (t.to_state, t.guard)))
          current_arr
        |> Array.to_list
      in
      if List.for_all (fun choices -> choices <> []) clock_choices then
        clock_choices
        |> cartesian_product
        |> List.iter (fun combo ->
               let next = List.map fst combo in
               let guard = merge_guards (List.map snd combo) in
               add_product_transition current next Clock guard))
  done;
  recompute_state_summaries prod;
  prod

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

let html_of_action = function
  | Epsilon -> "&#945; = &#949;"
  | Messages msgs -> "&#945; = " ^ html_of_msgset msgs
  | Clock -> "&#945; = {#}"
  | Progress ids -> "&#945; = " ^ html_of_string_set ids
  | FairBranch (id, branch) ->
      "&#945; = {" ^ escape_html id ^ (if branch then "_true" else "_false")
      ^ "}"

let html_of_guard g =
  let parts = ref [] in
  let add pred = parts := pred :: !parts in
  let add_msg pred msgs =
    if not (MsgSet.is_empty msgs) then add (pred (html_of_msgset msgs))
  in
  add_msg (fun s -> s ^ " &#8838; Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " &#8745; Imm(E) = &#8709;") g.forbid_now;
  if g.missing_now_groups <> [] then
    add
      ("&#8704;G &#8712; ["
       ^ (g.missing_now_groups |> List.map html_of_msgset |> String.concat "; ")
       ^ "]. &#172;(G &#8838; Imm(E))");
  if g.require_clock then add "# &#8712; Imm(E)";
  if g.forbid_clock then add "# &#8713; Imm(E)";
  add_msg (fun s -> s ^ " &#8745; F = &#8709;") g.future_disjoint;
  match List.rev !parts with
  | [] -> "true"
  | xs -> String.concat "<BR/>" xs

(* Render the v2 metadata directly in DOT for debugging the formal construction. *)
let print_automaton_dot auto out =
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
        Printf.sprintf "%d<BR/>H = %s<BR/>F = %s" id
          (html_of_msgset st.head)
          (html_of_msgset st.maybe_ready)
      in
      Printf.fprintf out "  %d [shape=%s,color=%s,label=<%s>];\n" id shape
        color label)
    ids;
  List.iter
    (fun t ->
      let label =
        if guard_is_any t.guard then html_of_action t.action
        else html_of_action t.action ^ "<BR/>" ^ html_of_guard t.guard
      in
      Printf.fprintf out "  %d -> %d [label=<%s>];\n" t.from_state
        t.to_state label)
    (List.rev auto.transitions);
  Printf.fprintf out "}\n"
