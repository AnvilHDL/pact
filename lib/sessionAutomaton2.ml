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

let powerset s = 
  let rec aux acc = function
    | [] -> [acc]
    | x :: xs ->
        let with_x = aux (MsgSet.add x acc) xs in
        let without_x = aux acc xs in
        with_x @ without_x
  in
  aux MsgSet.empty (MsgSet.elements s)

let msgset_to_list set = MsgSet.elements set

let string_of_msgset set =
  set
  |> MsgSet.elements
  |> List.map string_of_msg_spec
  |> String.concat ","

(* Observable labels used by the closed compatibility game. *)

type observation =
  | Message of message_specifier
  | Progress of identifier
  | FairBranch of identifier * int (*Will use it later, when type spec is allowed*)


(* msgs > Prog > fairbranch *)
module OrderedObs = struct
  type t = observation
  let compare a b =
    match (a, b) with
    | Message m1, Message m2 -> String.compare (string_of_msg_spec m1) (string_of_msg_spec m2)
    | Progress id1, Progress id2 -> String.compare id1 id2
    | FairBranch (id1, b1), FairBranch (id2, b2) ->
        let c = String.compare id1 id2 in
        if c <> 0 then c else Int.compare b1 b2
    | Message _, _ -> -1
    | _, Message _ -> 1
    | Progress _, _ -> -1
    | _, Progress _ -> 1

  let string_of_observation = function
    | Message m -> string_of_msg_spec m
    | Progress id -> "$" ^ id
    | FairBranch (id, branch) -> id ^ (if branch = 0 then "_false" else "_true")
end

module ObservationSet = Set.Make (OrderedObs)

let string_of_observation_set set =
  if ObservationSet.is_empty set then "ε"
  else
      "{"^
      (
      set
      |> ObservationSet.elements
      |> List.map OrderedObs.string_of_observation
      |> String.concat ","
      )^"}"

type action = 
 | Observations of ObservationSet.t
 | Clock

let epsilon = Observations ObservationSet.empty
let message_action msg = Observations (ObservationSet.singleton (Message msg))
let progress_action id = Observations (ObservationSet.singleton (Progress id))

let message_actions msgset =
  Observations (ObservationSet.union 
    (msgset |> MsgSet.elements |> List.map (fun msg -> Message msg) |> ObservationSet.of_list)
    ObservationSet.empty)
    

 let string_of_action = function
  | Observations obs_set -> string_of_observation_set obs_set
  | Clock -> "#"

(* Symbolic one-step environment constraints for a transition. *)
type guard = {
  require_now : MsgSet.t; (* require_now ⊆ Imm(E) *)
  forbid_now : MsgSet.t; (* forbid_now ∩ Imm(E) = ∅ *)
  require_clock : bool; (* require_clock ⇒ # ∈ Imm(E) *)
  forbid_clock : bool; (* forbid_clock ⇒ # ∉ Imm(E) *)
  future_disjoint : MsgSet.t; (* future_disjoint ∩ F = ∅ , *)
  future_members : MsgSet.t; (* future_members ⊆ F (SyncEdges' OfferFut equality per powerset slice) *)
}

let any_guard = {
  require_now = MsgSet.empty;
  forbid_now = MsgSet.empty;
  require_clock = false;
  forbid_clock = false;
  future_disjoint = MsgSet.empty;
  future_members = MsgSet.empty;
}

let guard_is_any g =
  MsgSet.is_empty g.require_now
  && MsgSet.is_empty g.forbid_now
  && not g.require_clock
  && not g.forbid_clock
  && MsgSet.is_empty g.future_disjoint
  && MsgSet.is_empty g.future_members

(* Local view of what is immediate now and possible later in this cycle. *)
type env = {
  imm : MsgSet.t;
  future : MsgSet.t;
  clock : bool;
}

let empty_env = { imm = MsgSet.empty; future = MsgSet.empty; clock = false }

(* A transition is enabled exactly when its symbolic guard matches the local view. *)

let project_msgset_to_universe universe msgs =
  MsgSet.inter msgs universe
let guard_satisfied env g universe =
  if guard_is_any g then true
  else
    let projected_require_now = project_msgset_to_universe universe g.require_now in
    let projected_forbid_now = project_msgset_to_universe universe g.forbid_now in
    let projected_future_disjoint = project_msgset_to_universe universe g.future_disjoint in
    let projected_future_members = project_msgset_to_universe universe g.future_members in


    let require_now_ok = MsgSet.subset projected_require_now env.imm in
    let forbid_now_ok = (MsgSet.is_empty (MsgSet.inter projected_forbid_now env.imm)) in
    let require_clock_ok = not g.require_clock || env.clock in
    let forbid_clock_ok = true in  (*this guard requires env to forbid clock and its always satisfiable*)
    let future_disjoint_ok = MsgSet.is_empty (MsgSet.inter projected_future_disjoint env.future) in
    let future_members_ok = MsgSet.subset projected_future_members env.future in
    require_now_ok
    && forbid_now_ok
    && require_clock_ok
    && forbid_clock_ok
    && future_disjoint_ok
    && future_members_ok


let string_of_guard g =
  let parts = ref [] in
  let fmt_msgset msgs = "{" ^ string_of_msgset msgs ^ "}" in
  (* " | " between groups (vs "," within a group) so {m1,m2} can't be misread as {m1} | {m2}. *)
  let add pred =
    parts := pred :: !parts
  in
  let add_msg pred msgs =
    if not (MsgSet.is_empty msgs) then
      add (pred (fmt_msgset msgs))
  in
  add_msg (fun s -> s ^ "subset Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " cap Imm(E) = empty") g.forbid_now;
  if g.require_clock then add "# in Imm(E)";
  if g.forbid_clock then add "# notin Imm(E)";
  add_msg (fun s -> s ^ " cap F = empty") g.future_disjoint;
  add_msg (fun s -> s ^ " subset F") g.future_members;
  match List.rev !parts with
  | [] -> "true"
  | xs -> String.concat " && " xs

type product_component = {
  pc_name : identifier;
  pc_state : int;
  pc_residual : string option;
}

(* head/maybe_ready cache Head/MaybeReady; head_clock is whether # is in this state's Head. *)
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
  boundary_guard : guard; (* pending boundary part of the guard; `guard` keeps the FULL merged guard for closed game/dead-end analysis *)
  internal_action : action; (* `action` projected onto internal_messages; debug only, epsilon if no internal component *)
  offers : MsgSet.t;
  mutable maybe_offers : MsgSet.t;
  mutable in_winning : bool;
  transition_debug_info : string option;
}

type transition_outgoing_index = (int, transition list) Hashtbl.t

type typeAutomaton = {
  mutable name : identifier;
  mutable states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  mutable start_state : int;
  mutable next_state_id : int;
  mutable total_message_set : MsgSet.t;
}

let action_messages = function
  | Observations obs_set ->
      obs_set
      |> ObservationSet.elements
      |> List.filter_map (function
           | Message msg -> Some msg
           | _ -> None)
      |> msgset_of_list
  | _ -> MsgSet.empty


let progress_ids_of_action = function
  | Observations obs_set ->
      obs_set
      |> ObservationSet.elements
      |> List.filter_map (function
           | Progress id -> Some id
           | _ -> None)
      |> StringSet.of_list
  | _ -> StringSet.empty
      

let transition_is_clock t =
  match t.action with
  | Clock -> true
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

  let create total_msgs =
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
      total_message_set = total_msgs;
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
        if not (transition_is_clock t) then (
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
      t.maybe_offers <- MsgSet.diff to_st.maybe_ready t.offers)
    auto.transitions

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
        require_clock = acc.require_clock && guard.require_clock;
        forbid_clock = acc.forbid_clock || guard.forbid_clock;
        future_disjoint = MsgSet.union acc.future_disjoint guard.future_disjoint;
        future_members = MsgSet.union acc.future_members guard.future_members;
      })
    any_guard guards

let add_progress_transition auto from_state to_state ids =
  let action = Observations (ObservationSet.of_list (List.map (fun id -> Progress id) ids)) in
  TypeAutomaton.add_transition auto from_state to_state action
    any_guard  MsgSet.empty

(* Unified synchronous product (internal parallel/closed/open): boundary_messages ride the open boundary (empty for closed/internal); internal_messages must be paired by ≥2 components; use_env computes environments from partner Head/MaybeReady, else plain cartesian product. *)
let unified_product ?progress_ids ?(verbose = false) ?dead_ends automata
    ~boundary_messages ~use_env =
    let _ = progress_ids in
    let _ = dead_ends in
    let _ = verbose in
    let _ = use_env in
    let _ = automata in
    let _ = boundary_messages in
    let open Except in
    raise (Except.UnimplementedError ([Text "unified_product is not yet implemented"]))



let closed_product ?progress_ids ?(verbose = false) ?dead_ends automata
    sync_messages =
  (* Closed product: all messages except those explicitly in sync_messages are boundary. *)
  let all_messages =
    Array.fold_left
      (fun acc auto -> MsgSet.union acc auto.total_message_set)
      MsgSet.empty automata
  in
  let boundary_messages = MsgSet.diff all_messages sync_messages in
  unified_product ?progress_ids ~verbose ?dead_ends automata ~boundary_messages
    ~use_env:true

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
      TypeAutomaton.add_transition auto state_id state_id epsilon any_guard
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
        | act  when t.from_state = t.to_state && guard_is_any t.guard && act = epsilon ->
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

let without_projected_guard_debug text =
  let rec loop dropping acc = function
    | [] -> List.rev acc
    | line :: rest ->
        let trimmed = String.trim line in
        if trimmed = "projected guard checks:" then
          loop true acc rest
        else if dropping && trimmed = "------------------------------------------------------------" then
          loop false (line :: acc) rest
        else if dropping then
          loop true acc rest
        else
          loop false (line :: acc) rest
  in
  text |> String.split_on_char '\n' |> loop false [] |> String.concat "\n"


let html_of_guard g =
  let parts = ref [] in
  let add pred = parts := pred :: !parts in
  let add_msg pred msgs =
    if not (MsgSet.is_empty msgs) then add (pred (html_of_msgset msgs))
  in
  (* " | " between groups, distinct from the ", " inside a group, so a single
     multi-message group can't be misread as several single-message groups. *)
  add_msg (fun s -> s ^ " = Imm(E)") g.require_now;
  add_msg (fun s -> s ^ " ∩ Imm(E) = ∅") g.forbid_now;
  if g.require_clock then add "# ∈ Imm(E)";
  if g.forbid_clock then add "# ∉ Imm(E)";
  add_msg (fun s -> s ^ " ∩ F = ∅") g.future_disjoint;
  add_msg (fun s -> s ^ " ⊆ F") g.future_members;
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
            string_of_action t.action
          else
            string_of_action t.action ^ "<BR/>satisfied: " ^ html_of_guard t.guard
        in
        (* internal_action is `action` projected onto internal_messages; only shown when it differs from action. *)
        let internal_label =
          if (not show_guards) || t.internal_action = t.action then ""
          else "<BR/>internal: " ^ string_of_action t.internal_action
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
        (* O and MO are independent fields; show each whenever non-empty rather than suppressing one based on the other. *)
        let offers =
          (if MsgSet.is_empty t.offers then ""
           else "<BR/>O = " ^ html_of_msgset t.offers)
          ^ (if MsgSet.is_empty t.maybe_offers then ""
             else "<BR/>MO = " ^ html_of_msgset t.maybe_offers)
        in
        let debug =
          match show_transition_debug, t.transition_debug_info with
          | false, _ -> ""
          | true, None -> ""
          | true, Some info ->
              let info = without_projected_guard_debug info in
              if info = "" then "" else "<BR/>" ^ html_of_text_block info
        in
        base ^ internal_label ^ pending ^ offers ^ boundary ^ debug
      in
      Printf.fprintf out "  %d -> %d [label=<%s>];\n" t.from_state
        t.to_state label)
    (List.rev auto.transitions);
  Printf.fprintf out "}\n"