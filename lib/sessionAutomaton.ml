open Lang
open Except

type action_kind = 
  | ImmediateAction of Lang.message_specifier
  | BlockAction of Lang.message_specifier


type state = {
  id : int;
  mutable accepting : bool;
  mutable adversary : bool;
  mutable is_winning : bool;
  mutable is_fair : bool;
  mutable offers : (Lang.message_specifier list);
  mutable offers_in_future : (Lang.message_specifier list);
}

type label_kind =
  | Action of message_specifier
  | Delay
  | Questionable of message_specifier list
  | Negation of message_specifier list list
  | OptionDelay of message_specifier list list
  | Theta of session_type
  | Recurse of identifier
  | Terminal of int
  | Fair of identifier * int (* arm k of the fair choice with this identifier *)

module LabelKindOrd = struct
  type t = label_kind
  let compare = Stdlib.compare
end

module LabelSet = Set.Make(LabelKindOrd)

let union_labelsets (sets : LabelSet.t list) : LabelSet.t =
  List.fold_left (fun acc s -> LabelSet.union acc s) LabelSet.empty sets
module IntListSet = Set.Make(struct
    type t = int list
    let compare = Stdlib.compare
end)

module IntSet = Set.Make(Int)
type int_set = IntSet.t

let string_of_label_set (ls: LabelSet.t) : string = 
  let elements = LabelSet.elements ls in
  let str_list = List.map (function
    | Action m -> Printf.sprintf "Action(%s)" (Lang.string_of_msg_spec m)
    | Delay -> "#"
    | Questionable ms ->
      let ms_str = String.concat "|" (List.map Lang.string_of_msg_spec ms) in
      Printf.sprintf "UpNext([%s])" ms_str
    | Negation msg_groups ->
      let ms_str = String.concat "|" (List.map (fun group -> String.concat "&" (List.map Lang.string_of_msg_spec group)) msg_groups) in
      Printf.sprintf "Negation([%s])" ms_str
    | Theta st -> Printf.sprintf "Theta(%s)" (Lang.string_of_protocol st)
    | Terminal st -> Printf.sprintf "Terminal(%d)" st
    | Recurse var -> Printf.sprintf "$"^var
    | Fair (id, k) -> Printf.sprintf "%s_%d" id k
    | OptionDelay msg_groups ->
      let ms_str = String.concat "|" (List.map (fun group -> String.concat "&" (List.map Lang.string_of_msg_spec group)) msg_groups) in
      Printf.sprintf "(#Questionable[%s])" ms_str
  ) elements in
  "{" ^ (String.concat ", " str_list) ^ "}"


type transition = {
  from_state : int;
  to_state : int;
  label : LabelSet.t;
  is_epsilon : bool;
  is_theta : bool;
  is_recurse : bool;
  is_conditional : bool;
  mutable in_winning : bool;
}

type transition_outgoing_index = (int, transition list) Hashtbl.t

let build_outgoing_index (transitions: transition list) : transition_outgoing_index =
  let index = Hashtbl.create 16 in
  List.iter (fun t ->
    let existing =
      try Hashtbl.find index t.from_state
      with Not_found -> []
    in
    Hashtbl.replace index t.from_state (t :: existing)
  ) transitions;
  index

let get_outgoing_from_index (index: transition_outgoing_index) (state_id: int) : transition list =
  try Hashtbl.find index state_id
  with Not_found -> []

let print_string_of_transitions (transitions: transition list) : unit =
  List.iter (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else if t.is_theta then "θ"^(string_of_label_set t.label)
      else if t.is_recurse then "$"
      else
        string_of_label_set t.label
    in
    Printf.eprintf "  %d -> %d [label=\"%s\"];\n" t.from_state t.to_state label_str
  ) transitions

let string_of_transitions (transitions: transition list) : string =

  let init = "[\n"  in

  let lines = List.map (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else if t.is_theta then "θ"
      else if t.is_recurse then (string_of_label_set t.label)
      else
        string_of_label_set t.label
    in
    Printf.sprintf "  %d -> %d [label=\"%s\"];" t.from_state t.to_state label_str
  ) transitions in
  init ^ (String.concat "\n" lines) ^ "\n]"

let string_of_transition (t: transition) : string =
  let label_str = 
    if t.is_epsilon then "ε"
    else if t.is_theta then "θ"
    else
      string_of_label_set t.label
  in
  Printf.sprintf "  %d -> %d [label=\"%s\"];" t.from_state t.to_state label_str

type typeAutomaton = {
  mutable name : identifier;
  mutable states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  mutable start_state : int;
  mutable next_state_id : int;
}

type varContext = {
  var : identifier;
  state_id : int
}

(* --- Automaton Helper Functions --- *)


module TypeAutomaton = struct
  type t = typeAutomaton

  let create () : t =
    let start_state = 0 in
    let states = Hashtbl.create 10 in
    Hashtbl.add states start_state { id = start_state; accepting = false; adversary = false; is_winning = false; offers = []; offers_in_future = []; is_fair = false };
    {
      name = "";
      states = states;
      transitions = [];
      start_state = start_state;
      next_state_id = 1;
    }
  let change_name (id : identifier) (auto: t) : unit =
    auto.name <- id

  let new_state (auto: t) (accepting: bool) : int =
    let id = auto.next_state_id in
    auto.next_state_id <- id + 1;
    let state = { id; accepting; adversary = false; is_winning = false; offers = []; offers_in_future = []; is_fair = false } in
    Hashtbl.add auto.states id state;
    id
  
  let remove_state (auto: t) (state_id: int) : unit =
    Hashtbl.remove auto.states state_id;
    auto.transitions <- List.filter (fun t -> t.from_state <> state_id && t.to_state <> state_id) auto.transitions

 
  (* Transitions by the fields add_transition merges on; valid while the list is the same one. *)
  let edge_cache : (t * transition list * (int * int * bool * bool * bool, transition list) Hashtbl.t) option Domain.DLS.key =
    Domain.DLS.new_key (fun () -> None)

  let edge_key t = (t.from_state, t.to_state, t.is_epsilon, t.is_theta, t.is_conditional)

  let edges_by_key auto =
    match Domain.DLS.get edge_cache with
    | Some (owner, edges, tbl) when owner == auto && edges == auto.transitions -> tbl
    | _ ->
        let tbl = Hashtbl.create 64 in
        List.iter (fun t ->
          let key = edge_key t in
          Hashtbl.replace tbl key (t :: Option.value (Hashtbl.find_opt tbl key) ~default:[]))
          auto.transitions;
        tbl

  let add_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) (is_epsilon: bool) (is_theta : bool) (is_recurse: bool) (is_conditional: bool) : unit =
    let tbl = edges_by_key auto in
    let key = (from_s, to_s, is_epsilon, is_theta, is_conditional) in
    (match Hashtbl.find_opt tbl key with
     | Some (_ :: _ as matches) ->
         (* Merge the label into every matching transition, in place in the list. *)
         let merged = ref [] in
         auto.transitions <- List.map (fun t ->
           if List.memq t matches then (
             let t' = { t with label = LabelSet.union t.label label_set } in
             merged := t' :: !merged;
             t')
           else t) auto.transitions;
         Hashtbl.replace tbl key !merged
     | _ ->
         let trans = { from_state = from_s; to_state = to_s; label = label_set; is_epsilon; is_theta; is_recurse; is_conditional; in_winning = false } in
         auto.transitions <- trans :: auto.transitions;
         Hashtbl.replace tbl key [trans]);
    Domain.DLS.set edge_cache (Some (auto, auto.transitions, tbl))

  let remove_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s && LabelSet.equal t.label label_set)
    ) auto.transitions

  let remove_all_transitions (auto: t) (from_s: int) (to_s: int) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s)
    ) auto.transitions
  let add_rec_var_mapping (map : varContext list) (var: identifier) (state_id: int) : varContext list =
    { var; state_id } :: map
  
  let append_offers (auto: t) (state_id: int) (offers: Lang.message_specifier list) : unit =
    let state_info = Hashtbl.find auto.states state_id in
    state_info.offers <- state_info.offers @ offers
  
  let make_fair auto state_id = 
    let state_info = Hashtbl.find auto.states state_id in
    state_info.is_fair <- true
  let make_adversary auto state_id =
    let state_info = Hashtbl.find auto.states state_id in
    state_info.adversary <- true


  let reroute_transitions (auto: t) (old_state: int) (new_state: int) (map : varContext list) : unit =
    let is_recurse_state = List.exists (fun v ->
      (v.state_id = old_state)
    ) map in
    if is_recurse_state then ()
    else
    let new_transitions = List.map (fun t ->
      (* replace state in terminal label *)
      let new_label = LabelSet.elements t.label |> List.map (function
        | Terminal st when st = old_state -> Terminal new_state
        | other -> other
      ) |> List.fold_left (fun acc l -> LabelSet.add l acc) LabelSet.empty in
      let from_s = if t.from_state = old_state then new_state else t.from_state in
      let to_s = if t.to_state = old_state then new_state else t.to_state in
      { t with label = new_label; from_state = from_s; to_state = to_s }
    ) auto.transitions in
    auto.transitions <- new_transitions;
    if auto.start_state = old_state then
      auto.start_state <- new_state;
    let new_state_info = Hashtbl.find auto.states new_state in
    let old_state_info = Hashtbl.find auto.states old_state in
    new_state_info.offers <- new_state_info.offers @ old_state_info.offers;
    (* A recursion jump merges into the loop head; keep the head's fair and adversary flags. *)
    new_state_info.is_fair <- new_state_info.is_fair || old_state_info.is_fair;
    new_state_info.adversary <- new_state_info.adversary || old_state_info.adversary;
    Hashtbl.remove auto.states old_state
end

let print_automaton_dot (auto: TypeAutomaton.t) (out: out_channel) : unit =
  Printf.fprintf out "digraph TypeAutomaton {\n";
  
  Printf.fprintf out "  rankdir=LR;\n";
  Printf.fprintf out "  nodesep=0.5;\n";
  Printf.fprintf out "  ranksep=0.75;\n";

  Printf.fprintf out "  __start [shape=none, label=\"\", width=0, height=0];\n";
  Printf.fprintf out "  __start -> %d [color=grey];\n" auto.start_state;

  let sorted_ids = 
    Hashtbl.fold (fun id _ acc -> id :: acc) auto.states [] 
    |> List.sort compare 
  in

  List.iter (fun id ->
    let state = Hashtbl.find auto.states id in
    let shape = if state.accepting then "doublecircle" else if state.adversary then "square" else "circle" in
    
    let color = if state.is_winning then "darkgreen" else if state.is_fair then "orange" else "black" in
    
    let style = if state.is_winning then "filled, bold" else "bold" in
    let fillcolor = if state.is_winning then "palegreen" else "white" in 

    Printf.fprintf out "  %d [shape=%s, color=%s, style=\"%s\", fillcolor=\"%s\"];\n" 
      id shape color style fillcolor
  ) sorted_ids;
  
  let sorted_transitions = List.sort (fun t1 t2 -> 
    if t1.from_state = t2.from_state then compare t1.to_state t2.to_state
    else compare t1.from_state t2.from_state
  ) auto.transitions in

  List.iter (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else
        String.concat "," (LabelSet.elements t.label |> List.map (function
          | Action m -> Printf.sprintf "%s" (Lang.string_of_msg_spec m)
          | Delay -> "#"
          | Terminal st -> Printf.sprintf "$<%d>" st
          | Questionable ms ->
            let ms_str = String.concat "|" (List.map Lang.string_of_msg_spec ms) in
            Printf.sprintf " ? [%s]" ms_str
          | Negation msg_groups ->
            let ms_str = String.concat "|" (List.map (fun group -> String.concat "&" (List.map Lang.string_of_msg_spec group)) msg_groups) in
            Printf.sprintf " ¬[%s]" ms_str
          | Theta st -> Printf.sprintf "θ(%s)" (Lang.string_of_protocol st)
          | OptionDelay msg_groups ->
            let ms_str = String.concat "|" (List.map (fun group -> String.concat "&" (List.map Lang.string_of_msg_spec group)) msg_groups) in
            Printf.sprintf "(#¬[%s])" ms_str
          (* Explicitly handle Recurse if needed, or fallback *)
          | Recurse id -> Printf.sprintf "$%s" id
          | Fair (id, k) -> Printf.sprintf "%s_%d" id k
          (* | _-> string_of_label_set t.label *)
        ))
    in
    
    let constraint_attr = if t.to_state <= t.from_state then "constraint=false," else "" in
    
    let color_attr = if t.to_state = t.from_state then "color=blue, fontcolor=blue," else "" in

    Printf.fprintf out "  %d -> %d [%s%slabel=\"%s\"];\n" t.from_state t.to_state constraint_attr color_attr label_str
  ) sorted_transitions;

  Printf.fprintf out "}\n";
  flush out

let compare_msg_spec (m1: Lang.message_specifier) (m2: Lang.message_specifier) : int =
  let m1_str = Lang.string_of_msg_spec m1 in
  let m2_str = Lang.string_of_msg_spec m2 in
  String.compare m1_str m2_str
let collect_future_messages (auto: TypeAutomaton.t) : unit =
  let is_delay_label (label_set: LabelSet.t) : bool =
    LabelSet.exists (function
      | Delay -> true
      | OptionDelay _ -> true
      | _ -> false
    ) label_set in
  

  let rec dfs_collect (visited: IntSet.t) (current_state: int) : Lang.message_specifier list =
    if IntSet.mem current_state visited then []
    else
      let visited' = IntSet.add current_state visited in
      let current_state_info = Hashtbl.find auto.states current_state in
      let collected = ref current_state_info.offers in
      
      let outgoing = List.filter (fun t -> 
        t.from_state = current_state && t.to_state <> current_state
      ) auto.transitions in
      
      List.iter (fun t ->
        if not (is_delay_label t.label) then
          (* No delay, continue DFS *)
          let child_offers = dfs_collect visited' t.to_state in
          collected := !collected @ child_offers
      ) outgoing;
      
      !collected
  in
  
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun state_id state_info ->
      let current_offers_in_future = state_info.offers_in_future in
      let new_offers_in_future = dfs_collect IntSet.empty state_id in
      let unique_new_offers = List.sort_uniq compare_msg_spec new_offers_in_future in
      if not (List.sort_uniq compare_msg_spec current_offers_in_future = unique_new_offers) then
        begin
          state_info.offers_in_future <- unique_new_offers;
          changed := true
        end
    ) auto.states
  done

let infer_fair_choice (b1 : Lang.session_type) (b2 : Lang.session_type) : bool =
  let rec first_messages (st: Lang.session_type) : Lang.message_specifier list =
    match st with
    | Lang.StyAtom (Lang.AtomicAct (Lang.AtomBMsg m)) -> [m]
    | Lang.StyAtom (Lang.AtomicAct (Lang.AtomNBMsg m)) -> [m]
    | Lang.StyAtom (Lang.AtomConjunction acts) ->
      List.map (function
        | Lang.AtomBMsg m | Lang.AtomNBMsg m -> m
      ) acts
    | Lang.StySeq (s1, _) -> (first_messages s1)
    | Lang.StyChoice (s1, s2) | Lang.StyFairChoice (s1, s2) -> (first_messages s1) @ (first_messages s2)
    | Lang.StyOffer offerings | Lang.StyXOffer offerings | Lang.StyFairXOffer offerings
    | Lang.StyOfferMatch (offerings, _) ->
      List.flatten (List.map (fun o ->
        match o.Lang.trigger with
        | Lang.AtomicAct (Lang.AtomBMsg m) -> [m]
        | Lang.AtomicAct (Lang.AtomNBMsg m) -> [m]
        | Lang.AtomConjunction acts ->
          List.map (function
            | Lang.AtomBMsg m | Lang.AtomNBMsg m -> m
          ) acts
        | _ -> []
      ) offerings)
    | Lang.StyParallel (s1, s2) -> (first_messages s1) @ (first_messages s2)
    | Lang.StyFuture s -> first_messages s
    | Lang.StyAtom (Lang.AtomDelay _) -> []
    | Lang.StySkip -> []
    | Lang.StyRec (_, body) -> first_messages body
    | Lang.StyVar _ -> []
    | _ -> raise (TypeError [Text ("Unsupported session type for fair choice inference "^(string_of_protocol st))])
  in
  let msgs1 = first_messages b1 in
  let msgs2 = first_messages b2 in

  let ms1_ep = List.map (fun m -> m.endpoint) msgs1 in
  let ms2_ep = List.map (fun m -> m.endpoint) msgs2 in

  let set1 = List.fold_left (fun acc ep -> IntSet.add (Hashtbl.hash ep) acc) IntSet.empty ms1_ep in
  let set2 = List.fold_left (fun acc ep -> IntSet.add (Hashtbl.hash ep) acc) IntSet.empty ms2_ep in
  (not (IntSet.equal set1 set2)) || ((IntSet.cardinal set1 < 1) && (IntSet.cardinal set2 < 1))
