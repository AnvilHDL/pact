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
}

type label_kind =
  | Action of message_specifier
  | Delay
  | Negation of message_specifier list
  | Terminal of int

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
    | Negation ms ->
      let ms_str = String.concat "|" (List.map Lang.string_of_msg_spec ms) in
      Printf.sprintf "Negation([%s])" ms_str
    | Terminal st -> Printf.sprintf "Terminal(%d)" st
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
}

let print_string_of_transitions (transitions: transition list) : unit =
  List.iter (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else if t.is_theta then "θ"
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
  mutable states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  mutable start_state : int;
  mutable next_state_id : int;
  mutable rec_var_state_map : (identifier, int) Hashtbl.t;
}

(* --- Automaton Helper Functions --- *)


module TypeAutomaton = struct
  type t = typeAutomaton

  let create () : t =
    let start_state = 0 in
    let states = Hashtbl.create 10 in
    Hashtbl.add states start_state { id = start_state; accepting = false; adversary = false; is_winning = false; offers = []; is_fair = false };
    let rec_var_state_map = Hashtbl.create 10 in
    {
      states = states;
      transitions = [];
      start_state = start_state;
      next_state_id = 1;
      rec_var_state_map = rec_var_state_map;
    }

  let new_state (auto: t) (accepting: bool) : int =
    let id = auto.next_state_id in
    auto.next_state_id <- id + 1;
    let state = { id; accepting; adversary = false; is_winning = false; offers = []; is_fair = false } in
    Hashtbl.add auto.states id state;
    id
  
  let remove_state (auto: t) (state_id: int) : unit =
    Hashtbl.remove auto.states state_id;
    auto.transitions <- List.filter (fun t -> t.from_state <> state_id && t.to_state <> state_id) auto.transitions

 
  let add_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) (is_epsilon: bool) (is_theta : bool) (is_recurse: bool) (is_conditional: bool) : unit =
    let found = ref false in
    let new_transitions = List.map (fun t ->
      if t.from_state = from_s && t.to_state = to_s && t.is_epsilon = is_epsilon && t.is_theta = is_theta then
        (found := true; { t with label = LabelSet.union t.label label_set })
      else t
    ) auto.transitions in
    if !found then
      auto.transitions <- new_transitions
    else
      let trans = { from_state = from_s; to_state = to_s; label = label_set; is_epsilon; is_theta; is_recurse; is_conditional } in
      auto.transitions <- trans :: auto.transitions

  let remove_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s && LabelSet.equal t.label label_set)
    ) auto.transitions

  let remove_all_transitions (auto: t) (from_s: int) (to_s: int) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s)
    ) auto.transitions
  let add_rec_var_mapping (auto: t) (var: identifier) (state_id: int) : unit =
    Hashtbl.add auto.rec_var_state_map var state_id
  
  let append_offers (auto: t) (state_id: int) (offers: Lang.message_specifier list) : unit =
    let state_info = Hashtbl.find auto.states state_id in
    state_info.offers <- state_info.offers @ offers
  
  let make_fair auto state_id = 
    let state_info = Hashtbl.find auto.states state_id in
    state_info.is_fair <- true
  let make_adversary auto state_id =
    let state_info = Hashtbl.find auto.states state_id in
    state_info.adversary <- true


  let reroute_transitions (auto: t) (old_state: int) (new_state: int) : unit =
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
    new_state_info.offers <- old_state_info.offers;
    new_state_info.is_fair <- old_state_info.is_fair;
    new_state_info.adversary <- old_state_info.adversary;
    Hashtbl.remove auto.states old_state
end

let print_automaton_dot (auto: TypeAutomaton.t) (out: out_channel) : unit =
  Printf.fprintf out "digraph TypeAutomaton {\n";
  Hashtbl.iter (fun id state ->
    let shape = if state.accepting then "doublecircle" else if state.adversary then "square" else "circle" in
    let color = if state.is_winning then "green" else if state.is_fair then "yellow" else "red" in
    Printf.fprintf out "  %d [shape=%s, color=%s];\n" id shape color
  ) auto.states;
  
  List.iter (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else if t.is_theta then "θ"
      else if t.is_recurse then "$"
      else
        String.concat "," (LabelSet.elements t.label |> List.map (function
          | Action m -> Printf.sprintf "%s" (Lang.string_of_msg_spec m)
          | Delay -> "#"
          | Terminal st -> Printf.sprintf "$<%d>" st
          | Negation ms ->
            let ms_str = String.concat "|" (List.map Lang.string_of_msg_spec ms) in
            Printf.sprintf "¬[%s]" ms_str
        ))
    in
    Printf.fprintf out "  %d -> %d [label=\"%s\"];\n" t.from_state t.to_state label_str
  ) auto.transitions;

  Printf.fprintf out "}\n";
  flush out


let check_label_satisfiability (l1: label_kind) (l2: label_kind) : bool =
  (* placeholder for now *)
  l1 = l2

let label_equivalence (labels1: LabelSet.t) (labels2: LabelSet.t) : bool =
  let labels1_satisfied = LabelSet.for_all (fun l1 ->
    LabelSet.exists (fun l2 -> check_label_satisfiability l1 l2) labels2
  ) labels1 in
  
  if not labels1_satisfied then false
  else
    LabelSet.for_all (fun l2 ->
      LabelSet.exists (fun l1 -> check_label_satisfiability l2 l1) labels1
    ) labels2


let label_equivalence_one_way (labels1: LabelSet.t) (labels2: LabelSet.t) : bool =
  let label1_satisfied = LabelSet.for_all (fun l1 ->
    LabelSet.exists (fun l2 -> check_label_satisfiability l1 l2) labels2
  ) labels1 in
  label1_satisfied



let infer_fair_choice (b1 : Lang.session_type) (b2 : Lang.session_type) : bool =
  let rec first_messages (st: Lang.session_type) : Lang.message_specifier list =
    match st with
    | Lang.StyAtom (Lang.AtomicAct (Lang.AtomBMsg m)) -> [m]
    | Lang.StyAtom (Lang.AtomicAct (Lang.AtomNBMsg m)) -> [m]
    | Lang.StySeq (s1, _) -> (first_messages s1)
    | Lang.StyChoice (s1, s2) -> (first_messages s1) @ (first_messages s2)
    | Lang.StyOffer offerings | Lang.StyXOffer offerings ->
      List.flatten (List.map (fun o ->
        match o.Lang.trigger with
        | Lang.AtomicAct (Lang.AtomBMsg m) -> [m]
        | Lang.AtomicAct (Lang.AtomNBMsg m) -> [m]
        | _ -> []
      ) offerings)
    | Lang.StyParallel (s1, s2) -> (first_messages s1) @ (first_messages s2)
    | Lang.StyFuture s -> first_messages s
    | Lang.StyAtom (Lang.AtomDelay _) -> []
    | Lang.StyTrue -> []
    | _ -> raise (TypeError [Text ("Unsupported session type for fair choice inference "^(string_of_protocol st))])
  in
  let msgs1 = first_messages b1 in
  let msgs2 = first_messages b2 in

  let ms1_ep = List.map (fun m -> m.endpoint) msgs1 in
  let ms2_ep = List.map (fun m -> m.endpoint) msgs2 in

  (* check if both sets are NOT equal OR both are empty *)
  let set1 = List.fold_left (fun acc ep -> IntSet.add (Hashtbl.hash ep) acc) IntSet.empty ms1_ep in
  let set2 = List.fold_left (fun acc ep -> IntSet.add (Hashtbl.hash ep) acc) IntSet.empty ms2_ep in
  (not (IntSet.equal set1 set2)) || ((IntSet.cardinal set1 < 1) && (IntSet.cardinal set2 < 1))



let rec build_automaton (st: Lang.session_type) (default_span : Lang.code_span) : TypeAutomaton.t =
  let auto = TypeAutomaton.create () in
  
  (* Internal recursive builder *)
  let rec build (s_type: Lang.session_type) (current: int) : int =
    match s_type with
    | Lang.StyAtom at ->
      (
        match at with
        | Lang.AtomicAct (Lang.AtomBMsg m) -> 
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let pseudo_next = TypeAutomaton.new_state auto false in
            TypeAutomaton.add_transition auto current pseudo_next (LabelSet.singleton (Negation [m])) false false false true;
            TypeAutomaton.add_transition auto pseudo_next current (LabelSet.singleton (Delay)) false false false false;
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action m)) false false false false;
            TypeAutomaton.append_offers auto current [m];
            next_s
          )
        | Lang.AtomicAct (Lang.AtomNBMsg m) ->
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current current (LabelSet.singleton (Negation [m])) false false false true;
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action m)) false false false false;
            TypeAutomaton.append_offers auto current [m];
            next_s
          )
        | Lang.AtomDelay n ->
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let last = ref current in
            List.iter(fun _ ->
              let next = TypeAutomaton.new_state auto false in
              TypeAutomaton.add_transition auto !last next (LabelSet.singleton (Delay)) false false false false;
              last := next;
            ) (List.init n (fun x -> x));
            !last

          )
        | _ ->
          raise (TypeError [Text ("Unsupported atomic action for automaton construction "^(string_of_protocol s_type)); Except.codespan_local default_span])
      )
    | Lang.StySeq (st1, st2) ->
      (Hashtbl.find auto.states current).accepting <- false;
      let mid = build st1 current in
      (Hashtbl.find auto.states mid).accepting <- false;
      build st2 mid
    | Lang.StyChoice (st1, st2) -> (* Internal choice m1 + m2 *)
      (Hashtbl.find auto.states current).accepting <- false;
      let left_root = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current left_root LabelSet.empty false true false false;
      let right_root = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current right_root LabelSet.empty false true false false;
      let left_end = build st1 left_root in
      let right_end = build st2 right_root in
      (* TypeAutomaton.append_offers auto current ( (Hashtbl.find auto.states left_root).offers @ (Hashtbl.find auto.states right_root).offers ); *)
      (Hashtbl.find auto.states left_end).accepting <- false;
      (Hashtbl.find auto.states right_end).accepting <- false;
      let choice_state = TypeAutomaton.new_state auto true in
      TypeAutomaton.reroute_transitions auto left_end choice_state;
      TypeAutomaton.reroute_transitions auto right_end choice_state;
      choice_state
    | Lang.StyTrue -> 
      (* StyTrue represents successful termination - just return current state as accepting *)
      (Hashtbl.find auto.states current).accepting <- true;
      current
    | Lang.StyXOffer offerings ->
      (
        let is_wildcard_present = List.exists (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomDelay _ -> true
          | _ -> false
        ) offerings in

        let all_msg_branches = List.filter_map (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> Some o
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> Some o
          | _ -> None
        ) offerings in
        let all_blocking = List.for_all (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> true
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> false
          | _ -> false
        ) offerings in

        let end_state = TypeAutomaton.new_state auto true in

        (* add wildcard branch and the possible delay *)
        if is_wildcard_present then begin
          let wildcard_offer = List.find (fun (o : offering_session_type) -> 
            match o.Lang.trigger with
            | Lang.AtomDelay _ -> true
            | _ -> false
          ) offerings in
          let all_msg_specs = List.filter_map (fun b -> 
            match b.Lang.trigger with 
            | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
            | _ -> None
          ) all_msg_branches in
          let new_wildcard_state = TypeAutomaton.new_state auto true in
          TypeAutomaton.add_transition auto current new_wildcard_state (LabelSet.singleton (Negation all_msg_specs)) false false false true ;

          match wildcard_offer.Lang.continuation with
          | Some cont ->
            let branch_end = build cont new_wildcard_state in
            if (branch_end<>current) then TypeAutomaton.reroute_transitions auto branch_end end_state

          | None -> TypeAutomaton.reroute_transitions auto new_wildcard_state end_state
        end;

        List.iter (fun o_ms ->
          let m = match o_ms.Lang.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> m
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> m
            | _ -> failwith "Should not reach here"
          in
          let st = match o_ms.Lang.continuation with
            | Some cont -> StySeq (StyAtom (AtomicAct (AtomNBMsg m)), cont)
            | None -> StyAtom (o_ms.trigger)
          in
          let branch_end = build st current in
          TypeAutomaton.remove_all_transitions auto current current;
        if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in

            let new_state = TypeAutomaton.new_state auto false in

            TypeAutomaton.add_transition auto current new_state (LabelSet.singleton (Negation all_msg_specs)) false false false true;
            TypeAutomaton.add_transition auto new_state current (LabelSet.singleton (Delay)) false false false false
          );

        
          if not (branch_end=current) then TypeAutomaton.reroute_transitions auto branch_end end_state

        ) all_msg_branches;
          
        end_state
      )
    
    | Lang.StyOffer offerings ->
      (
        let is_wildcard_present = List.exists (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomDelay _ -> true
          | _ -> false
        ) offerings in

        let all_msg_branches = List.filter_map (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> Some o
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> Some o
          | _ -> None
        ) offerings in
        let all_blocking = List.for_all (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> true
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> false
          | _ -> false
        ) offerings in 
        
        let end_state = TypeAutomaton.new_state auto true in

        (* add wildcard branch and the possible delay *)
        if is_wildcard_present then begin
          let wildcard_offer = List.find (fun (o : offering_session_type) -> 
            match o.Lang.trigger with
            | Lang.AtomDelay _ -> true
            | _ -> false
          ) offerings in
          let all_msg_specs = List.filter_map (fun b -> 
            match b.Lang.trigger with 
            | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
            | _ -> None
          ) all_msg_branches in
          let new_wildcard_state = TypeAutomaton.new_state auto true in
          TypeAutomaton.add_transition auto current new_wildcard_state (LabelSet.singleton (Negation all_msg_specs)) false false false true;

          match wildcard_offer.Lang.continuation with
          | Some cont ->
            let branch_end = build cont new_wildcard_state in
            TypeAutomaton.reroute_transitions auto branch_end end_state
          | None -> TypeAutomaton.reroute_transitions auto new_wildcard_state end_state
        end else begin
        end;

        let branch_types = List.map (fun o_ms ->
          let trigger_msg = match o_ms.Lang.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> m
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> m
            | _ -> failwith "Should not reach here"
          in
          match o_ms.Lang.continuation with
          | Some cont -> StySeq (StyAtom (AtomicAct (AtomNBMsg trigger_msg)), cont)
          | None -> StyAtom (AtomicAct (AtomNBMsg trigger_msg))
        ) all_msg_branches in


        let rec generate_permutations btype acc  = function
          | [] -> acc
          | h::t ->
            let new_acc = acc @ (List.map (fun existing ->
              Lang.StyParallel (h, existing)
            ) acc) @ [h] in
            generate_permutations btype new_acc t
        in
          

        let all_permut_branch_type =  generate_permutations st [] branch_types in


        List.iter (fun btype ->
          let branch_end = build btype current in
          TypeAutomaton.remove_all_transitions auto current current;
          TypeAutomaton.reroute_transitions auto branch_end end_state;
        ) all_permut_branch_type;

          if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in
            let new_state = TypeAutomaton.new_state auto false in
            TypeAutomaton.add_transition auto current new_state (LabelSet.singleton (Negation all_msg_specs)) false false false true;
            TypeAutomaton.add_transition auto new_state current (LabelSet.singleton (Delay)) false false false false
          );
        end_state
      )
    | Lang.StyParallel (st1, st2) ->
      (Hashtbl.find auto.states current).accepting <- false;
      let final_state = create_synchronous_product auto st1 st2 current default_span in
      final_state
    | Lang.StyFuture st ->
      (Hashtbl.find auto.states current).accepting <- false;
      TypeAutomaton.make_fair auto current;
      TypeAutomaton.make_adversary auto current;
      let new_pseudo = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current new_pseudo LabelSet.empty false true false false;
      TypeAutomaton.add_transition auto new_pseudo current (LabelSet.singleton Delay) false false false false;
      let cont_state = TypeAutomaton.new_state auto true in
      TypeAutomaton.add_transition auto current cont_state LabelSet.empty false true false false;
      let end_state = build st cont_state in
      end_state
    | Lang.StyVar var ->
      (
        let rec_start = Hashtbl.find_opt auto.rec_var_state_map var in
        match rec_start with
        | Some s_id ->
          TypeAutomaton.reroute_transitions auto current s_id
          ;
          s_id
        | None ->
          raise (TypeError [Text ("Unbound recursion variable "^var ^ " in automaton construction"); Except.codespan_local default_span]);
      )
    | Lang.StyRec (var, body) ->
      (Hashtbl.find auto.states current).accepting <- false;
      let exists_mapping = Hashtbl.find_opt auto.rec_var_state_map var in
      (match exists_mapping with
      | Some _ ->
        raise (TypeError [Text ("Duplicate recursion variable "^var ^ " in automaton construction"); Except.codespan_local default_span]);
      | None -> ());
      TypeAutomaton.add_rec_var_mapping auto var current;
      let body_end = build body current in
      body_end
    | _ ->
      raise (TypeError [Text ("Unsupported session type for automaton construction "^(string_of_protocol s_type)); Except.codespan_local default_span])

  and create_synchronous_product (auto: TypeAutomaton.t) (st1: Lang.session_type) (st2: Lang.session_type) (current_start_node: int) (default_span : code_span) : int =
    (* Build sub-automata for st1 and st2 *)
    let auto1 = build_automaton st1 default_span in
    let auto2 = build_automaton st2 default_span in
    
    (* Build product automaton manually into `auto` *)
    let state_map : ((int * int), int) Hashtbl.t = Hashtbl.create 10 in
    
    let get_product_state (s1, s2) =
      try Hashtbl.find state_map (s1, s2)
      with Not_found ->
        let new_id = 
          if (s1 = auto1.start_state) && (s2 = auto2.start_state) then current_start_node
          else TypeAutomaton.new_state auto false
        in
        Hashtbl.add state_map (s1, s2) new_id;
        new_id
    in
    
    let find_accepting_state (sub_auto: TypeAutomaton.t) =
      Hashtbl.fold (fun id s acc -> 
        if s.accepting then 
          match acc with 
          | Some ac -> Some (id::ac) 
          | None -> Some [id] 
        else acc
      ) sub_auto.states None
      |> function
         | Some [id] -> id
         | None -> failwith "Sub-automaton for parallel has no accepting state"
         | _ -> failwith "Sub-automaton for parallel has multiple accepting states"
    in
    
    let end1 = find_accepting_state auto1 in
    TypeAutomaton.add_transition auto1 end1 end1 LabelSet.empty false false false false;

    let end2 = find_accepting_state auto2 in
    TypeAutomaton.add_transition auto2 end2 end2 LabelSet.empty false false false false;

    let final_prod_state = get_product_state (end1, end2) in  

    let module IntPairSet = Set.Make(struct
      type t = int * int
      let compare = Stdlib.compare
    end) in
    let worklist = ref [(auto1.start_state, auto2.start_state)] in
    let visited = ref IntPairSet.empty in 
    
    while !worklist <> [] do
      let (s1, s2) = List.hd !worklist in
      worklist := List.tl !worklist;
      
      if not (IntPairSet.mem (s1, s2) !visited) then (
        visited := IntPairSet.add (s1, s2) !visited;
        let ps = get_product_state (s1, s2) in
        
        let trans1 = List.filter (fun t -> t.from_state = s1) auto1.transitions in
        let trans2 = List.filter (fun t -> t.from_state = s2) auto2.transitions in

        let s1_accepting = s1 = end1 in
        let s2_accepting = s2 = end2 in

        if s1_accepting && s2_accepting then begin
          (Hashtbl.find auto.states ps).accepting <- true;
        end

        else if s1_accepting then begin
          (* take t2 transitions with s1 *)
          List.iter (fun t2 ->
            let next_ps = get_product_state (s1, t2.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t2.label t2.is_epsilon t2.is_theta t2.is_recurse t2.is_conditional;
            if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
              worklist := (s1, t2.to_state) :: !worklist
          ) trans2;
        end else if s2_accepting then begin
          (* take t1 transitions with s2 *)
          List.iter (fun t1 ->
            let next_ps = get_product_state (t1.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps t1.label t1.is_epsilon t1.is_theta t1.is_recurse t1.is_conditional;
            if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
              worklist := (t1.to_state, s2) :: !worklist
          ) trans1;
      
    end else begin
        
        (* Handle epsilon transitions - independent steps *)
        List.iter (fun t1 ->
          if t1.is_epsilon then (
            let next_ps = get_product_state (t1.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps t1.label t1.is_epsilon t1.is_theta t1.is_recurse t1.is_conditional;
            if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
              worklist := (t1.to_state, s2) :: !worklist
          );
          if t1.is_theta then (
            let next_ps = get_product_state (t1.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps t1.label t1.is_epsilon t1.is_theta t1.is_recurse t1.is_conditional;
            if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
              worklist := (t1.to_state, s2) :: !worklist
          );
        ) trans1;
        
        List.iter (fun t2 ->
          if t2.is_epsilon then (
            let next_ps = get_product_state (s1, t2.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t2.label t2.is_epsilon t2.is_theta t2.is_recurse t2.is_conditional;
            if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
              worklist := (s1, t2.to_state) :: !worklist
          );
          if t2.is_theta then (
            let next_ps = get_product_state (s1, t2.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t2.label t2.is_epsilon t2.is_theta t2.is_recurse t2.is_conditional;
            if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
              worklist := (s1, t2.to_state) :: !worklist
          );

        ) trans2;

        let is_delay t =
          LabelSet.exists (function Delay -> true | _ -> false) t.label in
        
          let cartesian_product list1 list2 =
            List.flatten (List.map (fun x ->
              List.map (fun y -> (x, y)) list2
            ) list1)
          in
        (* Handle synchronized transitions *)
       let delay_trans1 = List.filter is_delay trans1 in
       let delay_trans2 = List.filter is_delay trans2 in
        let trans1 = List.filter (fun t -> not t.is_epsilon && not t.is_theta && not (is_delay t) ) trans1 in

        let trans2 = List.filter (fun t -> not t.is_epsilon && not t.is_theta && not (is_delay t) ) trans2 in



        if List.length trans1 = 0 then (
          List.iter( fun t ->
            let next_ps = get_product_state (s1, t.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
            if not (IntPairSet.mem (s1, t.to_state) !visited) then 
              worklist := (s1, t.to_state) :: !worklist
          )trans2;
        )
        else if List.length trans2 = 0 then (
          List.iter(
            fun t ->
              let next_ps = get_product_state (t.to_state, s2) in
              TypeAutomaton.add_transition auto ps next_ps t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
              if not (IntPairSet.mem (t.to_state, s2) !visited) then 
                worklist := (t.to_state, s2) :: !worklist
          )trans1;
      )
        else (
        List.iter (fun t1 ->
          List.iter (fun t2 ->
            let label_set = LabelSet.union t1.label t2.label in
            TypeAutomaton.add_transition auto ps (get_product_state (t1.to_state, t2.to_state)) label_set false false false (t1.is_conditional && t2.is_conditional);
            if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then 
              worklist := (t1.to_state, t2.to_state) :: !worklist
          ) trans2
        ) trans1;



        let delay_combinations = cartesian_product delay_trans1 delay_trans2 in
        List.iter (fun (t1, t2) ->
          let label_set = LabelSet.union t1.label t2.label in
          TypeAutomaton.add_transition auto ps (get_product_state (t1.to_state, t2.to_state)) label_set false false false false;
          if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then 
            worklist := (t1.to_state, t2.to_state) :: !worklist
        ) delay_combinations;
        )
        
      end
      )
    done;
    Hashtbl.iter(fun (s1, s2) prod_s_id ->
      let state1 = Hashtbl.find auto1.states s1 in
      let state2 = Hashtbl.find auto2.states s2 in
      let prod_state = Hashtbl.find auto.states prod_s_id in
      prod_state.offers <- state1.offers @ state2.offers;
      prod_state.is_fair <- state1.is_fair || state2.is_fair;
      prod_state.adversary <- state1.adversary || state2.adversary;

    )state_map;
    final_prod_state
  in
  let final_state = build st auto.start_state in
  (Hashtbl.find auto.states final_state).accepting <- true;
  flush stderr;
  auto

let create_product (session_ids: (((session_type ast_node)*identifier) list))  (verbose : bool)  =
  let automata_ids = List.map (fun (st_node, intf_id) ->
    let auto = build_automaton st_node.d st_node.span in
    let final_state = Hashtbl.fold (fun id s acc -> if s.accepting then id :: acc else acc) auto.states [] in
    assert (List.length final_state = 1);
    TypeAutomaton.add_transition auto (List.hd final_state) auto.start_state LabelSet.empty false true false false;
    TypeAutomaton.add_transition auto (List.hd final_state) (List.hd final_state) (LabelSet.singleton Delay) false true false false;
    TypeAutomaton.make_fair auto (List.hd final_state);
    (auto, intf_id)
  ) session_ids in

  if verbose then (
    List.iter (fun (auto, intf_id) ->
      let out_chan = open_out (intf_id ^ "_automaton.dot") in
      print_automaton_dot auto out_chan;
      close_out out_chan;
      flush stderr;
    ) automata_ids
  );
  
  let state_map : (int list, int) Hashtbl.t = Hashtbl.create 10 in
  let prod_auto = TypeAutomaton.create () in

  let get_product_state (states: int list) : int =
    try Hashtbl.find state_map states
    with Not_found -> (
      let new_id = TypeAutomaton.new_state prod_auto false in
      Hashtbl.add state_map states new_id;
      new_id
    )
  in


  let worklist = ref [List.map(fun (auto, _) -> auto.start_state) automata_ids] in
  let visited = ref IntListSet.empty  in

  while !worklist <> [] do
    let current_states = List.hd !worklist in
    worklist := List.tl !worklist;

    if not (IntListSet.mem current_states !visited) then (
      
      visited := IntListSet.add current_states !visited;
      let prod_state_id = get_product_state current_states in

      let is_all_start_state = List.for_all2 (fun st_id (auto, _) ->
        st_id = auto.start_state
      ) current_states automata_ids in
      if is_all_start_state then TypeAutomaton.reroute_transitions prod_auto 0 prod_state_id;
      let is_accepting_array = List.map2 (fun st_id (auto, _) ->
        let state = Hashtbl.find auto.states st_id in
        state.accepting
      ) current_states automata_ids in

      if List.for_all (fun x -> x) is_accepting_array then (
        (Hashtbl.find prod_auto.states prod_state_id).accepting <- true
      ) else (
        
        let transitions_list = List.mapi (fun idx (auto, _) ->
          let state_id = List.nth current_states idx in
          List.filter (fun t -> t.from_state = state_id) auto.transitions
        ) automata_ids in
        
        let is_delay t = LabelSet.exists (function Delay -> true | _ -> false) t.label in

        let epsilon_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_epsilon || t.is_theta || t.is_recurse then Some t else None
          ) transition_set
        ) transitions_list in

        let theta_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if t.is_theta then Some t else None
          ) transition_set
        ) epsilon_transitions in

        if List.for_all (fun ts -> ts = []) theta_transitions then (
        let sync_transitions = List.map (fun transition_set ->
          List.filter_map (fun t ->
            if not t.is_epsilon && not t.is_theta && not t.is_recurse && not (is_delay t) 
            then Some t 
            else None
          ) transition_set
        ) transitions_list in

        let delay_transitions = List.map (fun transition_set ->
          List.filter_map (fun t -> if is_delay t then Some t else None) transition_set
        ) transitions_list in


        List.iteri (fun i ep_set -> 
          List.iter (fun t ->
            let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
            let next_prod_state = get_product_state next_states in
            TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
            if not (IntListSet.mem next_states !visited) then 
               worklist := next_states :: !worklist
          ) ep_set
        ) epsilon_transitions;


        let rec cartesian_product lists =
            match lists with
            | [] -> [[]]
            | h :: t ->
                let rest = cartesian_product t in
                if h = [] then
                    (* If this list is empty, use None for this position *)
                    List.map (fun r -> None :: r) rest
                else
                    List.flatten (List.map (fun x -> List.map (fun r -> (Some x) :: r) rest) h)
        in

        let rec cartesian_product2 lists =
            match lists with
            | [] -> [[]]
            | h :: t ->
                let rest = cartesian_product2 t in
                List.flatten (List.map (fun x -> List.map (fun r -> x :: r) rest) h)
        in


        
        let all_transition_combinations = cartesian_product sync_transitions in


        
        List.iter (fun transition_set ->

          let actual_transitions = List.filter_map (fun opt -> opt) transition_set in
          

          if actual_transitions <> [] then (

            let combined_actions = List.flatten (List.map (fun t -> 
              List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label)
            ) actual_transitions) in

            let combined_actions = if combined_actions = [] then union_labelsets (List.map (fun t -> t.label) actual_transitions)
            else List.fold_left (fun acc a -> LabelSet.add (Action a) acc) LabelSet.empty combined_actions in
          


          let is_compatible =  (
            List.mapi( fun i t_opt ->
                match t_opt with
                | None -> true (* Empty slot is always compatible *)
                | Some t ->
                (
                      let t_actions = List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label) in
                      let actions = List.flatten ( List.mapi (fun idx t_opt ->
                        if idx = i then [] else
                          match t_opt with
                          | None -> []
                          | Some t -> List.filter_map (function Action m -> Some m | _ -> None) (LabelSet.elements t.label)
                      ) transition_set) in

                      (* let actions_of_this_state = List.mapi (fun indx s -> if i = indx then [] else (let auto, _= List.nth automata_ids indx in let st = Hashtbl.find auto.states s in st.offers) ) current_states in

                      let actions_of_this_state = List.flatten actions_of_this_state in *)

                      let t_not_acts = List.filter_map (function Negation ms -> Some ms | _ -> None) (LabelSet.elements t.label) in
                      let t_not_acts_flat = List.flatten t_not_acts in
                      List.for_all( fun ua ->
                        List.mem ua actions
                      )t_actions &&
                      List.for_all( fun tna ->
                        not (List.mem tna actions)
                      )t_not_acts_flat
                )
            )transition_set
          ) in 

          let is_compatible = List.for_all (fun x -> x) is_compatible in

          (* Printf.eprintf "[%s] Transition Combination: %s\n" (string_of_bool is_compatible) (String.concat "; " (List.mapi (fun i t_opt ->
            match t_opt with
            | None -> Printf.sprintf "Auto %d: None" i
            | Some t -> "Auto "^(string_of_int i)^": "^(string_of_transition t)
          ) transition_set)); *)

            if is_compatible then (
              let next_states = List.mapi (fun idx t_opt ->
                let current_state = List.nth current_states idx in
                match t_opt with
                | None -> current_state
                | Some t -> t.to_state
              ) transition_set in
              let next_prod_state = get_product_state next_states in
              
              
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state combined_actions false false false (List.for_all (fun t_opt -> match t_opt with None -> true | Some t -> t.is_conditional) transition_set);
              
              if not (IntListSet.mem next_states !visited) then 
                worklist := next_states :: !worklist
            )
          )
        ) all_transition_combinations;

        let all_delay_combinations = cartesian_product2 delay_transitions in
        List.iter( fun transition_set -> (
            if List.length transition_set < 2 then raise (Failure "Unexpected: less than 2 transitions in combination")
            else(
                let next_states = List.mapi ( fun idx _->
                  let t = List.nth transition_set idx in
                  t.to_state
                ) current_states in

                let next_prod_state = get_product_state next_states in
                TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state (LabelSet.singleton Delay) false false false false;
                if not (IntListSet.mem next_states !visited) then 
                  worklist := next_states :: !worklist
            )
          )
        ) all_delay_combinations;
        )
        else
        (
          List.iteri (fun i ep_set -> 
            List.iter (fun t ->
              let next_states = List.mapi (fun idx s -> if idx = i then t.to_state else s) current_states in
              let next_prod_state = get_product_state next_states in
              TypeAutomaton.add_transition prod_auto prod_state_id next_prod_state t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
              if not (IntListSet.mem next_states !visited) then 
                 worklist := next_states :: !worklist
            ) ep_set
          ) theta_transitions;
        )   

      )
    )
  done;

  (* Assign offers/fair/adversary flags as before... *)
  Hashtbl.iter (fun states prod_state_id ->
    let offers = List.flatten (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      let state = Hashtbl.find auto.states st_id in
      state.offers
    ) states) in
    let is_fair = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      (Hashtbl.find auto.states st_id).is_fair
    ) states) in
    let is_adversary = List.exists (fun x -> x) (List.mapi (fun idx st_id ->
      let auto, _ = List.nth automata_ids idx in
      (Hashtbl.find auto.states st_id).adversary
    ) states) in

    let prod_state = Hashtbl.find prod_auto.states prod_state_id in
    prod_state.offers <- offers;
    prod_state.is_fair <- is_fair;
    prod_state.adversary <- is_adversary
  ) state_map;

  (* Debug output *)
  if verbose then Hashtbl.iter (fun states prod_state_id ->
      Printf.eprintf "Product state %d corresponds to states %s\n" prod_state_id (String.concat "," (List.map string_of_int states))
  ) state_map;

  prod_auto

let label_adversary_state (auto : TypeAutomaton.t) (state_id : int) =
  let state = Hashtbl.find auto.states state_id in
  let check_if_adversary_state =
    List.exists (fun t ->
      t.is_theta
    ) (List.filter (fun t -> t.from_state = state_id) auto.transitions)
  in
  if check_if_adversary_state then
    state.adversary <- true

let can_reach_self (graph_transitions : transition list) (start_node : int) (target_node : int) : bool =
  let queue = Queue.create () in
  Queue.add start_node queue;
  let visited = Hashtbl.create 16 in
  Hashtbl.add visited start_node ();
  
  let found = ref false in
  
  while not !found && not (Queue.is_empty queue) do
    let u = Queue.take queue in
    if u = target_node then 
      found := true
    else
      let neighbors = List.filter_map (fun t -> 
        if t.from_state = u then Some t.to_state else None
      ) graph_transitions in
      
      List.iter (fun v ->
        if not (Hashtbl.mem visited v) then (
          Hashtbl.add visited v ();
          Queue.add v queue
        )
      ) neighbors
  done;
  !found
let play_game (prod_auto : TypeAutomaton.t) : (bool * string) =
  
  let is_winning : (int, bool) Hashtbl.t = Hashtbl.create 10 in
  

  Hashtbl.iter (fun state_id state ->
    if state.accepting then
      Hashtbl.add is_winning state_id true
  ) prod_auto.states;
  

  let changed = ref true in
  while !changed do
    changed := false;
    
    Hashtbl.iter (fun state_id state ->
      (* Skip if already marked as winning *)
      if not (Hashtbl.mem is_winning state_id) then (
        (* Get all outgoing transitions from this state *)
        let outgoing = List.filter (fun t -> 
          t.from_state = state_id
        ) prod_auto.transitions in
        
        if outgoing = [] then
          ()
        else
          (* look for transitions leading to self starting with this transition *)

          let should_mark_winning = 
            if state.is_fair then
              (
                      List.for_all (fun t ->
                        if t.from_state = t.to_state then true
                        else (
                          let has_path_to_self = can_reach_self prod_auto.transitions t.to_state state.id in

                        (Hashtbl.mem is_winning t.to_state &&
                        Hashtbl.find is_winning t.to_state) || has_path_to_self

                        )
                      ) outgoing
                  )
            
                  else if state.adversary then
                  (
                        List.for_all (fun t ->
                          if t.from_state = t.to_state then
                            true
                          else
                          Hashtbl.mem is_winning t.to_state &&
                          Hashtbl.find is_winning t.to_state
                        )outgoing
                  )
                  else
                    (
                    (* Player state: AT LEAST ONE child must be winning *)
                    List.exists (fun t ->
                      if t.from_state = t.to_state then
                        false
                      else
                      Hashtbl.mem is_winning t.to_state &&
                      Hashtbl.find is_winning t.to_state
                    ) outgoing
                    )
          in
          
          if should_mark_winning then (
            Hashtbl.add is_winning state_id true;
            changed := true
          )
      )
    ) prod_auto.states
  done;
  

Hashtbl.iter (fun state_id is_win ->
  if is_win then
    let state = Hashtbl.find prod_auto.states state_id in
    state.is_winning <- true;
) is_winning;

Hashtbl.iter (fun state_id state ->
  if not (Hashtbl.mem is_winning state_id) then
    state.is_winning <- false;

) prod_auto.states;
  let start_is_winning = 
    Hashtbl.mem is_winning prod_auto.start_state &&
    Hashtbl.find is_winning prod_auto.start_state
  in
  
  if start_is_winning then
    (true, "Compatibility verified: winning strategy exists from start state")
  else
    (false, Printf.sprintf "Compatibility failed: start state %d is not winning" prod_auto.start_state)



let check_compatibility_multiparty 
    (session_ids : ((session_type ast_node) * identifier) list)
    (pool_id : identifier)
    (verbose : bool) 
    : (bool * string) =


    let prod_auto = create_product session_ids verbose in

    Printf.eprintf "Product Construction Completed. Total States: %d\n" (Hashtbl.length prod_auto.states);

    Hashtbl.iter (fun state_id _ ->
        label_adversary_state prod_auto state_id
    ) prod_auto.states;
    
    let result, err = play_game prod_auto in
    Printf.eprintf "Game Analysis Completed.\n";

    let out = Stdlib.open_out ("prod_auto_"^pool_id^".dot") in
    print_automaton_dot prod_auto out;
    Stdlib.close_out out;
    flush stderr;
    (result, err)
