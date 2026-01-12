open Lang
open Except



type action_kind = 
  | ImmediateAction of Lang.message_specifier
  | BlockAction of Lang.message_specifier

type delay_kind = 
  | CycleDelay of int
  | MessageDelay of Lang.message_specifier
  | OptionDelay of Lang.message_specifier list



type state = {
  id : int;
  mutable accepting : bool;
}

type label_kind =
  | Action of message_specifier
  | Delay of delay_kind
  | Negation of message_specifier list
  | Terminal of int

module LabelKindOrd = struct
  type t = label_kind
  let compare = Stdlib.compare
end

module LabelSet = Set.Make(LabelKindOrd)

module IntSet = Set.Make(Int)
type int_set = IntSet.t

type transition = {
  from_state : int;
  to_state : int;
  label : LabelSet.t;
  is_epsilon : bool;
  is_theta : bool;
}

type typeAutomaton = {
  states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  start_state : int;
  mutable next_state_id : int;
  mutable rec_var_state_map : (identifier, int) Hashtbl.t;
}

(* --- Automaton Helper Functions --- *)


module TypeAutomaton = struct
  type t = typeAutomaton

  let create () : t =
    let start_state = 0 in
    let states = Hashtbl.create 10 in
    Hashtbl.add states start_state { id = start_state; accepting = false };
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
    let state = { id; accepting } in
    Hashtbl.add auto.states id state;
    id
  
  let remove_state (auto: t) (state_id: int) : unit =
    Hashtbl.remove auto.states state_id;
    auto.transitions <- List.filter (fun t -> t.from_state <> state_id && t.to_state <> state_id) auto.transitions

 
  let add_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) (is_epsilon: bool) (is_theta: bool) : unit =
    let found = ref false in
    let new_transitions = List.map (fun t ->
      if t.from_state = from_s && t.to_state = to_s && t.is_epsilon = is_epsilon && t.is_theta = is_theta then
        (found := true; { t with label = LabelSet.union t.label label_set })
      else t
    ) auto.transitions in
    
    if !found then
      auto.transitions <- new_transitions
    else
      let trans = { from_state = from_s; to_state = to_s; label = label_set; is_epsilon; is_theta } in
      auto.transitions <- trans :: auto.transitions
      
  let remove_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s && LabelSet.equal t.label label_set)
    ) auto.transitions
    
  let add_rec_var_mapping (auto: t) (var: identifier) (state_id: int) : unit =
    Hashtbl.add auto.rec_var_state_map var state_id


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
    Hashtbl.remove auto.states old_state
end

let print_automaton_dot (auto: TypeAutomaton.t) (out: out_channel) : unit =
  Printf.fprintf out "digraph TypeAutomaton {\n";
  Hashtbl.iter (fun id state ->
    let shape = if state.accepting then "doublecircle" else "circle" in
    Printf.fprintf out "  %d [shape=%s];\n" id shape
  ) auto.states;
  
  List.iter (fun t ->
    let label_str = 
      if t.is_epsilon then "ε"
      else if t.is_theta then "θ"
      else
        String.concat "," (LabelSet.elements t.label |> List.map (function
          | Action m -> Printf.sprintf "%s" (Lang.string_of_msg_spec m)
          | Delay(CycleDelay n) -> Printf.sprintf "#%d" n
          | Delay(MessageDelay m) -> Printf.sprintf "#m:%s" (Lang.string_of_msg_spec m)
          | Terminal st -> Printf.sprintf "$<%d>" st
          | Delay(OptionDelay ms) -> 
            let ms_str = String.concat "|" (List.map Lang.string_of_msg_spec ms) in
            Printf.sprintf "#offer:[%s]" ms_str
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
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action m)) false false;
            TypeAutomaton.add_transition auto current current (LabelSet.singleton (Delay(MessageDelay m))) false false;
            next_s
          )
        | Lang.AtomicAct (Lang.AtomNBMsg m) ->
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action m)) false false;
            next_s
          )
        | Lang.AtomDelay n ->
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Delay (CycleDelay n))) false false;
            next_s
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
      TypeAutomaton.add_transition auto current left_root LabelSet.empty false true;
      let right_root = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current right_root LabelSet.empty false true;
      let left_end = build st1 left_root in
      let right_end = build st2 right_root in
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
        let all_non_blocking = List.for_all (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> false
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> true
          | _ -> false
        ) offerings in
        if not all_blocking && not all_non_blocking then 
          raise(TypeError [Text ("Mixed blocking and non-blocking offerings in external choice"); Except.codespan_local default_span]);  

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
          TypeAutomaton.add_transition auto current new_wildcard_state (LabelSet.singleton (Negation all_msg_specs)) false false;

          match wildcard_offer.Lang.continuation with
          | Some cont ->
            let branch_end = build cont new_wildcard_state in
            TypeAutomaton.reroute_transitions auto branch_end end_state
          | None -> TypeAutomaton.reroute_transitions auto new_wildcard_state end_state
        end else begin
          if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in
            TypeAutomaton.add_transition auto current end_state (LabelSet.singleton (Delay(OptionDelay all_msg_specs))) false false
          )
        end;

        List.iter (fun o_ms ->
          let st = match o_ms.Lang.continuation with
            | Some cont -> StySeq (StyAtom o_ms.trigger, cont)
            | None -> StyAtom (o_ms.trigger)
          in
          let branch_end = build st current in
          TypeAutomaton.reroute_transitions auto branch_end end_state;
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
        let all_non_blocking = List.for_all (fun (o : offering_session_type) ->
          match o.Lang.trigger with
          | Lang.AtomicAct (Lang.AtomBMsg _) -> false
          | Lang.AtomicAct (Lang.AtomNBMsg _) -> true
          | _ -> false
        ) offerings in
        if not all_blocking && not all_non_blocking then 
          raise(TypeError [Text ("Mixed blocking and non-blocking offerings in external choice"); Except.codespan_local default_span]);  
        
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
          TypeAutomaton.add_transition auto current new_wildcard_state (LabelSet.singleton (Negation all_msg_specs)) false false;

          match wildcard_offer.Lang.continuation with
          | Some cont ->
            let branch_end = build cont new_wildcard_state in
            TypeAutomaton.reroute_transitions auto branch_end end_state
          | None -> TypeAutomaton.reroute_transitions auto new_wildcard_state end_state
        end else begin
          if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in
            TypeAutomaton.add_transition auto current end_state (LabelSet.singleton (Delay(OptionDelay all_msg_specs))) false false
          )
        end;

        let branch_types = List.map (fun o_ms ->
          match o_ms.Lang.continuation with
          | Some cont -> StySeq (StyAtom o_ms.trigger, cont)
          | None -> StyAtom (o_ms.trigger)
        ) all_msg_branches in

        let rec build_ultimate_choice (branch_types: Lang.session_type list) (acc : session_type) : session_type =
          match branch_types with
          | [] -> acc
          | [last] -> last
          | hd::tl -> 
            match acc with
            | StyTrue -> build_ultimate_choice tl hd
            | _ -> build_ultimate_choice tl (StyParallel (hd, acc))
        in
        let ultimate_choice = build_ultimate_choice branch_types StyTrue in

        let final_state = build ultimate_choice current in
        TypeAutomaton.reroute_transitions auto final_state end_state;
        end_state
      )
    | Lang.StyParallel (st1, st2) ->
      (Hashtbl.find auto.states current).accepting <- false;
      let final_state = create_synchronous_product auto st1 st2 current default_span in
      final_state
    | Lang.StyFuture st ->
      (Hashtbl.find auto.states current).accepting <- false;
      TypeAutomaton.add_transition auto current current LabelSet.empty false true;
      let cont_state = TypeAutomaton.new_state auto true in
      TypeAutomaton.add_transition auto current cont_state LabelSet.empty false true;
      let end_state = build st cont_state in
      end_state
    | Lang.StyVar var ->
      (
        let rec_start = Hashtbl.find_opt auto.rec_var_state_map var in
        match rec_start with
        | Some s_id ->
          TypeAutomaton.add_transition auto current s_id LabelSet.empty true false;
          current
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
    let end2 = find_accepting_state auto2 in
    let final_prod_state = get_product_state (end1, end2) in
    (Hashtbl.find auto.states final_prod_state).accepting <- true;

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
        
        (* Handle epsilon transitions - independent steps *)
        List.iter (fun t1 ->
          if t1.is_epsilon then (
            let next_ps = get_product_state (t1.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps LabelSet.empty true false;
            if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
              worklist := (t1.to_state, s2) :: !worklist
          )
        ) trans1;
        
        List.iter (fun t2 ->
          if t2.is_epsilon then (
            let next_ps = get_product_state (s1, t2.to_state) in
            TypeAutomaton.add_transition auto ps next_ps LabelSet.empty true false;
            if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
              worklist := (s1, t2.to_state) :: !worklist
          )
        ) trans2;
        
        (* Handle theta and regular transitions *)
        List.iter (fun t1 ->
          if not t1.is_epsilon then (
            List.iter (fun t2 ->
              if not t2.is_epsilon then (
                (* Both are non-epsilon transitions *)
                if t1.is_theta && not t2.is_theta then (
                  (* t1 is theta: auto1 advances independently, auto2 stays *)
                  let next_ps = get_product_state (t1.to_state, s2) in
                  TypeAutomaton.add_transition auto ps next_ps t2.label false false;
                  if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
                    worklist := (t1.to_state, s2) :: !worklist
                )
                else if t2.is_theta && not t1.is_theta then (
                  (* t2 is theta: auto2 advances independently, auto1 stays *)
                  let next_ps = get_product_state (s1, t2.to_state) in
                  TypeAutomaton.add_transition auto ps next_ps t1.label false false;
                  if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
                    worklist := (s1, t2.to_state) :: !worklist
                )
                else if not t1.is_theta && not t2.is_theta then (
                  (* Both are regular transitions: synchronous step with merged labels *)
                  let merged_labels = LabelSet.union t1.label t2.label in
                  let next_ps = get_product_state (t1.to_state, t2.to_state) in
                  TypeAutomaton.add_transition auto ps next_ps merged_labels false false;
                  if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then 
                    worklist := (t1.to_state, t2.to_state) :: !worklist
                )
                (* If both are theta, they can't synchronize - skip this case *)
              )
            ) trans2
          )
        ) trans1;
      )
    done;
    final_prod_state
  in

  let final_state = build st auto.start_state in
  (Hashtbl.find auto.states final_state).accepting <- true;
  auto