open Lang
open Except



type action_kind = 
  | ImmediateAction of Lang.message_specifier
  | BlockAction of Lang.message_specifier

type delay_kind = 
  | CycleDelay of int
  | MessageDelay of Lang.message_specifier 


type label_kind =
  | Action of action_kind
  | Delay of delay_kind
  | OfferingDelay of Lang.message_specifier list
  | Future of action_kind option
  | ChoiceLabel
  | OfferingLabel of Lang.message_specifier list
  | Terminal

type state = {
  id : int;
  mutable accepting : bool;
}

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
}

type typeAutomaton = {
  states : (int, state) Hashtbl.t;
  mutable transitions : transition list;
  start_state : int;
  mutable next_state_id : int;
}

(* --- Automaton Helper Functions --- *)


module TypeAutomaton = struct
  type t = typeAutomaton

  let create () : t =
    let start_state = 0 in
    let states = Hashtbl.create 10 in
    Hashtbl.add states start_state { id = start_state; accepting = false };
    {
      states = states;
      transitions = [];
      start_state = start_state;
      next_state_id = 1;
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

 
  let add_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) (is_epsilon: bool) : unit =
    let found = ref false in
    let new_transitions = List.map (fun t ->
      if t.from_state = from_s && t.to_state = to_s && t.is_epsilon = is_epsilon then
        (found := true; { t with label = LabelSet.union t.label label_set })
      else t
    ) auto.transitions in
    
    if !found then
      auto.transitions <- new_transitions
    else
      let trans = { from_state = from_s; to_state = to_s; label = label_set; is_epsilon } in
      auto.transitions <- trans :: auto.transitions
  let remove_transition (auto: t) (from_s: int) (to_s: int) (label_set: LabelSet.t) : unit =
    auto.transitions <- List.filter (fun t ->
      not (t.from_state = from_s && t.to_state = to_s && LabelSet.equal t.label label_set)
    ) auto.transitions
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
      else
        String.concat "," (LabelSet.elements t.label |> List.map (function
          | Action(ImmediateAction m) -> Printf.sprintf "NB:%s" (Lang.string_of_msg_spec m)
          | Action(BlockAction m) -> Printf.sprintf "B:%s" (Lang.string_of_msg_spec m)
          | Delay(CycleDelay n) -> Printf.sprintf "#%d" n
          | Delay(MessageDelay m) -> Printf.sprintf "#_B:%s" (Lang.string_of_msg_spec m)
          | OfferingDelay ms -> Printf.sprintf "#EC:[%s]" (String.concat ";" (List.map Lang.string_of_msg_spec ms))
          | OfferingLabel ms -> Printf.sprintf "#ac:[%s]" (String.concat ";" (List.map Lang.string_of_msg_spec ms))
          | ChoiceLabel -> "#c"
          | Future None -> "#F"
          | Future(Some(ImmediateAction m)) -> Printf.sprintf "#FNB:%s" (Lang.string_of_msg_spec m)
          | Future(Some(BlockAction m)) -> Printf.sprintf "#FB:%s" (Lang.string_of_msg_spec m)
          | Terminal -> "#end"
        ))
    in
    Printf.fprintf out "  %d -> %d [label=\"%s\"];\n" t.from_state t.to_state label_str
  ) auto.transitions;

  Printf.fprintf out "}\n";
  flush out


let check_label_satisfiability (l1: label_kind) (l2: label_kind) : bool =
  match l1, l2 with
  (* Choice synchronization must match *)
  | ChoiceLabel, OfferingLabel _ -> true
  | OfferingLabel _, ChoiceLabel -> true
  | ChoiceLabel, ChoiceLabel -> true

  

  | Delay (CycleDelay _), _ -> true (* # |-> * *)

  | Action(BlockAction m1), Action(ImmediateAction m2) -> m1 = m2
  | Action(BlockAction m1), Action(BlockAction m2) -> m1 = m2
  | Action(BlockAction m1), Future(Some(ImmediateAction m2)) -> m1 = m2 
  | Action(BlockAction m1), Future(Some(BlockAction m2)) -> m1 = m2
  
  | Action(ImmediateAction m1), Action(ImmediateAction m2) -> m1 = m2
  | Action(ImmediateAction m1), Action(BlockAction m2) -> m1 = m2 


  | Delay (MessageDelay _), Delay (CycleDelay _) -> true
  | Delay (MessageDelay m1), Action(ImmediateAction m2) -> m1 <> m2
  | Delay (MessageDelay m1), Action(BlockAction m2) -> m1 <> m2
  | OfferingDelay _, Delay (CycleDelay _) -> true
  | OfferingDelay ms1, Delay (MessageDelay m2) -> List.for_all (fun m1 -> m1 <> m2) ms1
  | Delay (MessageDelay m1) , OfferingDelay ms2 -> List.for_all (fun m2 -> m1 <> m2) ms2
  
  (* #FB_m |-> B_m, self *)
  | Future(Some(BlockAction m1)), Action(BlockAction m2) -> m1 = m2
  | Future(Some(BlockAction m1)), Future(Some(BlockAction m2)) -> m1 = m2

  | Future None, _ -> false (* #F |-> Nothing *)
  
  | Future(Some(ImmediateAction m1)), Action(BlockAction m2) -> m1 = m2
  
  | Terminal, Terminal -> false
  | Terminal, _ -> true
  
  | _ -> false


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

let rec build_automaton (st: Lang.session_type) (default_span : Lang.code_span) :  TypeAutomaton.t =
  let auto = TypeAutomaton.create () in
  
  (* Internal recursive builder *)
  let rec build (s_type: Lang.session_type) (current: int) : int =
    match s_type with
    | Lang.StySeq (st1, st2) ->
      let mid = build st1 current in
      (Hashtbl.find auto.states mid).accepting <- false;
      build st2 mid
    
    | Lang.StyChoice (st1, st2) -> (* Internal choice m1 + m2 *)
      let left_end = build st1 current in
      let choice_state = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto left_end choice_state (LabelSet.singleton ChoiceLabel) false;
      build st2 choice_state

    | Lang.StyOffer offerings -> (* External choice m1 & m2 *)
      let final = TypeAutomaton.new_state auto false in
      
      (* Helper to get message_specifier from atomic_action *)
      let get_msg_spec = function
        | Lang.AtomBMsg m -> m
        | Lang.AtomNBMsg m -> m
      in
      let all_msg_specs = List.map (fun (o : offering_session_type) -> get_msg_spec o.Lang.trigger) offerings in
      let all_blocking  = List.for_all (fun (o : offering_session_type) ->
        match o.Lang.trigger with
        | Lang.AtomBMsg _ -> true
        | Lang.AtomNBMsg _ -> false
      ) offerings in
      let all_non_blocking = List.for_all (fun (o : offering_session_type) ->
        match o.Lang.trigger with
        | Lang.AtomBMsg _ -> false
        | Lang.AtomNBMsg _ -> true
      ) offerings in
      if not all_blocking && not all_non_blocking then
        raise(TypeError [Text ("Mixed blocking and non-blocking offerings in external choice"); Except.codespan_local default_span])
      else if all_blocking then
        TypeAutomaton.add_transition auto current current (LabelSet.singleton (OfferingDelay all_msg_specs)) false;

      List.iter (fun offer ->
        let branch_s = TypeAutomaton.new_state auto false in
        let label, _is_blocking = match offer.Lang.trigger with
          | Lang.AtomBMsg m -> (Action(BlockAction m), true)
          | Lang.AtomNBMsg m -> (Action(ImmediateAction m), false)
        in
        TypeAutomaton.add_transition auto current branch_s (LabelSet.singleton label) false;
        
        let branch_end = match offer.Lang.continuation with
          | Some cont -> build cont branch_s
          | None -> branch_s (* If no continuation, the branch ends immediately *)
        in
        
        TypeAutomaton.add_transition auto branch_end current (LabelSet.singleton (OfferingLabel all_msg_specs)) false;
        (* Add epsilon to final state (for exiting the choice) *)
        TypeAutomaton.add_transition auto branch_end final LabelSet.empty true;
        
      ) offerings;
      final
    | Lang.StyXOffer _offerings -> (
      raise (TypeError [Text ("Exclusive Offer is not implemented in session automaton construction"); Except.codespan_local default_span])
    )

    | Lang.StyAtom (Lang.AtomDelay n) ->
      let next_s = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Delay (CycleDelay n))) false;
      next_s
      
    | Lang.StyAtom (Lang.AtomicAct(Lang.AtomBMsg m)) ->
      let label_is_offering (l : LabelSet.t) =
        (* for all labels in this set are of the following kind *)
        let labels = LabelSet.elements l in
        let labels_are_offering labels =
          List.for_all (function
            | OfferingLabel _ -> true
            | _ -> false
          ) labels
        in
        labels_are_offering labels
      in

      let label_is_future (l : LabelSet.t) =
        let labels = LabelSet.elements l in
        let labels_are_future labels =
          List.for_all (function
            | Future _ -> true
            | _ -> false
          ) labels
        in
        labels_are_future labels in

      let is_external_recursive = 
        List.filter_map ( fun t ->
          if t.from_state = current && label_is_offering t.label then
            Some (t.to_state, t.label)
          else
            None
        ) auto.transitions
      in
      if is_external_recursive <> [] then
        List.iter (fun (to_state, label) ->
          TypeAutomaton.add_transition auto current to_state label false
        ) is_external_recursive;
      
      let is_future = 
        List.find_opt ( fun t ->
          if t.from_state = current && t.to_state == current && label_is_future t.label then
            true
          else
            false
        ) auto.transitions
      in
      let next_s = TypeAutomaton.new_state auto false in
      if Option.is_some is_future then
        (
        TypeAutomaton.remove_transition auto current current (LabelSet.singleton (Future None));
        TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Future (Some (BlockAction m)))) false
        )
      else 
      (
        TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action(BlockAction m))) false;
      );
      TypeAutomaton.add_transition auto current current (LabelSet.singleton (Delay(MessageDelay m))) false;
      next_s
      
    | Lang.StyAtom (Lang.AtomicAct(Lang.AtomNBMsg m)) ->
      let next_s = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action(ImmediateAction m))) false;
      next_s

    | Lang.StyParallel (st1, st2) ->
      create_synchronous_product auto st1 st2 current default_span
      
    | Lang.StyFuture st ->
      (* Add #F epsilon self-loop *)
      TypeAutomaton.add_transition auto current current (LabelSet.singleton (Future None)) false;
      (* Or start the actual behavior *)
      build st current
  

  and create_synchronous_product (auto: TypeAutomaton.t) (st1: Lang.session_type) (st2: Lang.session_type) (current_start_node: int) (default_span : code_span) : int =
    (* 1. Build sub-automata for st1 and st2 *)
    let auto1 = build_automaton st1 default_span   in
    let auto2 = build_automaton st2 default_span in
    
    (* 2. Build product automaton manually into `auto` *)
    let state_map : ((int * int), int) Hashtbl.t = Hashtbl.create 10 in
    
    let get_product_state (s1, s2) =
      try Hashtbl.find state_map (s1, s2)
      with Not_found ->
        (* The start state is the one we were given *)
        let new_id = 
          if (s1 = auto1.start_state) && (s2 = auto2.start_state) then current_start_node
          else TypeAutomaton.new_state auto false
        in
        Hashtbl.add state_map (s1, s2) new_id;
        new_id
    in
    
    let find_accepting_state (sub_auto: TypeAutomaton.t) =
      Hashtbl.fold (fun id s acc -> if s.accepting then Some id else acc) sub_auto.states None
      |> function
         | Some id -> id
         | None -> failwith "Sub-automaton for parallel has no accepting state"
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
    let visited = ref (IntPairSet.empty) in 
    
    while !worklist <> [] do
      let (s1, s2) = List.hd !worklist in
      worklist := List.tl !worklist;
      
      if not (IntPairSet.mem (s1, s2) !visited) then (
        visited := IntPairSet.add (s1, s2) !visited;
        let ps = get_product_state (s1, s2) in
        
        let trans1 = List.filter (fun t -> t.from_state = s1) auto1.transitions in
        let trans2 = List.filter (fun t -> t.from_state = s2) auto2.transitions in
        
        (* Synchronous step: one from left AND one from right, merge labels *)
        List.iter (fun t1 ->
          List.iter (fun t2 ->
            (* Epsilon transitions don't sync *)
            if not t1.is_epsilon && not t2.is_epsilon then (
              let merged_labels = LabelSet.union t1.label t2.label in
              let next_ps = get_product_state (t1.to_state, t2.to_state) in
              TypeAutomaton.add_transition auto ps next_ps merged_labels false;
              
              if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then 
                worklist := (t1.to_state, t2.to_state) :: !worklist
            )
          ) trans2
        ) trans1;
        

        List.iter (fun t1 ->
          if t1.from_state = t1.to_state then (
            let next_ps = get_product_state (t1.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps t1.label t1.is_epsilon;
             if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
                worklist := (t1.to_state, s2) :: !worklist
          )
        ) trans1;
        
        List.iter (fun t2 ->
          if t2.from_state = t2.to_state then (
            let next_ps = get_product_state (s1, t2.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t2.label t2.is_epsilon;
            if not (IntPairSet.mem (s1, t2.to_state) !visited) then
                worklist := (s1, t2.to_state) :: !worklist
          )
        ) trans2;
        

        if s1 = end1 then (
          List.iter (fun t2 ->
            if t2.from_state != t2.to_state then ( (* Not a self-loop *)
              let next_ps = get_product_state (s1, t2.to_state) in
              TypeAutomaton.add_transition auto ps next_ps t2.label t2.is_epsilon;
              if not (IntPairSet.mem (s1, t2.to_state) !visited) then
                worklist := (s1, t2.to_state) :: !worklist
            )
          ) trans2
        );
        
        if s2 = end2 then (
          List.iter (fun t1 ->
            if t1.from_state != t1.to_state then ( (* Not a self-loop *)
              let next_ps = get_product_state (t1.to_state, s2) in
              TypeAutomaton.add_transition auto ps next_ps t1.label t1.is_epsilon;
              if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
                worklist := (t1.to_state, s2) :: !worklist
            )
          ) trans1
        );
      )
    done;
    final_prod_state
  in


  let final_state = build st auto.start_state in
  (Hashtbl.find auto.states final_state).accepting <- true;
  TypeAutomaton.add_transition auto final_state final_state (LabelSet.singleton Terminal) false;
  auto



let create_product_automaton (auto1: TypeAutomaton.t) (auto2: TypeAutomaton.t) (_default_span: Lang.code_span)  (verbose : bool)  
  : (TypeAutomaton.t, string) result =
  
  let product_auto = TypeAutomaton.create () in
  let state_map : ((int * int), int) Hashtbl.t = Hashtbl.create 10 in
  
  let get_state_id (s1, s2) =
    try Hashtbl.find state_map (s1, s2)
    with Not_found ->
      let s1_state = Hashtbl.find auto1.states s1 in
      let s2_state = Hashtbl.find auto2.states s2 in
      let new_id = TypeAutomaton.new_state product_auto (s1_state.accepting && s2_state.accepting) in
      Hashtbl.add state_map (s1, s2) new_id;
      new_id
  in
  let initial_product_state = get_state_id (auto1.start_state, auto2.start_state) in
  let product_auto = { product_auto with start_state = initial_product_state } in
   let remove_unreachable_states () =
        let reachable = Hashtbl.create 10 in
        let rec dfs state_id =
          if not (Hashtbl.mem reachable state_id) then (
            Hashtbl.add reachable state_id ();
            List.iter (fun t ->
              if t.from_state = state_id then
                dfs t.to_state
            ) product_auto.transitions
          )
        in
        dfs product_auto.start_state;
        
        Hashtbl.iter (fun id _ ->
          if not (Hashtbl.mem reachable id) then
            TypeAutomaton.remove_state product_auto id
        ) product_auto.states in
  let module IntPairSet = Set.Make(struct type t = int * int let compare = Stdlib.compare end) in
  let worklist = ref [(auto1.start_state, auto2.start_state)] in
  let visited = ref (IntPairSet.empty) in
  
  while !worklist <> [] do
    let (s1, s2) = List.hd !worklist in
    worklist := List.tl !worklist;
    
    if not (IntPairSet.mem (s1, s2) !visited) then (
      visited := IntPairSet.add (s1, s2) !visited;
      let ps = get_state_id (s1, s2) in
      let s1_state = Hashtbl.find auto1.states s1 in
      let s2_state = Hashtbl.find auto2.states s2 in

      let trans1 = List.filter (fun t -> t.from_state = s1) auto1.transitions in
      let trans2 = List.filter (fun t -> t.from_state = s2) auto2.transitions in
      
      let found_match = ref false in
      

      List.iter (fun t1 ->
        if not t1.is_epsilon then
          List.iter (fun t2 ->
            if not t2.is_epsilon && label_equivalence t1.label t2.label then (
              found_match := true;
              let to_ps = get_state_id (t1.to_state, t2.to_state) in
              let combined_labels = LabelSet.union t1.label t2.label in
              TypeAutomaton.add_transition product_auto ps to_ps combined_labels false;
              
              if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then
                worklist := (t1.to_state, t2.to_state) :: !worklist
            )
          ) trans2
      ) trans1;
      if not !found_match then(
      List.iter (fun t1 ->
          if t1.is_epsilon then (
            found_match := true;
            let to_ps = get_state_id (t1.to_state, s2) in
            TypeAutomaton.add_transition product_auto ps to_ps t1.label true;
            if not (IntPairSet.mem (t1.to_state, s2) !visited) then
              worklist := (t1.to_state, s2) :: !worklist
          )
        ) trans1
      );

      if not !found_match then (
      List.iter (fun t2 ->
        if t2.is_epsilon then (
          found_match := true;
          let to_ps = get_state_id (s1, t2.to_state) in
          TypeAutomaton.add_transition product_auto ps to_ps t2.label true;
          if not (IntPairSet.mem (s1, t2.to_state) !visited) then
            worklist := (s1, t2.to_state) :: !worklist
        )
      ) trans2
      );
      
      if not !found_match then (
      if not (s1_state.accepting && s2_state.accepting) then (
        if s1_state.accepting then (
          (* auto1 is done, check transitions from its start *)
          let trans1_initial = List.filter (fun t -> t.from_state = auto1.start_state) auto1.transitions in
          List.iter (fun t1_init ->
              if not t1_init.is_epsilon then
                List.iter (fun t2 ->
                  if not t2.is_epsilon && label_equivalence t1_init.label t2.label then (
                    found_match := true;
                    let to_ps = get_state_id (t1_init.to_state, t2.to_state) in
                    TypeAutomaton.add_transition product_auto ps to_ps (LabelSet.union t1_init.label t2.label) false;
                    if not (IntPairSet.mem (t1_init.to_state, t2.to_state) !visited) then
                      worklist := (t1_init.to_state, t2.to_state) :: !worklist
                  )
                ) trans2
          ) trans1_initial
        );
        
        if s2_state.accepting then (
          (* auto2 is done, check transitions from its start *)
          let trans2_initial = List.filter (fun t -> t.from_state = auto2.start_state) auto2.transitions in
          List.iter (fun t1 ->
              if not t1.is_epsilon then
                List.iter (fun t2_init ->
                  if not t2_init.is_epsilon && label_equivalence t1.label t2_init.label then (
                    found_match := true;
                    let to_ps = get_state_id (t1.to_state, t2_init.to_state) in
                    TypeAutomaton.add_transition product_auto ps to_ps (LabelSet.union t1.label t2_init.label) false;
                    if not (IntPairSet.mem (t1.to_state, t2_init.to_state) !visited) then
                      worklist := (t1.to_state, t2_init.to_state) :: !worklist
                  )
                ) trans2_initial
          ) trans1
        );
      )
      );

     

      if not !found_match && not (s1_state.accepting && s2_state.accepting) then (
        remove_unreachable_states ();
          if verbose then (
            let file = "product_automaton_debug.dot" in
            let out = open_out file in
            print_automaton_dot product_auto out;
            close_out out
          );
          raise (Except.TypeError [Text ((Printf.sprintf "No matching transitions found in product automaton  s1 =  %d | s2 = %d | current state = %d  " s1_state.id s2_state.id (get_state_id (s1_state.id, s2_state.id))) ); Except.codespan_local _default_span])
      )
 


    )
  done;
  

  remove_unreachable_states ();
  let reachable_accepting_states = Hashtbl.fold (fun id s acc ->
    (* Check if state is accepting AND was visited/is part of the product graph *)
    if s.accepting && Hashtbl.fold (fun _ v found -> found || v = id) state_map false then
      id :: acc 
    else 
      acc
  ) product_auto.states [] in
  
  if reachable_accepting_states = [] then (
     if verbose then (
            let file = "product_automaton_debug.dot" in
            let out = open_out file in
            print_automaton_dot product_auto out;
            close_out out
    );
    Error "No accepting states reachable in product automaton; incompatible session types."
  )
  else
    Ok product_auto

let create_product_automaton_multiparty (autos: (TypeAutomaton.t * identifier) list) (_default_span: Lang.code_span) (verbose : bool)
  : (TypeAutomaton.t, string) result =

  let product_auto = TypeAutomaton.create () in
  let state_map : ((int list), int) Hashtbl.t = Hashtbl.create 10 in


  let get_state_id (states: int list) =
    try Hashtbl.find state_map states
    with Not_found ->
      let accepting = List.for_all2 (fun (auto, _) s_id ->
        let s = Hashtbl.find auto.states s_id in
        s.accepting
      ) autos states in
      let new_id = TypeAutomaton.new_state product_auto accepting in
      Hashtbl.add state_map states new_id;
      new_id
  in

  let initial_product_state = get_state_id (List.map (fun (auto, _) -> auto.start_state) autos) in
  let product_auto = { product_auto with start_state = initial_product_state } in

  let remove_unreachable_states () =
    let reachable = Hashtbl.create 10 in
    let rec dfs state_id =
      if not (Hashtbl.mem reachable state_id) then (
        Hashtbl.add reachable state_id ();
        List.iter (fun t ->
          if t.from_state = state_id then
            dfs t.to_state
        ) product_auto.transitions
      )
    in
    dfs product_auto.start_state;
    
    Hashtbl.iter (fun id _ ->
      if not (Hashtbl.mem reachable id) then
        TypeAutomaton.remove_state product_auto id
    ) product_auto.states 
  in


  let module IntListSet = Set.Make(struct type t = int list let compare = Stdlib.compare end) in
  let worklist = ref [List.map (fun (auto, _) -> auto.start_state) autos] in
  let visited = ref (IntListSet.empty) in

  while !worklist <> [] do
    let states = List.hd !worklist in
    worklist := List.tl !worklist;
    
    if not (IntListSet.mem states !visited) then (
      visited := IntListSet.add states !visited;
      let ps = get_state_id states in

      (* To Do : Better save the outbound transitions in the state representation (like graph) instead of getting them each time *)
      let transitions_list = List.mapi (fun idx (auto, _) ->
        List.filter (fun t -> t.from_state = List.nth states idx) auto.transitions
      ) autos in

      let found_any_match = ref false in

      (* Collect all non-epsilon transitions with their automaton indices *)
      let indexed_transitions = 
        List.mapi (fun idx trans_list ->
          List.filter_map (fun t ->
            if not t.is_epsilon then Some (idx, t) else None
          ) trans_list
        ) transitions_list
        |> List.flatten
      in

      (* Try to find a valid subset of transitions where all obligations are met *)
      let rec find_valid_subset (candidates: (int * transition) list) 
                                 (selected: (int * transition) list) 
                                 (remaining: (int * transition) list) =
        match remaining with
        | [] ->
            (* Check if all selected transitions have their obligations met *)
            if selected <> [] then (
              let all_satisfied = List.for_all (fun (idx1, t1) ->
                (* Check if t1's obligations are met by at least one other transition *)
                List.exists (fun (idx2, t2) ->
                  idx1 <> idx2 && label_equivalence_one_way t1.label t2.label
                ) selected
              ) selected in
              
              if all_satisfied then (
                (* Found a valid subset! Create the product transition *)
                found_any_match := true;
                
                (* Create new state advancing only the automata in selected *)
                let to_states = List.mapi (fun idx s ->
                  match List.find_opt (fun (sel_idx, _) -> sel_idx = idx) selected with
                  | Some (_, t) -> t.to_state
                  | None -> s
                ) states in
                
                let to_ps = get_state_id to_states in
                
                (* Combine all labels from selected transitions *)
                let combined_labels = List.fold_left (fun acc (_, t) ->
                  LabelSet.union acc t.label
                ) LabelSet.empty selected in
                
                TypeAutomaton.add_transition product_auto ps to_ps combined_labels false;
                
                if not (IntListSet.mem to_states !visited) then
                  worklist := to_states :: !worklist;
                
                true
              ) else false
            ) else false
        | (idx, t) :: rest ->
            (* Try including this transition *)
            let with_t = find_valid_subset candidates ((idx, t) :: selected) rest in
            (* Try excluding this transition *)
            let without_t = find_valid_subset candidates selected rest in
            with_t || without_t
      in

      (* Try to find valid subsets of size >= 2 *)
      if indexed_transitions <> [] then (
        let _ = find_valid_subset indexed_transitions [] indexed_transitions in
        ()
      );

      (* If no matches found with non-epsilon transitions, try epsilon transitions *)
      if not !found_any_match then (
        List.iteri (fun idx trans_list ->
          List.iter (fun t ->
            if t.is_epsilon then (
              found_any_match := true;
              let to_states = List.mapi (fun i s -> if i = idx then t.to_state else s) states in
              let to_ps = get_state_id to_states in
              TypeAutomaton.add_transition product_auto ps to_ps t.label true;
              
              if not (IntListSet.mem to_states !visited) then
                worklist := to_states :: !worklist
            )
          ) trans_list
        ) transitions_list
      );

      (* Handle looping back to start states when automata reach accepting state *)
      if not !found_any_match then (
        let state_infos = List.map2 (fun (auto, _) s_id ->
          (auto, s_id, Hashtbl.find auto.states s_id)
        ) autos states in
        
        let any_accepting_not_all = 
          List.exists (fun (_, _, s) -> s.accepting) state_infos &&
          not (List.for_all (fun (_, _, s) -> s.accepting) state_infos) in
        
        if any_accepting_not_all then (
          (* Collect transitions including start states for accepting automata *)
          let extended_indexed_transitions = 
            List.mapi (fun idx (auto, s_id, s) ->
              let trans_list = 
                if s.accepting then
                  List.filter (fun t -> t.from_state = auto.start_state && not t.is_epsilon) auto.transitions
                else
                  List.filter (fun t -> t.from_state = s_id && not t.is_epsilon) auto.transitions
              in
              List.map (fun t -> (idx, t)) trans_list
            ) state_infos
            |> List.flatten
          in
          
          (* Try to find valid subset with looped automata *)
          let _ = find_valid_subset extended_indexed_transitions [] extended_indexed_transitions in
          ()
        )
      );

      (* Check if we're stuck *)
      if not !found_any_match then (
        let all_accepting = List.for_all2 (fun (auto, _) s_id ->
          let s = Hashtbl.find auto.states s_id in
          s.accepting
        ) autos states in
        
        let any_has_transitions = List.exists2 (fun (auto, _) s_id ->
          List.exists (fun t -> t.from_state = s_id) auto.transitions
        ) autos states in
        
        if not all_accepting && any_has_transitions then (
          remove_unreachable_states ();
          if verbose then (
            let file = "product_automaton_multiparty_debug.dot" in
            let out = open_out file in
            print_automaton_dot product_auto out;
            close_out out
          );
          let state_ids_str = String.concat ", " (List.map string_of_int states) in
          raise (Except.TypeError [
            Text (Printf.sprintf "No valid transition subset found where all obligations are met at states [%s]" state_ids_str);
            Except.codespan_local _default_span
          ])
        )
      )
    )
  done;

  remove_unreachable_states ();
  
  (* Check if any accepting states are reachable *)
  let reachable_accepting_states = Hashtbl.fold (fun id s acc ->
    if s.accepting && Hashtbl.fold (fun _ v found -> found || v = id) state_map false then
      id :: acc 
    else 
      acc
  ) product_auto.states [] in
  
  if reachable_accepting_states = [] then (
    if verbose then (
      let file = "product_automaton_multiparty_debug.dot" in
      let out = open_out file in
      print_automaton_dot product_auto out;
      close_out out
    );
    Error "No accepting states reachable in multiparty product automaton; incompatible session types."
  )
  else
    Ok product_auto



let check_compatibility (type1: Lang.session_type ast_node) (type2: Lang.session_type ast_node) (module_id1: identifier) (module_id2 : identifier) (verbose : bool) (default_span : code_span)  : bool * string =

  let auto1 = build_automaton type1.d type1.span in
  let auto2 = build_automaton type2.d type2.span in

  if verbose then begin
    let file1 = Printf.sprintf "automaton_%s.dot" module_id1 in
    let file2 = Printf.sprintf "automaton_%s.dot" module_id2 in
    let out1 = open_out file1 in
    let out2 = open_out file2 in
    print_automaton_dot auto1 out1;
    print_automaton_dot auto2 out2;
    close_out out1;
    close_out out2;
    Printf.eprintf "Automata printed to %s and %s\n" file1 file2;
  end;


  match create_product_automaton auto1 auto2 default_span verbose with
  | Ok _product_auto ->
    if verbose then begin
      Printf.eprintf "Product automaton created successfully.\n";
      let file = Printf.sprintf "product_automaton_%s_%s.dot" module_id1 module_id2 in 
      let out = open_out file in
      print_automaton_dot _product_auto out;
      close_out out;
      Printf.eprintf "Product automaton printed to %s\n" file;
    end;
    (true, "Compatible, constructed product automaton.")
  | Error reason -> (false, reason)


let check_compatiblity_multiparty (types: (Lang.session_type ast_node * identifier) list) (verbose : bool) (default_span : code_span) : bool * string =
  
  let autos = List.map (fun (stype_node, module_id) ->
    let auto = build_automaton stype_node.d stype_node.span in
    if verbose then begin
      let file = Printf.sprintf "automaton_%s.dot" module_id in
      let out = open_out file in
      print_automaton_dot auto out;
      close_out out;
      Printf.eprintf "Automaton for %s printed to %s\n" module_id file;
    end;
    (auto, module_id)
  ) types in

  match create_product_automaton_multiparty autos default_span verbose with
  | Ok _product_auto ->
    if verbose then begin
      Printf.eprintf "Multiparty product automaton created successfully.\n";
      let file = "product_automaton_multiparty.dot" in 
      let out = open_out file in
      print_automaton_dot _product_auto out;
      close_out out;
      Printf.eprintf "Multiparty product automaton printed to %s\n" file;
    end;
    (true, "Compatible multiparty session types, constructed product automaton.")
  | Error reason -> (false, reason)
  