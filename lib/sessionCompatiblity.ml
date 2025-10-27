open Lang




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
end


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
  
  | Action(ImmediateAction m1), Action(ImmediateAction m2) -> m1 = m2
  | Action(ImmediateAction m1), Action(BlockAction m2) -> m1 = m2 


  | Delay (MessageDelay _), Delay (CycleDelay _) -> true
  | Delay (MessageDelay m1), Action(ImmediateAction m2) -> m1 <> m2
  | Delay (MessageDelay m1), Action(BlockAction m2) -> m1 <> m2
  
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


let rec build_automaton (st: Lang.session_type) : TypeAutomaton.t =
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

    | Lang.StyChoiceDual offerings -> (* External choice m1 & m2 *)
      let final = TypeAutomaton.new_state auto false in
      
      (* Helper to get message_specifier from atomic_action *)
      let get_msg_spec = function
        | Lang.AtomBMsg m -> m
        | Lang.AtomNBMsg m -> m
      in
      let all_msg_specs = List.map (fun (o : offering_session_type) -> get_msg_spec o.Lang.trigger) offerings in
      
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
      
    | Lang.StyAtom (Lang.AtomDelay n) ->
      let next_s = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Delay (CycleDelay n))) false;
      next_s
      
    | Lang.StyAtom (Lang.AtomicAct(Lang.AtomBMsg m)) ->
      let next_s = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action(BlockAction m))) false;
      TypeAutomaton.add_transition auto current current (LabelSet.singleton (Delay(MessageDelay m))) false;
      next_s
      
    | Lang.StyAtom (Lang.AtomicAct(Lang.AtomNBMsg m)) ->
      let next_s = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action(ImmediateAction m))) false;
      next_s

    | Lang.StyParallel (st1, st2) ->
      create_synchronous_product auto st1 st2 current
      
    | Lang.StyFuture st ->
      (* Add #F epsilon self-loop *)
      TypeAutomaton.add_transition auto current current (LabelSet.singleton (Future None)) true;
      (* Or start the actual behavior *)
      build st current
  

  and create_synchronous_product (auto: TypeAutomaton.t) (st1: Lang.session_type) (st2: Lang.session_type) (current_start_node: int) : int =
    (* 1. Build sub-automata for st1 and st2 *)
    let auto1 = build_automaton st1 in
    let auto2 = build_automaton st2 in
    
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



let create_product_automaton (auto1: TypeAutomaton.t) (auto2: TypeAutomaton.t) 
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
      

      List.iter (fun t1 ->
        if t1.is_epsilon then (
          found_match := true;
          let to_ps = get_state_id (t1.to_state, s2) in
          TypeAutomaton.add_transition product_auto ps to_ps t1.label true;
          if not (IntPairSet.mem (t1.to_state, s2) !visited) then
            worklist := (t1.to_state, s2) :: !worklist
        )
      ) trans1;
      
      List.iter (fun t2 ->
        if t2.is_epsilon then (
          found_match := true;
          let to_ps = get_state_id (s1, t2.to_state) in
          TypeAutomaton.add_transition product_auto ps to_ps t2.label true;
          if not (IntPairSet.mem (s1, t2.to_state) !visited) then
            worklist := (s1, t2.to_state) :: !worklist
        )
      ) trans2;
      
      (* 3. Check for looping from accepting states  *)
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
      );

      if not !found_match && not (s1_state.accepting && s2_state.accepting) then (

      )
    )
  done;
  

  let reachable_accepting_states = Hashtbl.fold (fun id s acc ->
    (* Check if state is accepting AND was visited/is part of the product graph *)
    if s.accepting && Hashtbl.fold (fun _ v found -> found || v = id) state_map false then
      id :: acc 
    else 
      acc
  ) product_auto.states [] in
  
  if reachable_accepting_states = [] then
    Error "Deadlock: No reachable accepting states in product automaton."
  else
    Ok product_auto


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
          | Action(ImmediateAction m) -> Printf.sprintf "m:%s" (Lang.string_of_msg_spec m)
          | Action(BlockAction m) -> Printf.sprintf "B_m:%s" (Lang.string_of_msg_spec m)
          | Delay(CycleDelay n) -> Printf.sprintf "#%d" n
          | Delay(MessageDelay m) -> Printf.sprintf "#_B_m:%s" (Lang.string_of_msg_spec m)
          | OfferingDelay ms -> Printf.sprintf "#EC:[%s]" (String.concat ";" (List.map Lang.string_of_msg_spec ms))
          | OfferingLabel ms -> Printf.sprintf "#ac:[%s]" (String.concat ";" (List.map Lang.string_of_msg_spec ms))
          | ChoiceLabel -> "#c"
          | Future None -> "#F"
          | Future(Some(ImmediateAction m)) -> Printf.sprintf "#F_m:%s" (Lang.string_of_msg_spec m)
          | Future(Some(BlockAction m)) -> Printf.sprintf "#FB_m:%s" (Lang.string_of_msg_spec m)
          | Terminal -> "#end"
        ))
    in
    Printf.fprintf out "  %d -> %d [label=\"%s\"];\n" t.from_state t.to_state label_str
  ) auto.transitions;

  Printf.fprintf out "}\n";
  flush out


let check_compatibility (type1: Lang.session_type) (type2: Lang.session_type) (module_id1: identifier) (module_id2 : identifier) (verbose : bool)  : bool * string =

  let auto1 = build_automaton type1 in
  let auto2 = build_automaton type2 in

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


  match create_product_automaton auto1 auto2 with
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