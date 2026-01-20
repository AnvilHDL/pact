open Lang
open Except
open SessionAutomaton

let rec build_automaton (name : identifier option) (st: Lang.session_type) (default_span : Lang.code_span)  : TypeAutomaton.t =
  let auto = TypeAutomaton.create () in

  (
  match name with 
  | Some id -> TypeAutomaton.change_name id auto
  | None -> ()
  )
  ;
  
  (* Internal recursive builder *)
  let rec build (s_type: Lang.session_type) (current: int) : int =
    match s_type with
    | Lang.StyAtom at ->
      (
        match at with
        | Lang.AtomicAct (Lang.AtomBMsg m) -> 
          (
            (Hashtbl.find auto.states current).accepting <- false;
            TypeAutomaton.add_transition auto current current (LabelSet.singleton (OptionDelay [m])) false false false false;
            let next_s = TypeAutomaton.new_state auto true in
            TypeAutomaton.add_transition auto current next_s (LabelSet.singleton (Action m)) false false false false;
            TypeAutomaton.append_offers auto current [m];
            next_s
          )
        | Lang.AtomicAct (Lang.AtomNBMsg m) ->
          (
            (Hashtbl.find auto.states current).accepting <- false;
            let next_s = TypeAutomaton.new_state auto true in
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
      TypeAutomaton.add_transition auto current left_root (LabelSet.singleton (Theta st1)) false true false false;
      let right_root = TypeAutomaton.new_state auto false in
      TypeAutomaton.add_transition auto current right_root (LabelSet.singleton (Theta st2)) false true false false;
      let left_end = build st1 left_root in
      let right_end = build st2 right_root in
      (Hashtbl.find auto.states left_end).accepting <- false;
      (Hashtbl.find auto.states right_end).accepting <- false;
      let choice_state = TypeAutomaton.new_state auto true in
      if not (left_end = current) then
        TypeAutomaton.reroute_transitions auto left_end choice_state;
      if not (right_end = current) then
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
            | None -> StyAtom (AtomicAct (AtomNBMsg m))
          in

          let branch_end = build st current in

        if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in
            TypeAutomaton.add_transition auto current current (LabelSet.singleton (OptionDelay all_msg_specs)) false false false false
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

        let other_permuts = List.filter (fun btype ->
          not (List.mem btype branch_types)
        ) all_permut_branch_type in


        List.iteri (fun i o_ms ->
          let m = match o_ms.Lang.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> m
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> m
            | _ -> failwith "Should not reach here"
          in
          let st = match o_ms.Lang.continuation with
            | Some cont -> StySeq (StyAtom (AtomicAct (AtomNBMsg m)), cont)
            | None -> StyAtom (AtomicAct (AtomNBMsg m))
          in
          let other_branch_heads = List.filteri (fun j _ ->
            j <> i
          )all_msg_branches in
          let other_heads = List.map (fun o_other ->
            match o_other.Lang.trigger with
            | Lang.AtomicAct (Lang.AtomBMsg m) -> m
            | Lang.AtomicAct (Lang.AtomNBMsg m) -> m
            | _ -> failwith "Should not reach here"
          )other_branch_heads in
          let branch_end = build st current in
          let t = List.find (fun t ->
            match LabelSet.elements t.label with
            | [Action m'] when m = m' -> true
            | _ -> false
          ) auto.transitions in
          let t' = {t with label = LabelSet.add (Negation other_heads) t.label} in
          auto.transitions <- List.filter (fun tr -> not (tr = t)) auto.transitions;
          auto.transitions <- t' :: auto.transitions;
          TypeAutomaton.remove_all_transitions auto current current;
          TypeAutomaton.reroute_transitions auto branch_end end_state;
        )all_msg_branches;

        List.iter (fun btype ->
          let branch_end = build btype current in
          TypeAutomaton.remove_all_transitions auto current current;
          TypeAutomaton.reroute_transitions auto branch_end end_state;
        ) other_permuts;



          if all_blocking then (
            let all_msg_specs = List.filter_map (fun b -> 
              match b.Lang.trigger with 
              | Lang.AtomicAct (Lang.AtomBMsg m) | Lang.AtomicAct (Lang.AtomNBMsg m) -> Some m 
              | _ -> None
            ) all_msg_branches in
            TypeAutomaton.add_transition auto current current (LabelSet.singleton (OptionDelay all_msg_specs)) false false false false
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
      TypeAutomaton.add_transition auto current new_pseudo (LabelSet.singleton (Theta (StyAtom (AtomDelay 1)))) false true false false;
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
    let auto1 = build_automaton None st1 default_span in
    let auto2 = build_automaton None st2 default_span in
    
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
          LabelSet.exists (function Delay -> true | OptionDelay _ -> true | _ -> false) t.label in
        
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




        List.iter (fun t1 ->
          let next_ps = get_product_state (t1.to_state, s2) in
          let s2_offers = (Hashtbl.find auto2.states s2).offers in
          let s2_label = LabelSet.singleton (Questionable s2_offers) in
          let combined_label = LabelSet.union t1.label s2_label in
          TypeAutomaton.add_transition auto ps next_ps combined_label t1.is_epsilon t1.is_theta t1.is_recurse t1.is_conditional;
          if not (IntPairSet.mem (t1.to_state, s2) !visited) then 
            worklist := (t1.to_state, s2) :: !worklist
        ) trans1;

        List.iter (fun t2 ->
          let next_ps = get_product_state (s1, t2.to_state) in
          let s1_offers = (Hashtbl.find auto1.states s1).offers in
          let s1_label = LabelSet.singleton (Questionable s1_offers) in
          let combined_label = LabelSet.union t2.label s1_label in
          TypeAutomaton.add_transition auto ps next_ps combined_label t2.is_epsilon t2.is_theta t2.is_recurse t2.is_conditional;
          if not (IntPairSet.mem (s1, t2.to_state) !visited) then 
            worklist := (s1, t2.to_state) :: !worklist
        ) trans2;
        List.iter (fun t1 ->
          List.iter (fun t2 ->
            let label_set = LabelSet.union t1.label t2.label in
            TypeAutomaton.add_transition auto ps (get_product_state (t1.to_state, t2.to_state)) label_set false false false (t1.is_conditional && t2.is_conditional);
            if not (IntPairSet.mem (t1.to_state, t2.to_state) !visited) then 
              worklist := (t1.to_state, t2.to_state) :: !worklist
          ) trans2
        ) trans1;


        if List.length delay_trans1 = 0 && List.length delay_trans2 > 0 then (
          List.iter( fun t ->
            let next_ps = get_product_state (s1, t.to_state) in
            TypeAutomaton.add_transition auto ps next_ps t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
            if not (IntPairSet.mem (s1, t.to_state) !visited) then 
              worklist := (s1, t.to_state) :: !worklist
          )delay_trans2
        )
        else if List.length delay_trans2 = 0 && List.length delay_trans1 > 0 then (
          List.iter( fun t ->
            let next_ps = get_product_state (t.to_state, s2) in
            TypeAutomaton.add_transition auto ps next_ps t.label t.is_epsilon t.is_theta t.is_recurse t.is_conditional;
            if not (IntPairSet.mem (t.to_state, s2) !visited) then 
              worklist := (t.to_state, s2) :: !worklist
          )delay_trans1
        )

        else (
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
      prod_state.offers_in_future <- state1.offers_in_future @ state2.offers_in_future;
      prod_state.is_fair <- state1.is_fair || state2.is_fair;
      prod_state.adversary <- state1.adversary || state2.adversary;

    )state_map;
    final_prod_state
  in
  let final_state = build st auto.start_state in
  (Hashtbl.find auto.states final_state).accepting <- true;
  flush stderr;
  collect_future_messages auto;
  auto