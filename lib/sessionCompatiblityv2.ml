
open Lang

type message_or_delay = 
| Msg of message_specifier
| Delay of int 
| End



module MessageOrDelay = struct
    type t = message_or_delay

    let _equal = fun a b ->
        match (a, b) with
        | (Msg m1, Msg m2) -> m1 = m2
        | (Delay d1, Delay d2) -> d1 = d2
        | _ -> false

    let compare = fun a b ->
        match (a, b) with
        | (Msg m1, Msg m2) -> Stdlib.compare m1 m2
        | (Delay d1, Delay d2) -> Stdlib.compare d1 d2
        | (Msg _, Delay _) -> -1
        | (Delay _, Msg _) -> 1
        | (_, End) -> -1
        | (End, _) -> 1
    let empty = End
    
end

module ActionSet = Set.Make(MessageOrDelay)
(* special union function delay and some message is equivalent to message ignores delay*)
let special_union (set1 : ActionSet.t) (set2 : ActionSet.t) : ActionSet.t =
    let has_msg = 
        ActionSet.exists (function
            | Msg _ -> true
            | _ -> false
        ) set1 || ActionSet.exists (function
            | Msg _ -> true
            | _ -> false
        ) set2
    in
    if has_msg then
        ActionSet.filter (function
            | Delay _ -> false
            | _ -> true
        ) (ActionSet.union set1 set2)
    else
        ActionSet.union set1 set2

type act_continuation_map = {
    acts : ActionSet.t;  (* Now a set of actions *)
    cont : session_type
}

module RGSet = Set.Make(struct
    type t = act_continuation_map

    let _equal = fun a b ->
        ActionSet.equal a.acts b.acts && a.cont = b.cont

    let compare = fun a b ->
        let c1 = ActionSet.compare a.acts b.acts in
        if c1 <> 0 then c1
        else Stdlib.compare a.cont b.cont

end)

module RGCollections = Set.Make(struct
    type t = RGSet.t
    let compare = fun a b ->
        RGSet.compare a b
end)

let find_subset_acts (se1 : RGSet.t) (se2 : RGSet.t) : bool =
    RGSet.for_all (fun acm1 ->
        RGSet.exists (fun acm2 ->
            ActionSet.equal acm1.acts acm2.acts
        ) se2
    ) se1


let find_subset (se1 : RGSet.t) (collection : RGCollections.t) : RGSet.t option =
  RGCollections.elements collection
  |> List.find_opt (fun se2 -> find_subset_acts se1 se2)

let find_act (acm1 : act_continuation_map) (rgset2 : RGSet.t) : act_continuation_map option =
    RGSet.elements rgset2
    |> List.find_opt (fun acm2 ->
        ActionSet.equal acm1.acts acm2.acts
    )



let setProduct (set1 : RGCollections.t) (set2 : RGCollections.t) : RGCollections.t =
  (* for each element(Set) of collection we do a union of sets (unions of sets)  *)
  RGCollections.fold (fun rgset1 acc ->
    RGCollections.fold (fun rgset2 acc' ->
      let union_set = RGSet.union rgset1 rgset2 in
      RGCollections.add union_set acc'
    ) set2 acc
  ) set1 RGCollections.empty


let doubleProduct(set1 : RGCollections.t) (set2 : RGCollections.t) : RGCollections.t =
(* for each element(Set ) of collection we pick another set and do product of two sets (union of actions) *)
  RGCollections.fold (fun rgset1 acc ->
    RGCollections.fold (fun rgset2 acc' ->
        (* rgSet1 = rGSET 2 EXACTLY THEN dont do anything *)
        if RGSet.equal rgset1 rgset2 then
          acc'
        else
      (* Compute the cartesian product of the two RGSets *)
      let product_set = RGSet.fold (fun acm1 inner_acc ->
        RGSet.fold (fun acm2 inner_acc' ->
          (* Combine the actions from both act_continuation_maps *)
          let combined_acts = special_union acm1.acts acm2.acts in
          let cont' = match (acm1.cont, acm2.cont) with
            | (StyTrue, _) -> acm2.cont
            | (_, StyTrue) -> acm1.cont
            | _ -> StyParallel (acm1.cont, acm2.cont) in
          let combined_acm = {acts = combined_acts; cont = cont'} in
          RGSet.add combined_acm inner_acc'
        ) rgset2 inner_acc
      ) rgset1 RGSet.empty in
      RGCollections.add product_set acc'
    ) set2 acc
  ) set1 RGCollections.empty

let createParallelPermutations (sets : RGSet.t list) : RGSet.t list =
    let rec combine acc = function
        | [] -> acc
        | rgset :: rest ->
                let new_acc =
                    List.flatten (
                        List.map (fun existing_rgset ->
                            RGSet.fold (fun acm1 acc' ->
                                RGSet.fold (fun acm2 acc'' ->
                                    let combined_acts = ActionSet.union acm1.acts acm2.acts in
                                    let combined_acm = {acts = combined_acts; cont = StyParallel (acm1.cont, acm2.cont)} in
                                    RGSet.add combined_acm acc''
                                ) rgset acc'
                            ) existing_rgset RGSet.empty :: []
                        ) acc
                    )
                in
                combine new_acc rest
    in
    match sets with
    | [] -> []
    | hd :: tl -> combine [hd] tl

let string_of_actionset (aset : ActionSet.t) : string =
    let elements = ActionSet.elements aset in
    let element_strings = List.map (function
        | Msg m -> "Msg(" ^ string_of_msg_spec m ^ ")"
        | Delay d -> "Delay(" ^ string_of_int d ^ ")"
        | End -> "End"
    ) elements in
    "<" ^ (String.concat ", " element_strings) ^ ">"
let string_of_acm (acm : act_continuation_map) : string =
    let acts_str = string_of_actionset acm.acts in
    let cont_str = ":" ^ string_of_protocol acm.cont in
    "Acts: " ^ acts_str ^ ", Cont: " ^ cont_str

let string_of_rgset (rgset : RGSet.t) : string =
    let elements = RGSet.elements rgset in
    let element_strings = List.map string_of_acm elements in
    "[ " ^ (String.concat " | " element_strings) ^ " ]"
let string_of_rgcollections (rgcoll : RGCollections.t) : string =
    let elements = RGCollections.elements rgcoll in
    let element_strings = List.map string_of_rgset elements in
    "Collection: {\n " ^ (String.concat " ,\n " element_strings) ^ " \n}"


let rec constructReliabilityCollection (sty : session_type) : RGCollections.t =

  match sty with
  | StyTrue -> 
      RGCollections.empty
  | StyAtom (AtomicAct AtomBMsg m) ->
      RGCollections.union (RGCollections.singleton(RGSet.singleton {acts = ActionSet.singleton (Msg m); cont = StyTrue})) (RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty}))
  | StyAtom (AtomicAct (AtomNBMsg m)) ->
      RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Msg m); cont = StyTrue})
  | StyAtom (AtomDelay d) when d > 1 ->
        RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = StyAtom (AtomDelay (d - 1))})
  | StyAtom (AtomDelay 1) ->
        RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = StyTrue})
  | StySeq (sty1, sty2) ->
      let rgSet1 = constructReliabilityCollection sty1 in
      (* the action set is regset1 the continuation is for all elelment of the set we create sequence of the type *)
      RGCollections.fold (fun rgset acc ->
          RGSet.fold (fun acm acc' ->
            let new_cont =match acm.cont with
            | StyTrue -> sty2
            | _ -> StySeq (acm.cont, sty2)
          in
              let new_acm = RGSet.singleton {acts = acm.acts; cont = new_cont} in
              RGCollections.add new_acm acc'
          ) rgset acc
      ) rgSet1 RGCollections.empty 
  | StyParallel (sty1, sty2) ->
        let rgSet1 = constructReliabilityCollection sty1 in
        let rgSet2 = constructReliabilityCollection sty2 in
        doubleProduct rgSet1 rgSet2
  | StyChoice (sty1, sty2) ->
        let rgSet1 = constructReliabilityCollection sty1 in
        let rgSet2 = constructReliabilityCollection sty2 in
        setProduct rgSet1 rgSet2
  | StyOffer ps ->
    (*trigger continuation list give back as RgSets*)
   let rgSets = List.map (fun oty ->
    match oty.trigger with
    | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomDelay _ -> RGSet.singleton {acts = ActionSet.empty; cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    ) ps in
    let all_blocking = List.for_all (fun oty ->
      match oty.trigger with
      | AtomicAct (AtomBMsg _) -> true
      | _ -> false
    ) ps in
        
    let parallelPerm = createParallelPermutations rgSets in
    let new_set = if (not all_blocking) then rgSets@parallelPerm else rgSets@parallelPerm@[(RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty})] in
    List.fold_left (fun acc rgset ->
        RGCollections.add rgset acc
    ) RGCollections.empty new_set
      
  | StyXOffer ps ->
    (*trigger continuation list give back as RgSets*)
   let rgSets = List.map (fun oty ->
    match oty.trigger with
    | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomDelay _ -> RGSet.singleton {acts = ActionSet.empty; cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    ) ps in
    let all_blocking = List.for_all (fun oty ->
      match oty.trigger with
      | AtomicAct (AtomBMsg _) -> true
      | _ -> false
     ) ps in 
    if all_blocking then
      let new_set = rgSets@[(RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty})] in
      RGCollections.singleton (List.fold_left RGSet.union RGSet.empty new_set)
    else
    let rgCollections = RGCollections.of_list rgSets in
    rgCollections
  | StyFuture ps ->
    (*trigger continuation list give back as RgSets*)
    let futureCollection = RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = ps}) in
    let rgCollection = constructReliabilityCollection ps in
    setProduct futureCollection rgCollection
  | _ -> RGCollections.empty


let rec constructGuaranteeCollection (sty : session_type) : RGCollections.t =
    match sty with
    | StyTrue -> 
        RGCollections.empty
    | StyAtom (AtomicAct AtomNBMsg m) ->
        RGCollections.singleton(RGSet.singleton {acts = ActionSet.singleton (Msg m); cont = StyTrue})
    | StyAtom (AtomicAct (AtomBMsg m)) ->
        RGCollections.singleton(RGSet.union (RGSet.singleton {acts = ActionSet.singleton (Msg m); cont = StyTrue}) (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty}))
    | StyAtom (AtomDelay d) when d > 1 ->
          RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = StyAtom (AtomDelay (d - 1))})
    | StyAtom (AtomDelay 1) ->
          RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = StyTrue})
    | StySeq (sty1, sty2) ->
        let rgSet1 = constructGuaranteeCollection sty1 in
        (* the action set is regset1 the continuation is for all elelment of the set we create sequence of the type *)
        RGCollections.fold (fun rgset acc ->
            RGSet.fold (fun acm acc' ->
              let new_cont =match acm.cont with
              | StyTrue -> sty2
              | _ -> StySeq (acm.cont, sty2)
            in
                let new_acm = RGSet.singleton {acts = acm.acts; cont = new_cont} in
                RGCollections.add new_acm acc'
            ) rgset acc
        ) rgSet1 RGCollections.empty 
    | StyParallel (sty1, sty2) ->
        (*same as rely set  *)
            let rgSet1 = constructGuaranteeCollection sty1 in
            let rgSet2 = constructGuaranteeCollection sty2 in
            doubleProduct rgSet1 rgSet2
    | StyChoice (sty1, sty2) ->
            let rgSet1 = constructGuaranteeCollection sty1 in
            let rgSet2 = constructGuaranteeCollection sty2 in
            RGCollections.union rgSet1 rgSet2
    | StyOffer ps ->
      (*trigger continuation list give back as RgSets*)
      let rgSets = List.map (fun oty ->
        match oty.trigger with
        | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
        | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
        | AtomDelay _ -> RGSet.singleton {acts = ActionSet.empty; cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
      ) ps in
      let parallelPerm = createParallelPermutations rgSets in
      let all_blocking = List.for_all (fun oty ->
        match oty.trigger with
        | AtomicAct (AtomBMsg _) -> true
        | _ -> false
        ) ps in
      let new_set =  if (not all_blocking) then rgSets@parallelPerm else rgSets@parallelPerm@[(RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty})] in
     RGCollections.singleton (List.fold_left RGSet.union RGSet.empty new_set)
    | StyXOffer ps ->
        (*trigger continuation list give back as RgSets*)
         let rgSets = List.map (fun oty ->
            match oty.trigger with
            | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
            | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
            | AtomDelay _ -> RGSet.singleton {acts = ActionSet.empty; cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
        ) ps in
        let all_blocking = List.for_all (fun oty ->
          match oty.trigger with
          | AtomicAct (AtomBMsg _) -> true
          | _ -> false
         ) ps in
        if all_blocking then
          let new_set = rgSets@[(RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty})] in
          RGCollections.singleton (List.fold_left RGSet.union RGSet.empty new_set)
        else
          let rgCollections = RGCollections.of_list rgSets in
          rgCollections
    | StyFuture ps ->
        let futureCollection = RGCollections.singleton (RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = ps}) in
        let rgCollection = constructGuaranteeCollection ps in
        RGCollections.union futureCollection rgCollection
     | _ -> RGCollections.empty

let match_obligations check_fn rc1 gc2 span_1  span_2 =
    RGCollections.exists (fun rgset1 ->
          match find_subset rgset1 gc2 with
          | Some rgset2 ->
              RGSet.for_all (fun acm1 ->
                match find_act acm1 rgset2 with
                | Some acm2_req ->
                    check_fn {d = acm1.cont ; span = span_1} {d = acm2_req.cont ; span = span_2}
                | None -> raise (Failure "Should not happen")
              ) rgset1
          | None -> false
    ) rc1

let compatiblity_check_binary (sty1_ast : session_type ast_node) (sty2_ast : session_type ast_node) : bool =
    (* Memoization table to detect cycles and cache results *)
    let visited = Hashtbl.create 16 in
    
    let rec check_with_memo (sty1_ast : session_type ast_node) (sty2_ast : session_type ast_node) : bool =
        let key = (sty1_ast.d, sty2_ast.d) in
        
        (* Check if we've already seen this pair (cycle detection) *)
        match Hashtbl.find_opt visited key with
        | Some result -> result
        | None ->
            (* Assume true initially for cycles, then verify *)
            Hashtbl.add visited key true;
            
            let sty1 = sty1_ast.d in
            let sty2 = sty2_ast.d in
            let result = match sty1, sty2 with
            | StyTrue, StyTrue -> true
            | _, StyTrue -> false
            | StyTrue, _ -> false
            | StyAtom (AtomDelay d1), StyAtom (AtomDelay d2) ->
                d1 = d2
            | StyAtom (AtomDelay _d1), StyAtom (AtomicAct _) ->
                false
            | StyAtom (AtomicAct _), StyAtom (AtomDelay _d2) ->
                false
            | StyAtom (AtomicAct AtomNBMsg m1), StyAtom (AtomicAct AtomNBMsg m2) ->
                m1 = m2
            | StyAtom (AtomicAct (AtomBMsg m1)), StyAtom (AtomicAct (AtomBMsg m2)) ->
                m1 = m2
            | StyAtom (AtomicAct AtomNBMsg m1), StyAtom (AtomicAct (AtomBMsg m2)) ->
                m1 = m2
            | StyAtom (AtomicAct (AtomBMsg m1)), StyAtom (AtomicAct AtomNBMsg m2) ->
                m1 = m2
            | _ ->
                let obligations_1 = match_obligations check_with_memo (constructReliabilityCollection sty1) (constructGuaranteeCollection sty2) sty1_ast.span sty2_ast.span in
                  if obligations_1 then
                    (
                    Printf.eprintf "Type 1: obligations matched for %s by %s\n\n" (string_of_protocol sty1) (string_of_protocol sty2);
                    let obligations2 = match_obligations check_with_memo (constructReliabilityCollection sty2) (constructGuaranteeCollection sty1) sty2_ast.span sty1_ast.span in
                      if obligations2 then ( Printf.eprintf "Type 2: obligations matched for %s by %s\n\n" (string_of_protocol sty2) (string_of_protocol sty1); true) else false
                      )
                  else false
            in
            Hashtbl.replace visited key result;
            result
    in
    check_with_memo sty1_ast sty2_ast
    