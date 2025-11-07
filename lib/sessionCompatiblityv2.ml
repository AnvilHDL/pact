
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

type act_continuation_map = {
    acts : ActionSet.t;  (* Now a set of actions *)
    cont : session_type
}

module RGSet = Set.Make(struct
    type t = act_continuation_map

    let _equal = fun a b ->
        ActionSet.equal a.acts b.acts && a.cont = b.cont

    let compare = fun a b ->
        ActionSet.compare a.acts b.acts

    
end)

module RGCollections = Set.Make(struct
    type t = RGSet.t
    let compare = fun a b ->
        RGSet.compare a b
end)






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
          let combined_acts = ActionSet.union acm1.acts acm2.acts in
          let combined_acm = {acts = combined_acts; cont = StyParallel (acm1.cont, acm2.cont)} in
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


let rec constructReliabilitySet (sty : session_type) : RGCollections.t =

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
      let rgSet1 = constructReliabilitySet sty1 in
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
        let rgSet1 = constructReliabilitySet sty1 in
        let rgSet2 = constructReliabilitySet sty2 in
        doubleProduct rgSet1 rgSet2
  | StyChoice (sty1, sty2) ->
        let rgSet1 = constructReliabilitySet sty1 in
        let rgSet2 = constructReliabilitySet sty2 in
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
    let rgCollection = constructReliabilitySet ps in
    setProduct futureCollection rgCollection
  | _ -> RGCollections.empty


let rec constructGuaranteeSet (sty : session_type) : RGCollections.t =
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
        let rgSet1 = constructGuaranteeSet sty1 in
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
            let rgSet1 = constructGuaranteeSet sty1 in
            let rgSet2 = constructGuaranteeSet sty2 in
            doubleProduct rgSet1 rgSet2
    | StyChoice (sty1, sty2) ->
            let rgSet1 = constructGuaranteeSet sty1 in
            let rgSet2 = constructGuaranteeSet sty2 in
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
        let rgCollection = constructGuaranteeSet ps in
        RGCollections.union futureCollection rgCollection
     | _ -> RGCollections.empty
    

    