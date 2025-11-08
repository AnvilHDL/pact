
open Lang

(* Helper function to find index of element in list *)
let rec find_index_helper pred lst idx =
    match lst with
    | [] -> None
    | x :: xs -> if pred x then Some idx else find_index_helper pred xs (idx + 1)

let find_index pred lst = find_index_helper pred lst 0

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
            ActionSet.equal acm1.acts acm2.acts || acm1.acts = ActionSet.empty
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
    let ps_filtered = List.filter (fun oty ->
      match oty.trigger with
      | AtomDelay _ -> false
      | _ -> true
    ) ps in
    let wildcard_arm = List.find_opt (fun oty ->
      match oty.trigger with
      | AtomDelay _ -> true
      | _ -> false
    ) ps in
   let rgSets = List.map (fun oty ->
    match oty.trigger with
    | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomDelay _ -> raise (Failure "Should not happen (in offer construction)")
    ) ps_filtered in

    let (wildcard_collection : RGCollections.t option) = if Option.is_some wildcard_arm then 
            let oty = Option.get wildcard_arm in
            if oty.continuation = None then
            None
            else
            Some (constructReliabilityCollection (Option.get oty.continuation) )
        else
          None
    in
        
    let all_blocking = List.for_all (fun oty ->
      match oty.trigger with
      | AtomicAct (AtomBMsg _) -> true
      | _ -> false
    ) ps in
        
    let parallelPerm = createParallelPermutations rgSets in
    let new_set = if (not all_blocking) then rgSets@parallelPerm else rgSets@parallelPerm@[(RGSet.singleton {acts = ActionSet.singleton (Delay 1); cont = sty})] in
    let origRC = List.fold_left (fun acc rgset ->
        RGCollections.add rgset acc
    ) RGCollections.empty new_set
    in
    (
    match wildcard_collection with
    | Some wc_coll -> RGCollections.union origRC wc_coll
    | None -> origRC
      )
  | StyXOffer ps ->
    (*trigger continuation list give back as RgSets*)
    let ps_filtered = List.filter (fun oty ->
      match oty.trigger with
      | AtomDelay _ -> false
      | _ -> true
    ) ps in
    let wildcard_arm = List.find_opt (fun oty ->
      match oty.trigger with
      | AtomDelay _ -> true
      | _ -> false
    ) ps in
   let rgSets = List.map (fun oty ->
    match oty.trigger with
    | AtomicAct AtomNBMsg label-> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomicAct (AtomBMsg label) -> RGSet.singleton {acts = ActionSet.singleton (Msg label); cont = if Option.is_some oty.continuation then Option.get oty.continuation else StyTrue}
    | AtomDelay _ -> raise (Failure "Should not happen (in xoffer construction)")
    ) ps_filtered in
    let wildcardCollection = match wildcard_arm with
    | Some oty ->
        if oty.continuation = None then None
        else Some (constructReliabilityCollection (Option.get oty.continuation))
    | None -> None
    in 
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
    (
        match wildcardCollection with
        | Some wc_coll -> RGCollections.union rgCollections wc_coll
        | None -> rgCollections
    )
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
            Hashtbl.add visited key false;
            
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
                let rc1 = constructReliabilityCollection sty1 in
                let gc2 = constructGuaranteeCollection sty2 in
                let obligations_1 = match_obligations check_with_memo rc1 gc2 sty1_ast.span sty2_ast.span in
                  if obligations_1 then
                    (
                        let rc2 = constructReliabilityCollection sty2 in
                        let gc1 = constructGuaranteeCollection sty1 in
                    Printf.eprintf "Type 1: obligations matched for %s by %s\n\n" (string_of_protocol sty1) (string_of_protocol sty2);
                    let obligations2 = match_obligations check_with_memo rc2 gc1 sty2_ast.span sty1_ast.span in
                      if obligations2 then ( Printf.eprintf "Type 2: obligations matched for %s by %s\n\n" (string_of_protocol sty2) (string_of_protocol sty1); true) else false
                      )
                  else false
            in
            Hashtbl.replace visited key result;
            result
    in
    check_with_memo sty1_ast sty2_ast

let create_ep_id_intfc_id_map (pool_def_o : interface_pool_def ast_node) : identifier list Utils.string_map =
            (* First, build a map from right endpoints to their corresponding left endpoints *)
            let right_to_left_map = List.fold_left (fun map (chan : Lang.channel_def ast_node) ->
              Utils.StringMap.add chan.d.endpoint_right chan.d.endpoint_left map
            ) Utils.StringMap.empty pool_def_o.d.pool_channels in
            
            (* For each left endpoint, collect all interface IDs that use it *)
            let all_left_endpoints = List.map (fun (chan : Lang.channel_def ast_node) -> chan.d.endpoint_left) pool_def_o.d.pool_channels in
            let intfc_ids = List.map (fun (intf_member : interface_mem_def ast_node) -> intf_member.d.inf_mem_id) pool_def_o.d.interface_members in
            List.fold_left (fun map left_ep ->
              (* Find all interfaces that use this left endpoint (either directly or via its right endpoint) *)
              let interface_ids = List.fold_left2 (fun acc intf_id interface_member ->
                match interface_member.d.interface_class_id with
                | Some intf_inst ->
                    (* Check if this interface uses the left endpoint directly OR uses its paired right endpoint *)
                    let uses_this_endpoint = List.exists (fun actual_ep ->
                      actual_ep = left_ep || 
                      (match Utils.StringMap.find_opt actual_ep right_to_left_map with
                       | Some mapped_left -> mapped_left = left_ep
                       | None -> false)
                    ) intf_inst.params in
                    if uses_this_endpoint then intf_id :: acc else acc
                | None -> acc
              ) []  intfc_ids pool_def_o.d.interface_members in
              
              if interface_ids <> [] then
                Utils.StringMap.add left_ep (List.rev interface_ids) map
              else
                map
            ) Utils.StringMap.empty all_left_endpoints



let product_acts (gc_list : RGCollections.t list) =
    (* for each element in the collection,do a product on actions only *)
    let gc_list_projected_to_acts = List.map (fun rgcoll ->
        RGCollections.map (fun rgset ->
            RGSet.map (fun acm ->
                {acts = acm.acts; cont = StyTrue}
            ) rgset
        ) rgcoll
    ) gc_list in

    let rec fold_product acc = function
        | [] -> acc
        | rgcoll :: rest ->
            let new_acc = doubleProduct acc rgcoll in
            fold_product new_acc rest
    in
    fold_product (List.hd gc_list_projected_to_acts) (List.tl gc_list_projected_to_acts) 

let union_product_acts (gc_list : RGCollections.t list) =
    (* for each element in the collection,do a union on actions sets only not merge actions *)
    let gc_list_projected_to_acts = List.map (fun rgcoll ->
        RGCollections.map (fun rgset ->
            RGSet.map (fun acm ->
                {acts = acm.acts; cont = StyTrue}
            ) rgset
        ) rgcoll
    ) gc_list in
    let rec fold_union acc = function
        | [] -> acc
        | rgcoll :: rest ->
            let new_acc = setProduct acc rgcoll in
            fold_union new_acc rest
    in
    fold_union (List.hd gc_list_projected_to_acts) (List.tl gc_list_projected_to_acts)
    



let compatiblity_check_multiparty (session_ids: (((session_type ast_node)*identifier) list)) (_ep_intfc_map : identifier list Utils.string_map) (verbose : bool) (_span : code_span) =
    (* Memoization table to detect cycles and cache results *)
    let visited = Hashtbl.create 16 in

    (* Helper function that tracks both current and original types *)
    let rec check_multiparty_with_memo_internal (session_data: (((session_type ast_node)*identifier*(session_type ast_node)) list)) : (bool * string) =
        let session_ids = List.map (fun (sty_ast, id, _) -> (sty_ast, id)) session_data in
        let key = List.map (fun (sty_ast, id) -> (sty_ast.d, id)) session_ids in

        match Hashtbl.find_opt visited key with
        | Some result -> 
            if verbose then
                Printf.eprintf "[Info] Found cached result for session types (returning %s)\n" 
                    (if fst result then "COMPATIBLE" else "INCOMPATIBLE");
            result
        | None ->
            if verbose then begin
                Printf.eprintf "\n========================================\n";
                Printf.eprintf "[Info] Starting multiparty check for %d processes:\n" (List.length session_ids);
                List.iteri (fun i (sty_ast, id) ->
                    Printf.eprintf "  [%d] %s: %s\n" i id (string_of_protocol sty_ast.d)
                ) session_ids;
                Printf.eprintf "========================================\n";
            end;
            Hashtbl.add visited key (true, "Assumed true for cycle detection");

            let sty_list = List.map (fun (sty_ast, _, _) -> sty_ast.d) session_data in
            let result = match sty_list with
            | [] -> 
                if verbose then Printf.eprintf "[BASE CASE] Empty list - all processes completed\n";
                (true, "Single or no session, trivially compatible")
            | [p] -> 
                if verbose then Printf.eprintf "[BASE CASE] Single process - trivially compatible\n";
                if p = StyTrue then
                    (true, "Single process completed")
                else
                (false, "Single type remaining and not completed, incompatible")
            | [_; _] ->
                if verbose then Printf.eprintf "[Info] Two processes - using binary compatibility check\n";
                let res = compatiblity_check_binary (List.nth session_ids 0 |> fst) (List.nth session_ids 1 |> fst) in
                if verbose then Printf.eprintf "[RESULT] %s\n" (if res then "COMPATIBLE" else "INCOMPATIBLE");
                if res then (true, "Binary compatibility succeeded")
                else (false, "Binary compatibility failed")
            | _ ->
                if verbose then Printf.eprintf "[MULTIPARTY] Checking %d processes\n" (List.length sty_list);
                
                let sty_list_filtered = List.filter (fun sty -> 
                        match sty with
                        | StyTrue -> true
                        | StyAtom _-> true
                        | _ -> false
                    ) sty_list in
                
                if verbose then Printf.eprintf "[Info] Found %d simple types (StyTrue or StyAtom) to pre-match\n" (List.length sty_list_filtered);
                
                (* now for this list check if we have some matched types, checking two at a time , filter them out*)                
                let sty_list_satisfied = ref [] in
                let rec helper remaining_stys =
                    match remaining_stys with
                    | [] -> ()
                    | sty1 :: rest ->
                        match sty1 with
                        | StyTrue -> sty_list_satisfied := sty1 :: !sty_list_satisfied;helper rest
                        | StyAtom AtomDelay _ -> sty_list_satisfied := sty1 :: !sty_list_satisfied;helper rest
                        | _ -> helper rest;
                        let matched = ref false in
                        let rec try_match sty_list_to_try =
                            match sty_list_to_try with
                            | [] -> ()
                            | sty2 :: rest2 ->
                                match sty1, sty2 with
                                | StyTrue, StyTrue -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | StyAtom (AtomDelay d1), StyAtom (AtomDelay d2) when d1 = d2 -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | StyAtom (AtomicAct AtomNBMsg m1), StyAtom (AtomicAct AtomNBMsg m2) when m1 = m2 -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | StyAtom (AtomicAct (AtomBMsg m1)), StyAtom (AtomicAct (AtomBMsg m2)) when m1 = m2 -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | StyAtom (AtomicAct AtomNBMsg m1), StyAtom (AtomicAct (AtomBMsg m2)) when m1 = m2 -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | StyAtom (AtomicAct (AtomBMsg m1)), StyAtom (AtomicAct AtomNBMsg m2) when m1 = m2 -> sty_list_satisfied := sty1 :: sty2 :: !sty_list_satisfied; matched := true
                                | _ -> try_match rest2
                        in
                        try_match rest;
                        if !matched then
                            let rest_filtered = List.filter (fun sty -> not (List.mem sty !sty_list_satisfied)) rest in
                            helper rest_filtered
                        else
                            helper rest
                in
                helper sty_list_filtered;
                let remaining_data = List.filter (fun (curr_sty, _, _orig_ast) -> not (List.mem curr_sty.d !sty_list_satisfied)) session_data in
                let remaining_stys = List.map (fun (sty_ast, _, _) -> sty_ast.d) remaining_data in
                
                if verbose then begin
                    Printf.eprintf "[Info] %d processes after simple matching:\n" (List.length remaining_stys);
                    List.iteri (fun i sty ->
                        Printf.eprintf "  [%d] %s\n" i (string_of_protocol sty)
                    ) remaining_stys;
                end;
                
                if remaining_stys = [] then
                    (true, "All session types satisfied")
                else if List.length remaining_stys = 1 then begin
                    if verbose then Printf.eprintf "[Info] Only one process left, Incompatible\n";
                    (false, "Only one session type remaining, cannot satisfy multiparty compatibility")
                end
                else begin
                    if verbose then Printf.eprintf "\n[Info] Performing full multiparty compatibility check on %d processes\n" (List.length remaining_stys);
                    
                    (* For each session type, check if its reliability can be satisfied by 
                       the product of guarantees from all other processes (using ORIGINAL types for guarantees) *)
                    let all_compatible = List.for_all (fun (current_ast, current_id, orig_ast) ->
                        let sty = current_ast.d in
                        if verbose then Printf.eprintf "\n--- Checking type: %s ---\n" (string_of_protocol sty);
                        
                        let rc_sty = constructReliabilityCollection sty in
                        
                        (* If reliability collection is empty, this type is StyTrue - automatically compatible *)
                        if RGCollections.is_empty rc_sty then begin
                            if verbose then Printf.eprintf "[SKIP] Process has empty reliability - compatible\n";
                            true
                        end
                        else begin
                            let other_data = List.filter (fun (other_ast, _, _) -> other_ast.d <> sty) remaining_data in
                            let gc_list = List.map (fun (current_other_ast, _, orig_other_ast) ->
                                (* If the current type is StyTrue, use the original type's guarantees *)
                                match current_other_ast.d with
                                | StyTrue -> constructGuaranteeCollection orig_other_ast.d
                                | _ -> constructGuaranteeCollection current_other_ast.d
                            ) other_data in
                            let parallel_gc_list = product_acts gc_list in
                            let union_acts = union_product_acts gc_list in
                            let prod_gc_others = RGCollections.union parallel_gc_list union_acts in
                            
                            if verbose then begin
                                Printf.eprintf "[INFO] %d other processes providing guarantees\n" (List.length other_data);
                                Printf.eprintf "\nReliability collection:\n%s\n" (string_of_rgcollections rc_sty);
                                Printf.eprintf "Product of other guarantees:\n%s\n" (string_of_rgcollections prod_gc_others);
                            end;
                            
                            (* Check if there exists at least one reliability set that leads to completion *)
                            let found_path = RGCollections.exists (fun rgset_rely ->
                                if verbose then Printf.eprintf "\n[Info] Trying reliability set: %s\n" (string_of_rgset rgset_rely);
                                
                                match find_subset rgset_rely prod_gc_others with
                                | None -> 
                                    if verbose then
                                        Printf.eprintf "[FAILED] Could not satisfy reliability requirement\n";
                                    false
                                | Some rgset_guarantee ->
                                    if verbose then
                                        Printf.eprintf "[MATCHED] Reliability requirement satisfied by guarantee set: %s\n" (string_of_rgset rgset_guarantee);
                                    

                                    let all_actions_ok = RGSet.for_all (fun acm_rely ->
                                        match find_act acm_rely rgset_guarantee with
                                        | None -> 
                                            if verbose then
                                                raise (Failure (Printf.sprintf "[ERROR] Action %s not found in guarantee set, should not happen\n" (string_of_actionset acm_rely.acts)));
                                            false
                                        | Some _ ->
                                            let other_data_with_idx = List.mapi (fun idx data -> (idx, data)) other_data in
                                            

                                            let all_continuations = List.filter_map (fun (idx, (current_other_ast, id_other, orig_other_ast)) ->
                                                let gc_other = List.nth gc_list idx in
                                                let found = RGCollections.fold (fun rgset acc_opt ->
                                                    match acc_opt with
                                                    | Some _ -> acc_opt
                                                    | None ->
                                                        match find_act acm_rely rgset with
                                                        | Some acm -> Some ({d = acm.cont; span = code_span_dummy}, id_other, orig_other_ast)
                                                        | None -> None
                                                ) gc_other None in
                                                match found with
                                                | Some cont_data -> Some cont_data
                                                | None -> Some ({d = current_other_ast.d; span = code_span_dummy}, id_other, orig_other_ast)
                                            ) other_data_with_idx in
                                            

                                            let all_cont_data = ({d = acm_rely.cont; span = code_span_dummy}, current_id, orig_ast) :: all_continuations in

                                            let active_cont_data = List.map (fun (cont, id, orig) -> if cont.d = StyTrue then (orig,id,orig) else (cont,id,orig)) all_cont_data in

                                            if verbose then begin
                                                Printf.eprintf "[ACTION] %s: checking %d continuations (filtered %d StyTrue)\n"
                                                    (string_of_actionset acm_rely.acts)
                                                    (List.length active_cont_data)
                                                    (List.length all_cont_data - List.length active_cont_data);
                                                if List.length active_cont_data > 0 then
                                                    List.iteri (fun i (cont, _, _) ->
                                                        Printf.eprintf "    [%d] %s\n" i (string_of_protocol cont.d)
                                                    ) active_cont_data;
                                            end;
                                            
                                            (* Only recurse if there are active continuations *)
                                            if List.length active_cont_data = 0 then begin
                                                if verbose then Printf.eprintf "[ALL COMPLETE] All processes reached StyTrue\n";
                                                true
                                            end else begin
                                                (* Recursively check multiparty compatibility of continuations *)
                                                let (compatible, msg) = check_multiparty_with_memo_internal active_cont_data in
                                                if not compatible && verbose then
                                                    Printf.eprintf "[RECURSIVE FAIL] Continuations not compatible: %s\n" msg;
                                                if compatible && verbose then
                                                    Printf.eprintf "[RECURSIVE OK] Continuations are compatible\n";
                                                compatible
                                            end
                                    ) rgset_rely in
                                    
                                    if all_actions_ok && verbose then
                                        Printf.eprintf "[SUCCESS] All actions in reliability set can be satisfied\n";
                                    all_actions_ok
                            ) rc_sty in
                            
                            if not found_path && verbose then
                                Printf.eprintf "[FAIL] No compatible path found for this process\n";
                            if found_path && verbose then
                                Printf.eprintf "[OK] Process has at least one compatible path\n";
                            found_path
                        end
                    ) remaining_data in
                    
                    if all_compatible then begin
                        if verbose then Printf.eprintf "\n[RESULT] MULTIPARTY COMPATIBLE - All processes can complete\n";
                        (true, "Multiparty compatibility check passed")
                    end
                    else begin
                        if verbose then Printf.eprintf "\n[RESULT] MULTIPARTY INCOMPATIBLE - At least one process cannot complete\n";
                        (false, "Multiparty compatibility check failed")
                    end
                end
            in
            Hashtbl.replace visited key result;
            result
    in

    let session_data_initial = List.map (fun (sty_ast, id) -> (sty_ast, id, sty_ast)) session_ids in
    check_multiparty_with_memo_internal session_data_initial
    

let check_compatibility_multiparty (pool_def : interface_pool_def ast_node) (verbose : bool) : (bool * string) =
        let ep_intfc_map = create_ep_id_intfc_id_map pool_def in
        let session_ids = List.filter_map (fun intf_member ->
            match intf_member.d.interface_def with
            | Some intf_in -> Some ({d = intf_in; span = intf_member.span}, intf_member.d.inf_mem_id)
            | None -> raise (Failure "Interface member missing definition")
        ) pool_def.d.interface_members in
        compatiblity_check_multiparty session_ids ep_intfc_map verbose pool_def.span