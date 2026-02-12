open Lang
open EventGraph

(* TODO: to use arrays instead of hash tables *)

let event_traverse (ev : event) visitor : event list =
  let visited = Seq.return ev.id |> Utils.IntSet.of_seq |> ref in
  let q = Seq.return ev |> Queue.of_seq in
  let res = ref [] in
  let add_to_queue ev' =
    if Utils.IntSet.mem ev'.id !visited |> not then (
      visited := Utils.IntSet.add ev'.id !visited;
      Queue.add ev' q
    )
    else ()
  in
  while Queue.is_empty q |> not do
    let cur = Queue.pop q in
    res := cur::!res;
    visitor add_to_queue cur
  done;
  !res

(* returns immediate predecessors *)
let imm_preds ev =
  let rec get_pred src =
  match src with
  | `Seq (e', _)
  | `Root (Some (e', _)) -> [e']
  | `Branch (_, {branches_val; _}) -> branches_val
  | `Later (e1, e2) -> [e1; e2]
  | `Root None -> []
  | `UntilEntry (e', _info) -> [e']
  | `UntilExit info -> [info.until_stop_cond]
  | `Recurse (src, id) -> get_pred src@[List.find (fun e -> e.id = id) ev.graph.events]
  in
  get_pred ev.source

let toposort_with_preds preds events =
  let n = List.fold_left (fun l e -> Int.max l e.id) 0 events in
  let n = n + 1 in
  let in_subgraph = Array.make n false in
  let outdegs = Array.make n 0 in
  let is_in_subgraph e' =
    e'.id < n && in_subgraph.(e'.id)
  in
  List.iter (fun e -> in_subgraph.(e.id) <- true) events;
  List.iter (fun e ->
    preds e |> List.rev |>
    List.iter (fun e' ->
      if is_in_subgraph e' then
        outdegs.(e'.id) <- outdegs.(e'.id) + 1
    )
  ) events;
  let q = List.filter (fun e -> outdegs.(e.id) = 0) events |> List.to_seq |> Stack.of_seq in
  let res = ref [] in
  while Stack.is_empty q |> not do
    let e = Stack.pop q in
    res := e::!res;
    preds e |> List.rev |> List.iter (fun e' ->
      if is_in_subgraph e' then (
        outdegs.(e'.id) <- outdegs.(e'.id) - 1;
        if outdegs.(e'.id) = 0 then
          Stack.push e' q
      )
    )
  done;
  !res


let toposort = toposort_with_preds imm_preds

let event_predecessors (ev : event) : event list =
  let visitor add_to_queue cur =
    let rec get_queue src =
    match src with
    | `Later (e1, e2) ->
      add_to_queue e1;
      add_to_queue e2
    | `Branch (_, {branches_val; _}) ->
      List.iter add_to_queue branches_val
    | `Seq (ev', _)
    | `Root (Some (ev', _)) ->
      add_to_queue ev'
    | `Root None -> ()
    | `UntilEntry (ev', info) ->
      add_to_queue ev';
      add_to_queue info.until_body_end
    | `UntilExit info ->
      add_to_queue info.until_stop_cond
    | `Recurse (src, id) ->(
      get_queue src;
      let ev' = List.find (fun e -> e.id = id) cur.graph.events in
      add_to_queue ev'
    )
  in
  get_queue cur.source in
  event_traverse ev visitor |> toposort

let event_successors (ev : event) : event list =
  let visitor add_to_queue cur =
    List.iter add_to_queue cur.outs
  in
  event_traverse ev visitor |> toposort

let events_pred events ev =
  let n = List.length events in
  let preds = event_predecessors ev in
  let event_is_pred = Array.make n false in
  List.iter (fun e -> event_is_pred.(e.id) <- true) preds;
  (preds, event_is_pred)


let event_is_successor (ev : event) (ev' : event) =
  event_successors ev |> List.exists (fun x -> x.id = ev'.id)

let event_is_predecessor (ev : event) (ev' : event) =
  event_predecessors ev |> List.exists (fun x -> x.id = ev'.id)


(* inclusive: include the matching event itself or its predecessor? *)
let find_first_msg_after (ev : event) (msg: Lang.message_specifier) inclusive =
  event_successors ev |> List.find_map
    (fun ev' ->
      List.find_map (fun sa ->
        match sa.d.ty with
        | Send (msg', _) | Recv msg' ->
            if msg' = msg then Some (ev', sa) else None
      ) ev'.sustained_actions
      |> Option.map (fun (ev', sa) -> if inclusive then sa.d.until else ev')
    )


module IntHashtbl = Hashtbl.Make(Int)
let event_distance_max = 1 lsl 20
let event_succ_distance non_succ_dist msg_dist_f later_dist_f either_dist_f events (ev : event) (cur: event) =
  assert (cur.id = ev.id); (* not supporting other cases *)
  let preds = event_predecessors ev in
  let dist = IntHashtbl.create 8 in
  IntHashtbl.add dist ev.id 0;
  let get_dist ev' = IntHashtbl.find_opt dist ev'.id |> Option.value ~default:non_succ_dist in
  let set_dist ev' d = IntHashtbl.add dist ev'.id d in
  List.iter (fun ev' -> set_dist ev' 0) preds; (* predecessors must have been reached *)
  List.rev events |> List.iter (fun ev' ->
    if IntHashtbl.find_opt dist ev'.id |> Option.is_none then
    let d =
      let rec get_d src = 
      match src with
    | `Root None -> raise (Except.unknown_error_default "Unexpected root!")
    | `Later (ev1, ev2) -> later_dist_f (get_dist ev1) (get_dist ev2)
    | `Seq (ev1, ad) ->
      let d1 = get_dist ev1 in
      (
        match ad with
        | `Cycles n' -> d1 + n'
        | `Send _ | `Recv _ | `Choice _ | `Sync _ -> msg_dist_f d1
      )
    | `Root (Some (ev1, _)) ->
      (* We need to check carefully to decide if we are sure
        the branch has/hasn't been taken. *)
        get_dist ev1
    | `Branch (_, {branches_val = [ev]; _}) ->
      get_dist ev
    | `Branch (_, {branches_val = ev1::ev2::el; _}) ->
      let first_two = either_dist_f (get_dist ev1) (get_dist ev2) in
      List.fold_left (fun v e -> either_dist_f v @@ get_dist e) first_two el
    | `Recurse (src, id) ->
      let ev' = List.find (fun e -> e.id = id) ev'.graph.events in
      get_d src |> either_dist_f (get_dist ev')
    | _ -> raise (Except.unknown_error_default "Unexpected event source!")
    in
    get_d ev'.source 
  in
    set_dist ev' (min d event_distance_max)
  );
  dist

let event_min_among_succ events weights =
  let n = List.length events in
  assert (n = (Array.length weights));
  let res = Array.copy weights in
  List.iter (fun ev' ->
    let update_res e' v =
      let v' = res.(e'.id) in
      if v < v' then
        res.(e'.id) <- v
    in
    let v = res.(ev'.id) in
    let rec get_res src =
    match src with
    | `Root None -> ()
    | `Later (e1, e2) ->
      update_res e1 v;
      update_res e2 v
    | `Branch (_, {branches_val; _}) ->
      List.iter (fun e -> update_res e v) branches_val
    | `Seq (e, _) ->
      update_res e v
    | `Root (Some (e, br_side)) ->
      (* side sel = 0 is visited last *)
      if br_side.branch_side_sel = 0 then (
        update_res e
        @@ List.fold_left
          (fun v e -> Int.max v res.(e.id)) v br_side.owner_branch.branches_to
      )
    | `UntilEntry (e, info) ->
      (* To Do : verify *)
      update_res e v;
      update_res info.until_body_end v
    | `UntilExit info ->
      update_res info.until_stop_cond v
    | `Recurse (src, id) ->
      let ev' = List.find (fun e -> e.id = id) ev'.graph.events in
      update_res ev' v;
      get_res src
    in
    get_res ev'.source
  ) events;
  res

let event_min_distance =
  event_succ_distance event_distance_max (fun d -> d) min min

let event_min_distance_with_later =
  event_succ_distance event_distance_max (fun d -> d) max min

let event_max_distance =
  event_succ_distance event_distance_max (fun _ -> event_distance_max) max max


let events_visit_backward visitor = List.iter visitor
let events_visit_forward visitor events = List.rev events |> List.iter visitor

let events_prepare_outs events =
  List.iter (fun ev -> ev.outs <- []) events;
  List.iter (fun ev ->
    let rec prep_out src = 
    match src with
    | `Later (e1, e2) ->
      e1.outs <- ev::e1.outs;
      e2.outs <- ev::e2.outs
    | `Branch (_ev', br_info) ->
      List.iter (fun e ->
        e.outs <- ev::e.outs
      ) br_info.branches_val
    | `Seq (ev', _)
    | `Root (Some (ev', _)) ->
      ev'.outs <- ev::ev'.outs
    | `Root None -> ()
    | `UntilEntry (ev', info) ->
      ev'.outs <- ev::ev'.outs;
      info.until_body_end.outs <- ev::info.until_body_end.outs
    | `UntilExit info ->
      info.until_stop_cond.outs <- ev::info.until_stop_cond.outs
    | `Recurse (src, id) ->
      let ev' = List.find (fun e -> e.id = id) ev.graph.events in
      ev'.outs <- ev::ev'.outs;
      prep_out src
    in
    prep_out ev.source
  ) events

let event_is_dominant e1 e2 =
  let preds = (event_predecessors e1) @ [e1] in
  (* max id + 1 *)
  let n = (List.fold_left (fun i e -> Int.max i e.id) 0 preds) + 1 in
  let is_dominated = Array.make n false in
  List.iter (fun e ->
    let d =
      if e.id = e2.id then
        true
      else (
        let rec get_dominant src =
        match src with
        | `Root None -> false
        | `Later (e1, e2) ->
          is_dominated.(e1.id) || is_dominated.(e2.id)
        | `Seq (e', _) ->
          is_dominated.(e'.id)
        | `Branch (_, {branches_val; _}) ->
          List.fold_left (fun b e -> b && is_dominated.(e.id)) true branches_val
        | `Root (Some (e', _)) ->
          is_dominated.(e'.id)
          (* for now i *)
        | `UntilEntry (e', _) ->
          (* assuming entry happens always : can also be exit of body *)
          is_dominated.(e'.id) 
        | `UntilExit info ->
          is_dominated.(info.until_stop_cond.id)
        | `Recurse (src, id) ->
          let ev' = List.find (fun e -> e.id = id) e.graph.events in
          get_dominant src && is_dominated.(ev'.id)
        in
        get_dominant e.source
      )
    in
    is_dominated.(e.id) <- d
  ) preds;
  is_dominated.(e1.id)

let events_pred_min_dist ev =
  let preds = (event_predecessors ev) @ [ev] in
  let n = (List.fold_left (fun i e -> Int.max i e.id) 0 preds) + 1 in
  let is_preds = Array.make n false in
  let check_is_pred e = e.id < n && is_preds.(e.id) in
  List.iter (fun e -> is_preds.(e.id) <- true) preds;
  let res = Array.make n (-1) in
  let branch_counter = Hashtbl.create 4 in
  res.(ev.id) <- 0;
  let update_dist e v =
    if res.(e.id) < v then
      res.(e.id) <- v
  in
  List.rev preds
    |> List.iter (fun e ->
      let v = res.(e.id) in
      match e.source with
      | `Seq (e', d) -> (
        let gap =
          (* if we want max delay of pred we change send recv to <max> *)
          match d with
          | `Cycles n -> n
          | `Send _ | `Recv _ | `Choice _
          | `Sync _ -> 0
        in
        update_dist e' (v + gap)
      )
      | `Later (e1, e2) -> (
        update_dist e1 v;
        update_dist e2 v
      )
      | `Branch (_, {branches_val; _}) ->
        List.iter (fun e -> update_dist e v) branches_val
      | `Root None -> ()
      | `Root (Some (e', {branch_event = Some br_ev; owner_branch; branch_side_sel})) -> (
        let c = Hashtbl.find_opt branch_counter br_ev.id |> Option.value ~default:0 in
        if c + 1 = owner_branch.branch_count then (
          (* only pass when all sides have been reached *)
          update_dist e'
            @@
            List.fold_left (fun v e -> Int.min v res.(e.id))
              event_distance_max owner_branch.branches_to
        ) else (
          (* other sides of the branch may not be a predecessor, in which
          case we just pass through the result as there is no real branching *)
          let other_side_idx = if branch_side_sel = 0 then 1 else 0 in
          let other = List.nth owner_branch.branches_to other_side_idx in
          if check_is_pred other then
            Hashtbl.replace branch_counter br_ev.id (c + 1)
          else
            update_dist e' v
        )
      )
      | _ -> raise (Except.unknown_error_default "Unexpected event source!")
    );
  res

(* E G (ev -> e) *)
let events_reachable events ev =
  let n = List.length events in
  let event_is_reachable = Array.make n true in
  let (preds, is_pred) = events_pred events ev in
  let preds = preds @ [ev] in
  List.iter (fun e ->
      match e.source with
      | `Root (Some (_, br_side_info)) ->
        (* invalidate the other side of the branch if it's not a predecessor *)
        List.iter (fun other_side ->
          if other_side.id <> e.id && not is_pred.(other_side.id) then
            event_is_reachable.(other_side.id) <- false
        ) br_side_info.owner_branch.branches_to
      | _ -> ()
    ) preds;
  (* now propagate *)
  List.rev events
  |> List.iter (fun e ->
      if event_is_reachable.(e.id) then (
        let reachable =
          let rec get_src_reachable src =
          match src with
          | `Root None -> true
          | `Root (Some (e', _)) -> event_is_reachable.(e'.id)
          | `Later (e1, e2) -> event_is_reachable.(e1.id) && event_is_reachable.(e2.id)
          | `Seq (e', _) -> event_is_reachable.(e'.id)
          | `Branch (_, {branches_val; _}) ->
            List.fold_left (fun b e -> b || event_is_reachable.(e.id)) false branches_val
          | `UntilEntry (e', _) ->
            (* same thing : To  Do *)
            event_is_reachable.(e'.id)
          | `UntilExit info ->
            event_is_reachable.(info.until_stop_cond.id)
          | `Recurse (src, id) ->
            let ev' = List.find (fun e -> e.id = id) e.graph.events in
            get_src_reachable src || event_is_reachable.(ev'.id)
          in
          get_src_reachable e.source
        in
        event_is_reachable.(e.id) <- reachable
      )
    );
  event_is_reachable

let events_max_dist events lookup_message ev =
  let n = List.length events in
  let res = Array.make n (-event_distance_max) in
  let pred_min_dist = events_pred_min_dist ev in
  let pred_min_dist_mxn = Array.length pred_min_dist in
  let is_pred e' = e'.id < pred_min_dist_mxn && pred_min_dist.(e'.id) >= 0 in
  let reachable = events_reachable events ev in
  let update_dist e v =
    if res.(e.id) > v then
      res.(e.id) <- v
  in
  let get_max_delay =
    function
    | `Cycles n -> n
    | `Send m  ->
      let msg_def = lookup_message m |> Option.get in
      (
        match msg_def.recv_sync with
        | Static _ | Dependent _ -> 0
        | _ -> event_distance_max
      )
    | `Choice mlist ->
      List.fold_left (fun mx m ->
        let wild_card = {msg="*"; endpoint = "*"  } in
        if m = wild_card then
          event_distance_max
        else
        let msg_def = lookup_message m |> Option.get in
        let d = match msg_def.recv_sync with
          | Static _ | Dependent _ -> 0
          | _ -> event_distance_max
        in
        Int.max mx d
      ) 0 mlist 
    | `Recv m ->
      let msg_def = lookup_message m |> Option.get in
      (
        match msg_def.send_sync with
        | Static _ | Dependent _ -> 0
        | _ -> event_distance_max
      )
    | `Sync _ -> event_distance_max (* oo *)
  in
  let get_min_delay =
    function
    | `Cycles n -> n
    | `Send _ | `Recv _ | `Sync _ | `Choice _ -> 0
  in
  let min2_outs = Array.make n
    ((event_distance_max, 0), (event_distance_max, 0))
  in
  let update_min2_outs v e' e =
    let ((m0, i0), (m1, i1)) = min2_outs.(e.id) in
    let r =
      if v < m0 then
        ((v, e'.id), (m0, i0))
      else if v < m1 then
        ((m0, i0), (v, e'.id))
      else
        ((m0, i0), (m1, i1))
    in
    min2_outs.(e.id) <- r
  in
  let pick_filter_out ((m0, i0), (m1, _i1)) i =
    if i0 <> i then m0
    else m1
  in
  List.iter (fun e ->
    if is_pred e then (
      match e.source with
      | `Seq (e', d') ->
        update_min2_outs (-(pred_min_dist.(e.id) + (get_min_delay d'))) e e'
      | `Root (Some (e', br_side)) ->
        let other_side =
          if br_side.branch_side_sel = 0 then 1 else 0
        in
        let other_side = List.nth br_side.owner_branch.branches_to other_side in
        if not (is_pred other_side) || br_side.branch_side_sel = 0 then (
          let m =
            List.fold_left (fun v e ->
              if is_pred e then
                Int.min v (-pred_min_dist.(e.id))
              else
                v
            ) event_distance_max br_side.owner_branch.branches_to
          in
          let e = List.hd br_side.owner_branch.branches_to in
          update_min2_outs m e e'
        )
      | _ -> ()
    )
  ) events;
  List.rev events
    |> List.iter (fun e ->
      if reachable.(e.id) then (
        let pred = is_pred e in
        if pred then res.(e.id) <- -pred_min_dist.(e.id)
        else res.(e.id) <- event_distance_max;
        (
          (* propagate *)
          let rec gen_src_max src =
          (
          match src with
          | `Root None -> ()
          | `Seq (e', d) -> (
            let gap = get_max_delay d in
            if res.(e'.id) = -event_distance_max then
              update_dist e @@ -event_distance_max
            else (
              update_dist e @@ res.(e'.id) + gap;
              (* we can look at other paths *)
              let other_path = pick_filter_out min2_outs.(e'.id) e.id in
              if other_path <> -event_distance_max then
                update_dist e @@ other_path + gap
            )
          )
          | `Later (e1, e2) ->
            if not pred then
              update_dist e @@ Int.max (res.(e1.id)) (res.(e2.id))
          | `Branch (_, {branches_val; _}) ->
            update_dist e
              @@
              List.fold_left
                (fun v e -> Int.max v res.(e.id))
                (-event_distance_max) branches_val
          | `Root (Some (e', br_side)) ->
            update_dist e res.(e'.id);
            let first_br_to = List.hd br_side.owner_branch.branches_to in
            update_dist e @@ pick_filter_out min2_outs.(e'.id) first_br_to.id
          | `UntilEntry (e', info) ->
            update_dist e @@ Int.max res.(e'.id) res.(info.until_body_end.id)
          | `UntilExit info ->
            update_dist e res.(info.until_stop_cond.id)
          | `Recurse (src, id) ->
            let ev' = List.find (fun e -> e.id = id) e.graph.events in
            gen_src_max src;
            update_dist e @@ (Int.max (res.(e.id)) (res.(ev'.id)))

        )
          in
          gen_src_max e.source
        )
      )
    );
  res

let event_is_msg_end msg e =
  List.exists (fun ac_span ->
    match ac_span.d with
    | ImmediateSend (msg', _)
    | ImmediateRecv msg' ->
      msg' = msg
    | _ -> false
  ) e.actions
  ||
  match e.source with
  | `Seq (_, `Send msg') | `Seq (_, `Recv msg') ->
    msg' = msg
  | _ -> false


let events_with_msg events msg = List.filter (event_is_msg_end msg) events

let events_start_msg events msg =
  List.filter (fun e ->
      List.exists (fun sa ->
        match sa.d.ty with
        | Send (msg', _) | Recv msg' -> msg' = msg
      ) e.sustained_actions
    ) events

let events_first_msg events ev msg =
  let n = List.length events in
  let path_has_msg = Array.make n false in
  let event_has_msg = Array.make n false in
  events_with_msg events msg
    |> List.iter (fun e -> event_has_msg.(e.id) <- true);
  let succs = event_successors ev in
  let event_is_succ = Array.make n false in
  List.iter (fun e -> event_is_succ.(e.id) <- true) succs;
  let preds = event_predecessors ev in
  let event_is_pred = Array.make n false in
  List.iter (fun e -> event_is_pred.(e.id) <- true) preds;
  let event_succ_masked_has_msg e = ev.id <> e.id && event_is_succ.(e.id) && event_has_msg.(e.id) in
  assert (event_succ_masked_has_msg ev |> not);
  let reachable = events_reachable events ev in
  List.iter (fun e ->
      let v =
        let rec get_v src =
        match src with
        | `Root None -> false
        | `Later (e1, e2) ->
            path_has_msg.(e1.id) || path_has_msg.(e2.id)
              || (event_succ_masked_has_msg e1) || (event_succ_masked_has_msg e2)
        | `Root (Some (e', _))
        | `Seq (e', _) -> path_has_msg.(e'.id) || (event_succ_masked_has_msg e')
        | `Branch (_, {branches_val; _}) ->
          List.fold_left (fun v e ->
            if reachable.(e.id) then
              v && (path_has_msg.(e.id) || event_succ_masked_has_msg e)
            else
              v
          ) true branches_val
        | `UntilEntry (e', info) ->
          path_has_msg.(e'.id) || path_has_msg.(info.until_body_end.id)
            || (event_succ_masked_has_msg e') || (event_succ_masked_has_msg info.until_body_end)
        | `UntilExit info ->
          path_has_msg.(info.until_stop_cond.id) || (event_succ_masked_has_msg info.until_stop_cond)
        | `Recurse (src, id) ->
          let ev' = List.find (fun e -> e.id = id) e.graph.events in
          get_v src && (if reachable.(ev'.id) then
            path_has_msg.(ev'.id) || event_succ_masked_has_msg ev'
          else
            true)
          in
        get_v e.source
      in
      path_has_msg.(e.id) <- v
    ) succs;
  (* now handle those that are neither predecessor nor successor but remove those in other sides of branches *)
  (* reachable non-predecessor or first successor *)
  List.filter (fun e ->
      event_has_msg.(e.id) && e.id <> ev.id && (
        (not event_is_pred.(e.id) && not event_is_succ.(e.id) && reachable.(e.id)) ||
        (event_is_succ.(e.id) && not path_has_msg.(e.id))
      )
    ) events


type events_order =
| Before
| After
| BeforeEq
| AfterEq
| AlwaysEq
| Unordered
| Unreachable

let is_strict_ordered = function
  | Before | After | Unreachable -> true
  | _ -> false

let events_get_order events lookup_message e1 e2 =
  let to_sign v =
    if v = -event_distance_max then -2
    else if v < 0 then -1
    else if v > 0 then 1
    else 0
  in
  let mx_dist1 = (events_max_dist events lookup_message e1).(e2.id) |> to_sign in
  let mx_dist2 = (events_max_dist events lookup_message e2).(e1.id) |> to_sign in
  match mx_dist1, mx_dist2 with
  | -2, _ | _, -2 -> Unreachable
  | 0, 0 -> AlwaysEq
  | 1, 1 | -1, -1 -> Unordered
  | -1, 0 | 0, 1 -> AfterEq
  | -1, 1 -> After
  | 1, 0 | 0, -1 -> BeforeEq
  | 1, -1 -> Before
  | _ -> Unreachable

let graph_owned_regs g =
  let res = ref [] in
  List.iter (fun e ->
    List.iter (fun ac_span ->
      match ac_span.d with
      | RegAssign (lval, _td) ->
        res := lval.lval_range.subreg_name::!res
      | _ -> ()
    ) e.actions
  ) g.events;
  !res

let message_is_immediate msg is_send =
  (is_send && msg.recv_sync <> Dynamic) || (not is_send && msg.send_sync <> Dynamic)



(* Check if there exists a path from event with id 'from_id' to event with id 'to_id' *)
let exists_path_prime (graph_prime : event_graph_prime) (from_id : int) (to_id : int) : bool =
  let visited = Hashtbl.create (List.length graph_prime.event_nodes) in
  let event_map = 
    List.fold_left (fun acc ev -> Hashtbl.add acc ev.ev_id ev; acc) 
                   (Hashtbl.create (List.length graph_prime.event_nodes)) 
                   graph_prime.event_nodes in

  let rec dfs current_id =
    if current_id = to_id then true
    else if Hashtbl.mem visited current_id then false
    else (
      Hashtbl.add visited current_id ();
      match Hashtbl.find_opt event_map current_id with
      | None -> false
      | Some event_prime -> List.exists (fun (child : event_child) -> dfs child.cid) event_prime.child
    )
  in
  dfs from_id

(* Get all events reachable from the given event id *)
let get_all_reachable_prime (graph_prime : event_graph_prime) (from_id : int) : int list =
  let visited = Hashtbl.create (List.length graph_prime.event_nodes) in
  let reachable = ref [] in
  let event_map = 
    List.fold_left (fun acc ev -> Hashtbl.add acc ev.ev_id ev; acc) 
                   (Hashtbl.create (List.length graph_prime.event_nodes)) 
                   graph_prime.event_nodes in

  let rec dfs current_id =
    if not (Hashtbl.mem visited current_id) then (
      Hashtbl.add visited current_id ();
      reachable := current_id :: !reachable;
      match Hashtbl.find_opt event_map current_id with
      | None -> ()
      | Some event_prime -> List.iter (fun (child : event_child) -> dfs child.cid) event_prime.child
    )
  in
  dfs from_id;
  List.rev !reachable

(* Find all paths from 'from_id' to 'to_id' (returns list of path as list of event ids) *)
let find_all_paths_prime (graph_prime : event_graph_prime) (from_id : int) (to_id : int) : int list list =
  let event_map = 
    List.fold_left (fun acc ev -> Hashtbl.add acc ev.ev_id ev; acc) 
                   (Hashtbl.create (List.length graph_prime.event_nodes)) 
                   graph_prime.event_nodes in

  let rec find_paths current_id path visited =
    if current_id = to_id then [List.rev (current_id :: path)]
    else if List.mem current_id visited then []
    else (
      match Hashtbl.find_opt event_map current_id with
      | None -> []
      | Some event_prime -> 
          List.fold_left (fun acc (child : event_child) ->
            let new_paths = find_paths child.cid (current_id :: path) (current_id :: visited) in
            acc @ new_paths
          ) [] event_prime.child
    )
  in
  find_paths from_id [] []

(* cuts the path till reaching the event*)
let filter_paths_with_event (paths: int list list) (event_ids: int list) : int list list =
  let filter_path = List.filter (
          fun p -> List.exists(fun ge -> List.mem ge p)event_ids
  ) paths
  in 
  let split_path_on_events p =
    let rec aux acc current = function
      | [] -> if current = [] then List.rev acc else List.rev (List.rev current :: acc)
      | x :: xs ->
          if List.mem x event_ids then
            if current = [] then aux acc [x] xs
            else aux (List.rev current :: acc) [x] xs
          else
            aux acc (x :: current) xs
    in
    let segments = aux [] [] p |> List.filter (fun seg -> seg <> []) in
    segments
  in
  let acc = ref [] in
  List.iter (fun p -> acc := split_path_on_events p @ !acc) filter_path;
  let trimmed_paths = !acc in
  (* filter for duplicates *)
  let unique_paths = Hashtbl.create (List.length trimmed_paths) in
  List.iter (fun p -> Hashtbl.replace unique_paths p ()) trimmed_paths;
  let trimmed_paths = Hashtbl.fold (fun k _ acc -> k :: acc) unique_paths [] in
(* 
  Printf.eprintf "The trimmed paths are  of len %d \n" (List.length (List.hd trimmed_paths));
  List.iter(fun p -> Printf.eprintf "original path : " ;List.iter (fun ge -> Printf.eprintf "%d " ge) p; Printf.eprintf "\n") paths;
  List.iter(
    fun p -> Printf.eprintf "trimmed path : " ;List.iter (fun ge -> Printf.eprintf "%d " ge) p; Printf.eprintf "\n"
  ) trimmed_paths; *)
  trimmed_paths

(* cuts the path and returns segment in between the events*)
let filter_paths_between_events (paths : int list list) (event_ids : int list) : int list list =
  let filter_path = List.filter (
          fun p -> List.exists (fun ge -> List.mem ge event_ids) p
  ) paths
  in 
  let extract_segment_split p = 
    let start = ref false in
    let rec aux acc current = function
    (* if empty and start is false discard the current segment and return the collection *)
      | [] -> List.rev acc 
      | x :: xs ->
        if List.mem x event_ids then
          if not !start then (
            start := true;
            aux acc [x] xs
          ) else (
            (* end of segment *)
            let new_acc = List.rev (x :: current) :: acc in
            aux new_acc [] xs
          )
      else aux acc (x :: current) xs
  in
  aux [] [] p
  in
  let acc = ref [] in
  List.iter (fun p -> acc := extract_segment_split p @ !acc) filter_path;
  let trimmed_paths = !acc in
  (* filter for duplicates *)
  let unique_paths = Hashtbl.create (List.length trimmed_paths) in
  List.iter (fun p -> Hashtbl.replace unique_paths p ()) trimmed_paths;
  let trimmed_paths = Hashtbl.fold (fun k _ acc -> k :: acc) unique_paths [] in

  trimmed_paths


let filter_paths_with_multiple_events (paths: int list list) (event_ids: int list list) : int list list =
  (* Check if a path contains multiple events from the event pool of event ids list list *)
  let filter_path = List.filter (
          fun p -> 
            let count = List.fold_left (fun acc event_pool ->
              if List.exists (fun ge -> List.mem ge p) event_pool then acc + 1 else acc
            ) 0 event_ids in
            count >= 2
  ) paths
  in 
  filter_path


type session_node = {
  session_msg : Lang.message_specifier;
  mutable session_childs : Lang.message_specifier list;
  event_id : int; (* the event where this message action occurs *)
}

type session_graph = {
  session_nodes : session_node list;
}


let extract_message_from_action action =
  match action with
  | DebugPrint _ | DebugFinish | RegAssign _ | PutShared _ -> None
  | ImmediateSend (msg, _) -> Some (msg) (* true = send *)
  | ImmediateRecv msg -> Some (msg) (* false = receive *)


let extract_message_from_sustained_action sa =
  match sa.ty with
  | Send (msg, _) -> Some (msg) (* true = send *)
  | Recv msg -> Some (msg) (* false = receive *)



let create_session_graph (g: event_graph) : session_graph = 
  let visited_events = Hashtbl.create (List.length g.events) in
  let all_nodes = ref [] in

  (* Process the current event to extract message actions *)
  let process_event event =
    let action_nodes = List.fold_left (fun acc action ->
      match extract_message_from_action action.d with
      | Some (msg) ->
        let node = { session_msg = msg; session_childs = []; event_id = event.id } in
        node :: acc
      | None -> acc
    ) [] event.actions in
    
    let sustained_nodes = List.fold_left (fun acc sa ->
      match extract_message_from_sustained_action sa.d with
      | Some (msg) ->
        let node = { session_msg = msg; session_childs = []; event_id = event.id } in
        node :: acc
      | None -> acc
    ) [] event.sustained_actions in
    
    action_nodes @ sustained_nodes
  in

  (* Traverse over graphs bfs add children as session nodes *)
  let rec bfs current_event =
    if not (Hashtbl.mem visited_events current_event.id) then (
      Hashtbl.add visited_events current_event.id ();
      let nodes = process_event current_event in
      all_nodes := nodes @ !all_nodes;
      List.iter bfs current_event.outs
    )
  in
  
  (* Find root events and start BFS from them *)
  let root_events = List.filter (fun e ->
    match e.source with
    | `Root _ -> true
    | _ -> false
  ) g.events in
  
  List.iter bfs root_events;
  
  (* Build connections between nodes based on event ordering *)
  let event_to_nodes = Hashtbl.create (List.length !all_nodes) in
  List.iter (fun node ->
    let current_nodes = Hashtbl.find_opt event_to_nodes node.event_id |> Option.value ~default:[] in
    Hashtbl.replace event_to_nodes node.event_id (node :: current_nodes)
  ) !all_nodes;
  
  (* For each node, connect it to nodes in successor events *)
  List.iter (fun node ->
    let current_event = List.find (fun e -> e.id = node.event_id) g.events in
    (* Use direct outgoing edges to connect to successor nodes *)
    List.iter (fun succ_event ->
      match Hashtbl.find_opt event_to_nodes succ_event.id with
      | Some succ_nodes ->
        List.iter (fun succ_node ->
          if not (List.mem succ_node.session_msg node.session_childs) then
            node.session_childs <- succ_node.session_msg :: node.session_childs
        ) succ_nodes
      | None -> ()
    ) current_event.outs
  ) !all_nodes;
  
  { session_nodes = !all_nodes }



let print_session_graph (sg: session_graph) =

  let node_map = Hashtbl.create (List.length sg.session_nodes) in
  List.iter (fun node ->
    Hashtbl.add node_map (node.session_msg.endpoint ^ "." ^ node.session_msg.msg) node
  ) sg.session_nodes;
  
  let visited = Hashtbl.create (List.length sg.session_nodes) in
  let msg_to_string msg = msg.endpoint ^ "." ^ msg.msg in
  
  let rec print_node node =
    let node_key = msg_to_string node.session_msg in
    if Hashtbl.mem visited node_key then
      Printf.sprintf "(%s)" node_key
    else (
      Hashtbl.add visited node_key ();
      match node.session_childs with
      | [] -> node_key (* leaf node *)
      | [child] -> 
        let child_node = Hashtbl.find_opt node_map (msg_to_string child) in
        (match child_node with
         | Some cn -> Printf.sprintf "%s -> %s" node_key (print_node cn)
         | None -> Printf.sprintf "%s -> %s" node_key (msg_to_string child))
      | children ->
        (* multiple children: node -> {child1 ^ child2 ^ ...} *)
        let child_strs = List.map (fun child ->
          let child_node = Hashtbl.find_opt node_map (msg_to_string child) in
          match child_node with
          | Some cn -> print_node cn
          | None -> msg_to_string child
        ) children in
        Printf.sprintf "%s -> {%s}" node_key (String.concat " ^ " child_strs)
    )
  in
  
  let all_child_msgs = List.concat_map (fun node -> node.session_childs) sg.session_nodes in
  let root_nodes = List.filter (fun node ->
    not (List.exists (fun child_msg -> 
      child_msg.endpoint = node.session_msg.endpoint && 
      child_msg.msg = node.session_msg.msg
    ) all_child_msgs)
  ) sg.session_nodes in
  
  let graph_strings = List.map print_node root_nodes in
  Printf.eprintf "Session Graph: %s\n" (String.concat " | " graph_strings)
  