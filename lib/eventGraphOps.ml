open EventGraph


let lifetime_const current = {live = current; dead = [(current, `Eternal)]}
let lifetime_immediate current = {live = current; dead = [(current, `Cycles 1)]}

let full_reg_range regname size =
  {
    subreg_name = regname;
    subreg_range_interval = (Const 0, size)
  }

let sub_reg_range regname offset len =
  {
    subreg_name = regname;
    subreg_range_interval = (Const offset, len)
  }
  
let subreg_ranges_possibly_intersect r1 r2 =
  r1.subreg_name = r2.subreg_name &&
    (match fst r1.subreg_range_interval, fst r2.subreg_range_interval with
    | Const n1, Const n2 ->
      let end1 = n1 + (snd r1.subreg_range_interval)
      and end2 = n2 + (snd r2.subreg_range_interval) in
      end2 > n1 && end1 > n2
    | _ -> true
    )

let print_graph (g: event_graph) =
  List.iter (fun ev ->
    let rec src_string src =
      (
    match src with
    | `Later (e1, e2) -> Printf.eprintf "> %d: later %d %d\n" ev.id e1.id e2.id
    | `Seq (ev', a) ->
      let c = match a with
      | `Cycles n -> Printf.sprintf "C %d" n
      | `Send _ -> "S"
      | `Recv _ -> "R"
      | `Choice _-> "IC"
      | `Sync s -> Printf.sprintf "S %s" s
      in
      Printf.eprintf "> %d: seq %d %s\n" ev.id ev'.id c
    | `Branch (ev', _) -> Printf.eprintf "> %d: branch %d\n" ev.id ev'.id
    | `Root None -> Printf.eprintf "> %d: root\n" ev.id
    | `Root (Some (ev', br_side_info)) ->
        Printf.eprintf "> %d: branch-root %d %d\n" ev.id br_side_info.branch_side_sel ev'.id
    | `Recurse (source, id) ->
        src_string source;
        Printf.eprintf "> %d: recurse id:%d\n" ev.id id
    | `Select (e, msg_group) ->
        Printf.eprintf "> %d: select %d with msg group %s\n" ev.id e.id (String.concat ";" (List.map Lang.string_of_msg_spec msg_group))
    | `SelectJoin join_info ->
        Printf.eprintf "> %d: select join with parent %d, join roots [%s], join nodes [%s]\n" ev.id join_info.join_parent.id
          (String.concat ";" (List.map (fun e -> string_of_int e.id) join_info.join_roots))
          (String.concat ";" (List.map (fun e -> string_of_int e.id) join_info.join_nodes))
      )
    in
    src_string ev.source
  ) g.events

let print_dot_graph g out =
  Printf.fprintf out "// BEGIN GRAPH IN DOT FORMAT\n";
  Printf.fprintf out "// can render to PDF with 'dot -Tpdf -O <filename>'\n";
  Printf.fprintf out "digraph {\n";
  let ev_node_name ev = Printf.sprintf "event%d" ev.id in
  let print_edge e1 e2 label =
    Printf.fprintf out "  %s -> %s [label = \"%s\"];\n"
      (ev_node_name e1)
      (ev_node_name e2)
      label
  in
  List.iter (fun ev ->
    if ev.is_loop_terminal then
      Printf.fprintf out "  %s [peripheries=2];\n" @@ ev_node_name ev
    else if ev.is_recurse then
      Printf.fprintf out "  %s [style=dashed];\n" @@ ev_node_name ev;
    let rec print_src_edge src =
    (
      match src with
    | `Later (e1, e2) ->
      print_edge e1 ev "L";
      print_edge e2 ev "L"
    | `Seq (ev', a) ->
      let label = match a with
      | `Cycles n -> Printf.sprintf "#%d" n
      | `Send _ -> "S"
      | `Recv _ -> "R"
      | `Choice _ -> "IC"
      | `Sync _ -> "G"
      in
      print_edge ev' ev label
    | `Branch (_, br_info) ->
      List.iter (fun e ->
        print_edge e ev "B"
      ) br_info.branches_val
    | `Root None -> ()
    | `Root (Some (ev', br_side_info)) ->
      let ev_has_imm_act = List.find_opt (fun a ->
        match a.Lang.d with
        | ImmediateRecv _ | ImmediateSend _ -> true
        | _ -> false
      ) ev.actions in
      (
        match ev_has_imm_act with
        | Some act ->
          let act_string =
            match act.Lang.d with
            | ImmediateRecv ms -> (Lang.string_of_msg_spec ms)^"?"
            | ImmediateSend (ms, _) -> (Lang.string_of_msg_spec ms)^"!"
            | _ -> failwith "Unexpected action"
          in
          print_edge ev' ev act_string
        | None -> print_edge ev' ev @@ string_of_int br_side_info.branch_side_sel
      )
    | `Recurse (source, id) ->
      print_src_edge source;
      let rec_ev = List.find (fun e -> e.id = id) g.events in
      print_edge rec_ev ev ("ϵ")
    | `Select (e, msg_group) ->
      print_edge e ev (Printf.sprintf "?{%s}" (String.concat ";" (List.map Lang.string_of_msg_spec msg_group)))
    | `SelectJoin join_info ->
      List.iter (fun e ->
        print_edge e ev "?J"
      ) join_info.join_nodes
    ) in
    print_src_edge ev.source
  ) g.events;
  Printf.fprintf out "}\n";
  Printf.fprintf out "// END GRAPH IN DOT FORMAT\n"


let print_graph_with_session_types g out =
  Printf.fprintf out "// BEGIN GRAPH WITH SESSION TYPES IN DOT FORMAT\n";
  Printf.fprintf out "// can render to PDF with 'dot -Tpdf -O <filename>'\n";
  Printf.fprintf out "digraph {\n";
  let escape_dot_string s =
    String.concat "" (List.map (fun c ->
      match c with
      | '"' -> "\\\""
      | '\\' -> "\\\\"
      | _ -> String.make 1 c
    ) (List.of_seq (String.to_seq s)))
  in
  let ev_node_name ev =
    match ev.session_type with
    | Some session_type ->
      Printf.sprintf "\"event%d\\n(%s)\""
        ev.id (escape_dot_string (Lang.string_of_protocol session_type.d))
    | None ->
      Printf.sprintf "\"event%d\\n($)\"" ev.id
  in
  let print_edge e1 e2 label =
    Printf.fprintf out "  %s -> %s [label = \"%s\"];\n"
      (ev_node_name e1)
      (ev_node_name e2)
      label
  in
  List.iter (fun ev ->
    if ev.is_loop_terminal then
      Printf.fprintf out "  %s [peripheries=2];\n" @@ ev_node_name ev;
   let rec print_src_edge src =
    (
      match src with
    | `Later (e1, e2) ->
      print_edge e1 ev "L";
      print_edge e2 ev "L"
    | `Seq (ev', a) ->
      let label = match a with
      | `Cycles n -> Printf.sprintf "#%d" n
      | `Send _ -> "S"
      | `Recv _ -> "R"
      | `Choice _ -> "IC"
      | `Sync _ -> "G"
      in
      print_edge ev' ev label
    | `Branch (_, br_info) ->
      List.iter (fun e ->
        print_edge e ev "B"
      ) br_info.branches_val
    | `Root None -> ()
    | `Root (Some (ev', br_side_info)) ->
      let ev_has_imm_act = List.find_opt (fun a ->
        match a.Lang.d with
        | ImmediateRecv _ | ImmediateSend _ -> true
        | _ -> false
      ) ev.actions in
      if Option.is_some ev_has_imm_act then
        print_edge ev' ev "Imm"
      else
      print_edge ev' ev @@ string_of_int br_side_info.branch_side_sel
    | `Recurse (source, id) ->
      print_src_edge source;
      let rec_ev = List.find (fun e -> e.id = id) g.events in
      print_edge rec_ev ev ("ϵ")
    | `Select (e, msg_group) ->
      print_edge e ev (Printf.sprintf "?{%s}" (String.concat ";" (List.map Lang.string_of_msg_spec msg_group)))
    | `SelectJoin join_info ->
      List.iter (fun e ->
        print_edge e ev "?J"
      ) join_info.join_nodes
    ) in
    print_src_edge ev.source
  ) g.events;
  Printf.fprintf out "}\n";
  Printf.fprintf out "// END GRAPH WITH SESSION TYPES IN DOT FORMAT\n"

let find_last_event g =
  List.find (
    fun e ->
      e.is_loop_terminal
  ) g.events

let string_of_actions action = 
  match action with
  | DebugPrint _ -> "DebugPrint"
  | DebugFinish -> "DebugFinish"
  | RegAssign _ -> "RegAssign"
  | PutShared _ -> "PutShared"
  | ImmediateRecv _ -> "ImmediateRecv"
  | ImmediateSend _ -> "ImmediateSend"


let print_paths paths = 

List.iter (fun p -> 
                      Printf.eprintf "Path: ";
                      List.iter (fun id -> Printf.eprintf "%d " id) p;
                      Printf.eprintf "\n"
                    ) paths
