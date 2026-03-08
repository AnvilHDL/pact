open EventGraph
open EventGraphOps
open Lang
open GraphBuildContext
open DataTypeCheck

type build_context = Typing.build_context
module BuildContext = Typing.BuildContext

let unwrap_or_err err_msg err_span opt =
  match opt with
  | Some d -> d
  | None -> raise (event_graph_error_default err_msg err_span)

let do_sanity_check_offer (msg_list : (message_specifier * message_def) list) (span : code_span)  =

List.iter (fun ((msg_spec : message_specifier), message_def) ->
  if message_def.dir == Out && message_def.handshake_mode != ValidReady then
    raise (Except.TypeError [Text ("In exclusive offer: Outbound message " ^ msg_spec.msg ^ " must use ready/valid handshake");
      Except.codespan_local span])
  else if message_def.dir == Inp && message_def.handshake_mode != ValidAck then
    raise (Except.TypeError [Text ("In exclusive offer: Inbound message " ^ msg_spec.msg ^ " must use valid/ack handshake");
      Except.codespan_local span])
  ) msg_list



let binop_td_const graph (ci:cunit_info) _ctx span op n td =
  let w = unwrap_or_err "Invalid value" span td.ld.w in
  let sz = TypedefMap.data_type_size ci.typedefs ci.macro_defs td.ld.dtype in
  let sz' = match op with
  | Add -> sz+1
  | Mul -> sz + Utils.int_log2 n
  | _ -> sz in
  let (wires', w') = if sz' > sz then
    let (wires', padding) = WireCollection.add_literal graph.thread_id
      ci.typedefs ci.macro_defs (Lang.WithLength (sz' - sz, 0)) graph.wires in
    WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [padding; w] wires'
  else (graph.wires, w) in
  let (wires'', wconst) = WireCollection.add_literal graph.thread_id
     ci.typedefs ci.macro_defs (WithLength (sz', n)) wires' in
  let (wires''', wres) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs op w' (`Single wconst) wires'' in
  graph.wires <- wires''';
  {ld ={td.ld with w = Some wres; dtype = `Array (`Logic, ParamEnv.Concrete sz')}}


let binop_td_td graph (ci:cunit_info) ctx span op td1 td2 =
  let w1 = unwrap_or_err "Invalid value" span td1.ld.w in
  let w2 = unwrap_or_err "Invalid value" span td2.ld.w in
  let sz1 = TypedefMap.data_type_size ci.typedefs ci.macro_defs td1.ld.dtype
  and sz2 = TypedefMap.data_type_size ci.typedefs ci.macro_defs td2.ld.dtype in
  let sz' = match op with
  | Add -> (max sz1 sz2) +1
  | Mul -> sz1 + sz2
  | _ -> max sz1 sz2 in
  let (wires', w1') = if sz' > sz1 then
    let (wires', padding) = WireCollection.add_literal graph.thread_id
    ci.typedefs ci.macro_defs (Lang.WithLength (sz' - sz1, 0)) graph.wires in
    WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [padding; w1] wires'
  else (graph.wires, w1) in
  let (wires', w2') = if sz' > sz2 then
    let (wires', padding) = WireCollection.add_literal graph.thread_id
    ci.typedefs ci.macro_defs (Lang.WithLength (sz' - sz2, 0)) wires' in
    WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [padding; w2] wires'
  else (wires', w2) in
  let (wires', wres) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs op w1' (`Single w2') wires' in
  graph.wires <- wires';
  let open Typing in
  let new_dtype = (`Array (`Logic, ParamEnv.Concrete sz')) in
  Typing.merged_data graph (Some wres) new_dtype ctx.current [td1.ld; td2.ld]


let rec lvalue_info_of graph (ci:cunit_info) ctx span lval =
  let binop_td_const = binop_td_const graph ci ctx span
  and binop_td_td = binop_td_td graph ci ctx span in
  match lval with
  | Reg ident ->
    let r = Utils.StringMap.find_opt ident graph.regs
      |> unwrap_or_err ("Undefined register " ^ ident) span in
    let sz = TypedefMap.data_type_size ci.typedefs ci.macro_defs r.d_type in
    {
      lval_range = full_reg_range ident sz;
      lval_dtype = r.d_type
    }
  | Indexed (lval', idx) ->
    (* TODO: better code reuse *)
    let lval_info' = lvalue_info_of graph ci ctx span lval' in
    let (le', _len') = lval_info'.lval_range.subreg_range_interval in
    let (le, len, dtype) =
      TypedefMap.data_type_index ci.typedefs ci.macro_defs
        (construct_graphIR graph ci ctx)
        (binop_td_const Mul)
        lval_info'.lval_dtype idx
      |> unwrap_or_err "Invalid lvalue indexing" span in
    let le'_nd = MaybeConst.map (fun ld -> {ld}) le' in
    let le_n = MaybeConst.map (fun nd -> nd.ld)
      (MaybeConst.add (binop_td_const Add) (binop_td_td Add) le'_nd le)
    in
    {
      lval_range = {lval_info'.lval_range with subreg_range_interval = (le_n, len)};
      lval_dtype = dtype
    }
  | Indirected (lval', fieldname) ->
    let lval_info' = lvalue_info_of graph ci ctx span lval' in
    let (le', _len') = lval_info'.lval_range.subreg_range_interval in
    let (le, len, dtype) = TypedefMap.data_type_indirect ci.typedefs ci.macro_defs lval_info'.lval_dtype fieldname
      |> unwrap_or_err ("Invalid lvalue indirection through field " ^ fieldname) span in
    let le'_nd = MaybeConst.map (fun ld -> {ld}) le' in
    let le_n = MaybeConst.map (fun nd -> nd.ld)
      (MaybeConst.add_const le (binop_td_const Add) le'_nd)
    in
    {
      lval_range = {lval_info'.lval_range with subreg_range_interval = (le_n, len)};
      lval_dtype = dtype
    }

and construct_graphIR (graph : event_graph) (ci : cunit_info)
                    (ctx : build_context) (e : expr_node) : node_data =
  let binop_td_const = binop_td_const graph ci ctx
  and _binop_td_td = binop_td_td graph ci ctx in
  match e.d with
  | Literal lit ->
    let (wires', w) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs lit graph.wires in
    graph.wires <- wires';
    Typing.const_data graph (Some w) (dtype_of_literal lit :> data_type) ctx.current
  | Sync ident ->
    (
      let shared_info = Hashtbl.find_opt ctx.shared_vars_info ident
        |> unwrap_or_err ("Undefined identifier: " ^ ident) e.span in
      Typing.sync_event_data graph ident shared_info.value ctx.current
    )
  | Identifier ident ->
      let ctx_val = Typing.context_lookup ctx.cg_lt_ctx ident in
      let macro_val = List.assoc_opt ident (List.map (fun (macro : macro_def) ->(macro.id, macro.value)) ci.macro_defs) in
      (match ctx_val, macro_val with
        | Some _, Some _ ->
          raise (event_graph_error_default ("Conflicting Identifier " ^ ident ^ " declarations found") e.span)
        | Some binding, None -> Typing.use_binding binding |> Typing.sync_data  graph ctx.current
        | None, Some value ->
          let sz = Utils.int_log2 (value + 1) in
          let (wires', w) = WireCollection.add_literal graph.thread_id
              ci.typedefs ci.macro_defs
              (WithLength (sz, value)) graph.wires in
            graph.wires <- wires';
            Typing.const_data graph (Some w) (`Array (`Logic, ParamEnv.Concrete sz)) ctx.current
        | None, None ->
          Typing.context_lookup ctx.cg_lt_ctx ident
          |> unwrap_or_err ("Undefined identifier: " ^ ident) e.span
          |> Typing.use_binding |> Typing.sync_data graph ctx.current
      )

  | Assign (lval, e') ->
    let td = construct_graphIR graph ci ctx e' in
    let lvi = lvalue_info_of graph ci ctx e.span lval in
    let err_string = DTypeCheck.fmt_assign lval lvi.lval_dtype td.ld.dtype in
    check_dtype err_string (Some lvi.lval_dtype) td.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
    ctx.current.actions <- (RegAssign (lvi, td.ld) |> tag_with_span e.span)::ctx.current.actions;
    Typing.cycles_data graph 1 ctx.current
  | Call (id, arg_list) ->
      let func = List.find_opt (fun (f: Lang.func_def) -> f.name = id) ci.func_defs
        |> unwrap_or_err ("Undefined function: " ^ id) e.span in
      let td_args = List.map (construct_graphIR graph ci ctx) arg_list in
      let ctx' = BuildContext.clear_bindings ctx |> ref in
      if List.length td_args <> List.length func.args then
        raise (event_graph_error_default "Arguments missing in function call" e.span);
        List.iter2 (fun td arg ->
        (
          let _ = td.ld.w in (* added for tc*)
          match arg.arg_type with
            | Some gtype ->
              let err_string = DTypeCheck.fmt_func_arg id arg.arg_name gtype td.ld.dtype in
              check_dtype err_string (Some gtype) td.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            | None -> ()
        );
        ctx' := BuildContext.add_binding !ctx' arg.arg_name td.ld
      ) td_args func.args;
      construct_graphIR graph ci !ctx' func.body
  | Binop (binop, e1, e2) ->
    (
      let td1 = construct_graphIR graph ci ctx e1 in
      let w1 = unwrap_or_err "Invalid value" e1.span td1.ld.w in
      match e2 with
      | `List ws2 ->
        let td2_list = List.map (fun e2 ->
          let td2 = construct_graphIR graph ci ctx e2 in
          td2
        ) ws2 in
        let w2_list = List.map (fun td2 ->
          unwrap_or_err "Invalid value of second operator" e1.span td2.ld.w
        ) td2_list in
        let (wires', w) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs binop w1 (`List w2_list) graph.wires in
        graph.wires <- wires';
        let new_dtype = `Array (`Logic, ParamEnv.Concrete w.size) in
        Typing.merged_data graph (Some w) new_dtype ctx.current (List.concat [[td1.ld]; List.map (fun td -> td.ld) td2_list])
      | `Single e ->
        let td2 = construct_graphIR graph ci ctx e in
        let w2 = unwrap_or_err "Invalid value of second operator" e1.span td2.ld.w in
        let (wires', w) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs binop w1 (`Single w2) graph.wires in
        graph.wires <- wires';
        let err_string = DTypeCheck.fmt_binop binop td1.ld.dtype td2.ld.dtype in
        check_dtype err_string (Some td1.ld.dtype) td2.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        
        let new_dtype = match binop with
        | LAnd | LOr | Lt | Gt | Lte | Gte | Eq | Neq ->
          `Logic
        | _ ->
          td1.ld.dtype
        in 
        
        Typing.merged_data graph (Some w) new_dtype ctx.current [td1.ld; td2.ld]
    )
  | Unop (unop, e') ->
    let td = construct_graphIR graph ci ctx e' in
    let w' = unwrap_or_err "Invalid value" e'.span td.ld.w in
    let (wires', w) = WireCollection.add_unary graph.thread_id ci.typedefs unop w' graph.wires in
    graph.wires <- wires';
    Typing.derived_data (Some w) td.ld
  | Tuple [] -> Typing.const_data graph None (unit_dtype) ctx.current
  | Let (_idents, _, e) ->

    raise (Except.TypeError [Text ("Let expressions cannot be unused! "^(string_of_expr e.d)); Except.codespan_local e.span])
  | Join (e1, e2) ->
    (
      match e1.d with
      | Let (["_"], dtype, inner_e) ->
        let td1 = construct_graphIR graph ci ctx inner_e in
        let err_string = DTypeCheck.fmt_simple td1.ld.dtype in
        check_dtype err_string dtype td1.ld.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let td = construct_graphIR graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.ld.lt td.ld.lt in
        {ld = {td.ld with lt}} (* forcing the bound value to be awaited *)
      | Let ([], dtype, inner_e) ->
        let td1 = construct_graphIR graph ci ctx inner_e in
        let err_string = DTypeCheck.fmt_mismatch_opt ~context:"Invalid data type" ~expected:dtype ~got:td1.ld.dtype in
        check_dtype err_string dtype td1.ld.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let td = construct_graphIR graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.ld.lt td.ld.lt in
        {ld = {td.ld with lt}} (* forcing the bound value to be awaited *)
      | Let ([ident], dtype, inner_e) ->
          let td1 = construct_graphIR graph ci ctx inner_e in
          let err_string = DTypeCheck.fmt_let_binding ident dtype td1.ld.dtype in
          check_dtype err_string dtype td1.ld.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
          let ctx' = BuildContext.add_binding ctx ident td1.ld in
          let td = construct_graphIR graph ci ctx' e2 in
          (* check if the binding is used *)
          let binding = Typing.context_lookup ctx'.cg_lt_ctx ident |> Option.get in
          (* no need to wait if the value is current *)
          if td1.ld.lt.live.id <> ctx.current.id && not binding.binding_used then (
            (* raise (event_graph_error_default "Value is potentially not awaited!" e1.span) *)
            Printf.eprintf "[Warning] Value bound to %s is potentially not awaited!\n" ident;
            (SpanPrinter.print_code_span ~indent:2 ~trunc:(-5) stderr ci.file_name e1.span)
          ;
          );
          td
      | Let _ -> raise (event_graph_error_default "Discarding expression results!" e.span)
      | _ ->
        let td1 = construct_graphIR graph ci ctx e1 in
        let td = construct_graphIR graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.ld.lt td.ld.lt in
        {ld = {td.ld with lt}} (* forcing the bound value to be awaited *)
    )
  | Wait (e1, e2) ->
    (
      match e1.d with
      | Let (["_"], dtype, inner_e) ->
        let td1 = construct_graphIR graph ci ctx inner_e in
        let err_string = DTypeCheck.fmt_simple td1.ld.dtype in
        check_dtype err_string dtype td1.ld.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let ctx' = BuildContext.wait graph ctx td1.ld.lt.live in
        construct_graphIR graph ci ctx' e2
      | Let ([], dtype, inner_e) ->
        let td1 = construct_graphIR graph ci ctx inner_e in
        let err_string = DTypeCheck.fmt_simple td1.ld.dtype in
        check_dtype err_string dtype td1.ld.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let ctx' = BuildContext.wait graph ctx td1.ld.lt.live in
        construct_graphIR graph ci ctx' e2
      | Let ([ident], dtype, inner_e) ->
        let td1 = construct_graphIR graph ci ctx inner_e in
        let err_string = DTypeCheck.fmt_let_binding ident dtype td1.ld.dtype in
        check_dtype err_string dtype td1.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        (* add the binding to the context *)
        let ctx' = BuildContext.wait graph ctx td1.ld.lt.live in
        let ctx' = BuildContext.add_binding ctx' ident td1.ld in
        construct_graphIR graph ci ctx' e2
      | Let _ -> raise (event_graph_error_default "Discarding expression results!" e.span)
      | _ ->
        let td1 = construct_graphIR graph ci ctx e1 in
        let ctx' = BuildContext.wait graph ctx td1.ld.lt.live in
        construct_graphIR graph ci ctx' e2
    )
  | Ready msg_spec ->
    let _ = MessageCollection.lookup_message graph.messages msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in ready" e.span in
    (* if msg.dir <> In then (
      (* mismatching direction *)
      raise (event_graph_error_default "Mismatching message direction!" e.span)
    ); *)
    let wires, msg_valid_port = WireCollection.add_msg_valid_port graph.thread_id ci.typedefs msg_spec graph.wires in
    graph.wires <- wires;
    Typing.immediate_data graph (Some msg_valid_port) `Logic ctx.current
  | Probe msg_spec ->
    let m = MessageCollection.lookup_message graph.messages msg_spec ci.channel_classes
    |> unwrap_or_err "Invalid message specifier in probe" e.span in
    let wires, msg_ack_port = if m.handshake_mode = Lang.ValidReady then (
      WireCollection.add_msg_ready_port graph.thread_id ci.typedefs msg_spec graph.wires
    )
    else WireCollection.add_msg_ack_port graph.thread_id ci.typedefs msg_spec graph.wires in
    graph.wires <- wires;
    Typing.immediate_data graph (Some msg_ack_port) `Logic ctx.current
  | Cycle n -> Typing.cycles_data graph n ctx.current
  | IfExpr (e1, e2, e3) ->
    let td1 = construct_graphIR graph ci ctx e1 in
    (* TODO: type checking *)
    let w1 = unwrap_or_err "Invalid condition" e1.span td1.ld.w in
    let ctx' = BuildContext.wait graph ctx td1.ld.lt.live in
    let branch_info = {
      branch_cond_v = td1.ld;
      branch_cond = TrueFalse;
      branch_count = 2; (* for if-else *)
      branches_to = [];
      branches_val = [];
    } in

    let (br_side_true, ctx_true) = BuildContext.branch_side graph ctx' branch_info 0 in
    let td2 = construct_graphIR graph ci ctx_true e2 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx' branch_info 1 in
    let td3 = construct_graphIR graph ci ctx_false e3 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td2.ld.lt.live; td3.ld.lt.live];

    BuildContext.branch_merge ctx' [ctx_true; ctx_false];

    let ctx_br = BuildContext.branch graph ctx' branch_info ci.file_name in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.ld.lt.dead td2.ld.lt.dead |> Utils.list_unordered_join td3.ld.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.ld.reg_borrows td2.ld.reg_borrows |> Utils.list_unordered_join td3.ld.reg_borrows in
    (
      match td2.ld.w, td3.ld.w with
      | None, None -> {ld = {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}}
      | Some w2, Some w3 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w1, w2)] w3 graph.wires in
        graph.wires <- wires';
        {ld = {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.ld.dtype}}
      | _ -> raise (event_graph_error_default "Invalid if expression!" e.span)
    )
  | TrySend (send_pack, e1, e2) ->
    (* data to send *)
    let msg = MessageCollection.lookup_message graph.messages send_pack.send_msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in try send" e.span in
    let td_send_data = construct_graphIR graph ci ctx send_pack.send_data in
    let wires, w_cond =
      if msg.handshake_mode <> Lang.ValidAck then
        WireCollection.add_msg_ack_port graph.thread_id ci.typedefs send_pack.send_msg_spec graph.wires
      else
        WireCollection.add_msg_ack_port graph.thread_id ci.typedefs send_pack.send_msg_spec graph.wires
    in
    let td_cond = {
      w = Some w_cond;
      lt = {live = ctx.current; dead = [(ctx.current, `Cycles 1)]};
      reg_borrows = [];
      dtype = `Logic;
    } in
    graph.wires <- wires;

    (* TODO: dedup *)
    let branch_info = {
      branch_cond_v = td_cond;
      branch_cond = TrueFalse;
      branch_count = 2;
      branches_to = [];
      branches_val = [];
    } in

    let (br_side_true, ctx_true) = BuildContext.branch_side graph ctx branch_info 0 in
    let td1 = construct_graphIR graph ci ctx_true e1 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx branch_info 1 in
    let td2 = construct_graphIR graph ci ctx_false e2 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td1.ld.lt.live; td2.ld.lt.live];

    BuildContext.branch_merge ctx [ctx_true; ctx_false];

    ctx_true.current.actions <- (ImmediateSend (send_pack.send_msg_spec, td_send_data.ld) |> tag_with_span e.span)::ctx_true.current.actions;

    let ctx_br = BuildContext.branch graph ctx branch_info ci.file_name in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.ld.lt.dead td2.ld.lt.dead |> Utils.list_unordered_join td_cond.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.ld.reg_borrows td2.ld.reg_borrows |> Utils.list_unordered_join td_cond.reg_borrows in
    (
      match td1.ld.w, td2.ld.w with
      | None, None -> {ld = {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}}
      | Some w1, Some w2 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w_cond, w1)] w2 graph.wires in
        graph.wires <- wires';
        {ld = {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.ld.dtype}}
      | _ -> raise (event_graph_error_default "Invalid try send expression!" e.span)
    )
  | TryRecv (ident, recv_pack, e1, e2) ->
    let wires, w_cond = WireCollection.add_msg_valid_port graph.thread_id ci.typedefs recv_pack.recv_msg_spec graph.wires in
    let td_cond = {
      w = Some w_cond;
      lt = {live = ctx.current; dead = [(ctx.current, `Cycles 1)]};
      reg_borrows = [];
      dtype = `Logic; 
    } in
    graph.wires <- wires;

    (* TODO: dedup *)
    let branch_info = {
      branch_cond_v = td_cond;
      branch_cond = TrueFalse;
      branch_count = 2;
      branches_to = [];
      branches_val = [];
    } in

    let (br_side_true, ctx_true_no_binding) = BuildContext.branch_side graph ctx branch_info 0 in

    (* message *)
    let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in try receive" e.span in
    let (wires', w_recv) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
    graph.wires <- wires';
    let stype = List.hd msg.sig_types in
    let d_recv = delay_pat_globalise recv_pack.recv_msg_spec.endpoint stype.lifetime.e in
    let td_recv = {
      w = w_recv;
      lt = {live = ctx_true_no_binding.current; dead = [(ctx_true_no_binding.current, d_recv)]};
      reg_borrows = [];
      dtype = stype.dtype;
    } in
    let ctx_true = BuildContext.add_binding ctx_true_no_binding ident td_recv in
    let td1 = construct_graphIR graph ci ctx_true e1 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx branch_info 1 in
    let td2 = construct_graphIR graph ci ctx_false e2 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td1.ld.lt.live; td2.ld.lt.live];

    BuildContext.branch_merge ctx [ctx_true_no_binding; ctx_false];

    ctx_true.current.actions <- (ImmediateRecv recv_pack.recv_msg_spec |> tag_with_span e.span)::ctx_true.current.actions;

    let ctx_br = BuildContext.branch graph ctx branch_info ci.file_name in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.ld.lt.dead td2.ld.lt.dead |> Utils.list_unordered_join td_cond.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.ld.reg_borrows td2.ld.reg_borrows |> Utils.list_unordered_join td_cond.reg_borrows in
    (
      match td1.ld.w, td2.ld.w with
      | None, None -> {ld = {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}}
      | Some w1, Some w2 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w_cond, w1)] w2 graph.wires in
        graph.wires <- wires';
        {ld = {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.ld.dtype}}
      | _ -> raise (event_graph_error_default "Invalid try recv expression!" e.span)
    )

  | Match (match_v, match_arms) ->
    let td_v = construct_graphIR graph ci ctx match_v in
    let w_v = unwrap_or_err "Invalid match expression" match_v.span td_v.ld.w in
    let ctx' = BuildContext.wait graph ctx td_v.ld.lt.live in
    let branch_info = {
      branch_cond_v = td_v.ld;
      branch_cond = MatchCases [];
      branch_count = List.length match_arms;
      branches_to = [];
      branches_val = [];
    } in

    let (default_arms, match_arms) =
      List.partition (fun ((pat, _) : expr_node * expr_node option) -> pat.d = Identifier "_") match_arms in
    (
      match default_arms with
      | [default_arm] ->
        let td_pats = List.map (fun (pat, _) -> construct_graphIR graph ci ctx' pat) match_arms in
        (* make sure that the patterns are all constants *)
        List.iter2
          (fun ((pat, _) : expr_node * expr_node option) td ->
            let valid =
              match td.ld.w with
              | None -> false
              | Some w -> w.is_const
            in
            if not valid then
              raise (event_graph_error_default "Match patterns must be constant values!" pat.span)
          ) match_arms td_pats;

        (* build bodies *)
        let branches = List.mapi
          (fun idx (_, body) ->
            let (br_side, ctx) = BuildContext.branch_side graph ctx' branch_info idx in
            let td = construct_graphIR graph ci ctx @@ Option.get body in
            ((ctx, br_side, td), (ctx.current, td.ld.lt.live))
          )
          match_arms
        in
        let (br_side_default, ctx_default) = BuildContext.branch_side graph ctx' branch_info (branch_info.branch_count - 1) in
        let td_default = construct_graphIR graph ci ctx_default @@ Option.get @@ snd default_arm in

        let (branches, branches_events) = List.split branches in
        let (branches_to, branches_val) = List.split branches_events in
        branch_info.branches_to <- branches_to @ [ctx_default.current];
        branch_info.branches_val <- branches_val @ [td_default.ld.lt.live];

        BuildContext.branch_merge ctx' @@ ctx_default::(List.map (fun (ctx, _, _) -> ctx) branches);
        let ctx_br = BuildContext.branch graph ctx' branch_info ci.file_name in
        List.iter
          (fun (_, br_side, _) ->
            br_side.branch_event <- Some ctx_br.current
          )
          branches;
        br_side_default.branch_event <- Some ctx_br.current;
        let lt = {
          live = ctx_br.current;
          dead = List.fold_left (fun l (_, _, td) -> Utils.list_unordered_join l td.ld.lt.dead) td_v.ld.lt.dead branches;
        } in
        let reg_borrows' = List.fold_left (fun l (_, _, td) -> Utils.list_unordered_join l td.ld.reg_borrows) td_v.ld.reg_borrows branches in
        branch_info.branch_cond <- MatchCases (List.map (fun td -> td.ld) td_pats);
        if List.for_all (fun (_, _, td_val) -> Option.is_none td_val.ld.w) branches then
          {ld = {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}}
        else (
          let (wires', w) = WireCollection.add_cases graph.thread_id ci.typedefs w_v
            (List.map2 (fun td_pat (_, _, td_val) -> (Option.get td_pat.ld.w, Option.get td_val.ld.w)) td_pats branches) (match td_default.ld.w with | Some w -> w | None -> raise (event_graph_error_default "Invalid match expression (exactly one default case expected)!" e.span))
            graph.wires in
          graph.wires <- wires';
          {ld = {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td_default.ld.dtype}}
        )
      | _ -> raise @@ event_graph_error_default "Invalid match expression (atleast one default case expected)!" e.span
    )
  | Cast (e', dtype) ->
    let td = construct_graphIR graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in cast" e'.span td.ld.w in
    let target_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs dtype in
    if w.size > target_size then (
      (* Truncate: take slice of the wire to match target size *)
      let base_i = MaybeConst.Const 0 in
      let wires', w' = WireCollection.add_slice graph.thread_id w base_i target_size graph.wires in
      graph.wires <- wires';
      Typing.merged_data graph (Some w') dtype ctx.current [td.ld]
    ) else if w.size < target_size then (
      (* Extend: pad with zeros to match target size *)
      let pad_len = target_size - w.size in
      let wires', pad_w = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (pad_len, 0)) graph.wires in
      let wires', w' = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [pad_w; w] wires' in
      graph.wires <- wires';
      Typing.merged_data graph (Some w') dtype ctx.current [td.ld]
    ) else (
      (* Sizes match, just update type *)
      Typing.merged_data graph (Some w) dtype ctx.current [td.ld]
    )
  | Concat (es, is_flat) ->
    let tds = List.map (fun e' -> (e', construct_graphIR graph ci ctx e')) es in
    let ws = List.map (fun ((e', td) : expr_node * node_data) -> unwrap_or_err "Invalid value in concat" e'.span td.ld.w) tds in
    let (wires', w) = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs ws graph.wires in
    graph.wires <- wires';
    let tdtype = List.map (fun ((_, td): expr_node * node_data) -> td.ld.dtype) tds in
    let is_flat_logic = List.for_all (fun d -> match d with | `Logic | `Array (`Logic, _) -> true | _ -> false) tdtype in
    let eff_is_flat = is_flat || is_flat_logic in
    if not (List.for_all (fun d -> d = List.hd tdtype) tdtype) && (not eff_is_flat) then
      raise (Except.TypeError [Text ("In concat: Incompatible types: " ^ (String.concat ", " (List.map string_of_data_type tdtype))); Except.codespan_local e.span]);
    let new_dtype = ( 
      match eff_is_flat with 
      | false -> `Array (List.hd tdtype, ParamEnv.Concrete (List.length es))
      | _ -> `Array (`Logic, ParamEnv.Concrete (w.size))
    ) in
    List.map (fun (_,td) -> td.ld) tds |> Typing.merged_data graph (Some w) new_dtype ctx.current
  |  Read rlval ->
    let reg_ident = Lang.get_lvalue_reg_id rlval in
    let r = Utils.StringMap.find_opt reg_ident graph.regs
      |> unwrap_or_err ("Undefined register " ^ reg_ident) e.span in    
    let (wires'', w'') = WireCollection.add_reg_read graph.thread_id ci.typedefs ci.macro_defs r graph.wires in
    graph.wires <- wires'';
    let td = {ld = {w = Some w''; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = r.d_type}} in
    let get_borrow_info in_off le dt w lval td' =
      match lval with 
        | Reg _ -> (dt,in_off,le,w,td')
        | Indexed (lv, idx) ->
          let inner_info = lvalue_info_of graph ci ctx e.span lv in
          let inner_le = fst inner_info.lval_range.subreg_range_interval in
          let inner_le_nd = MaybeConst.map (fun ld -> {ld}) inner_le in
          let inner_dtype = inner_info.lval_dtype in
          let (offset_le, len, dt') = TypedefMap.data_type_index ci.typedefs ci.macro_defs
            (construct_graphIR graph ci ctx)
            (binop_td_const e.span Mul)
            inner_dtype idx |> unwrap_or_err (Printf.sprintf "Invalid indexing %s for datatype %s" (string_of_index idx) (Lang.string_of_data_type inner_dtype)) e.span in
          let total_offset_le = MaybeConst.add (binop_td_const e.span Add) (_binop_td_td e.span Add) offset_le inner_le_nd in
          let off_i = MaybeConst.map_off total_offset_le in
          let (off, le') = if off_i < 0 then (
            Printf.eprintf "[Warning] The offset is not a constant value for %s, borrowing full range\n" reg_ident;
            (0, len)
          ) else (off_i, len) in
          let (wire', w') = WireCollection.add_slice graph.thread_id w (MaybeConst.map (fun td -> unwrap_or_err "Invalid indexing in lvalue" e.span td.ld.w) total_offset_le) le' graph.wires in
          graph.wires <- wire';
          let new_td = match total_offset_le with
            | MaybeConst.NonConst td_offset -> Typing.merged_data graph (Some w') dt' ctx.current [td'.ld; td_offset.ld]
            | MaybeConst.Const _ -> {ld = {td'.ld with w = Some w'; dtype = dt'}}
          in
          (dt', off, le', w', new_td)
        | Indirected (lval_inner, field_id) -> 
          let lval_info_inner = lvalue_info_of graph ci ctx e.span lval_inner in
          let (inner_le, _inner_len) = lval_info_inner.lval_range.subreg_range_interval in
          let inner_le_nd = MaybeConst.map (fun ld -> {ld}) inner_le in
          let (field_offset_le, len, new_dtype) = TypedefMap.data_type_indirect ci.typedefs ci.macro_defs lval_info_inner.lval_dtype field_id
            |> unwrap_or_err (Printf.sprintf "Invalid indirection %s" field_id) e.span in
          (* total offset = inner offset + field offset *)
          let total_offset_le = MaybeConst.add_const field_offset_le (binop_td_const e.span Add) inner_le_nd in
          let off_i = MaybeConst.map_off total_offset_le in
          let (off, le') = if off_i < 0 then (
            Printf.eprintf "[Warning] The offset is not a constant value for indirection %s, borrowing full range\n" field_id;
            (0, len)
          ) else (off_i, len) in
          let (wi', new_w) = WireCollection.add_slice graph.thread_id w (MaybeConst.map (fun td -> unwrap_or_err "Invalid indexing in indirection" e.span td.ld.w) total_offset_le) le' graph.wires in
          graph.wires <- wi';
          let new_td = match total_offset_le with
            | MaybeConst.Const _ -> {ld = {td'.ld with w = Some new_w; dtype = new_dtype}}
            | MaybeConst.NonConst td_offset -> Typing.merged_data graph (Some new_w) new_dtype ctx.current [td'.ld; td_offset.ld]
          in
          (new_dtype, off, le', new_w, new_td)
    in
    let full_sz = TypedefMap.data_type_size ci.typedefs ci.macro_defs r.d_type in
    let (_dt,off,le,_w,td'') = get_borrow_info 0 full_sz r.d_type w'' rlval td in
    let borrow = {borrow_range = sub_reg_range reg_ident off le; borrow_start = ctx.current; borrow_source_span = e.span} in
    {ld = { td''.ld with dtype = _dt; reg_borrows = borrow :: td''.ld.reg_borrows }}
  | Debug op ->
    (
      match op with
      | DebugPrint (s, e_list) ->
        let timed_ws = List.map (construct_graphIR graph ci ctx) e_list in
        let all_w = List.for_all(
          fun td ->
            match td.ld.w with
            | Some _ -> true
            | None -> false
        ) timed_ws in 
        if not all_w then
          raise (Except.TypeError [Text "Invalid value in debug print"; Except.codespan_local e.span]);
        ctx.current.actions <- (let open EventGraph in DebugPrint (s, List.map (fun td -> td.ld) timed_ws) |> tag_with_span e.span)::ctx.current.actions;
        {ld = {w = None; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = unit_dtype}}
      | DebugFinish ->
        ctx.current.actions <- (let open EventGraph in tag_with_span e.span DebugFinish)::ctx.current.actions;
        {ld = {w = None; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = unit_dtype}}
    )
  | Send send_pack ->
    (* just check that the endpoint and the message type is defined *)
    let ep  = send_pack.send_msg_spec.endpoint in
    if not (MessageCollection.endpoint_owned graph.messages ep) then
      raise (event_graph_error_default (Printf.sprintf "Endpoint %s not owned by the process" ep) e.span);
    let msg = MessageCollection.lookup_message graph.messages send_pack.send_msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in send" e.span in
    if msg.dir <> Out then (
      (* mismatching direction *)
      raise (event_graph_error_default "Mismatching message direction!" e.span)
    );
    (* evaluates send pack to data *)
    let td = construct_graphIR graph ci ctx send_pack.send_data in
    let msg_dtype = (List.hd msg.sig_types).dtype in
    let err_string = DTypeCheck.fmt_send send_pack.send_msg_spec.endpoint msg_dtype td.ld.dtype in
    check_dtype err_string (Some msg_dtype) td.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
    let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx.current in
    ctx.current.sustained_actions <-
      ({
        until = ntd.ld.lt.live;
        ty = Send (send_pack.send_msg_spec, td.ld)
      } |> tag_with_span e.span)::ctx.current.sustained_actions;
    ntd
| Offer offer_arms ->
    let offer_msg_list = List.map (fun (offer_arm, _) ->
      match offer_arm with
      | OfferSend send_pack -> send_pack.send_msg_spec
      | OfferRecv (_, recv_pack) -> recv_pack.recv_msg_spec
      | OfferWildcard -> {endpoint = "*"; msg = "*"}
    ) offer_arms in

    let is_wildcard_present = List.exists (fun msg_spec ->
      msg_spec.endpoint = "*" && msg_spec.msg = "*"
    ) offer_msg_list in

    let offer_msg_list_filtered = List.filter (fun msg_spec ->
      msg_spec.endpoint <> "*" || msg_spec.msg <> "*"
    ) offer_msg_list in

    let msg_defs = List.map (fun msg_spec ->
      MessageCollection.lookup_message graph.messages msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in offer" e.span
    ) offer_msg_list_filtered in

    let msg_list = List.combine offer_msg_list_filtered msg_defs in

    (* do_sanity_check_offer msg_list e.span; *)

    let cond_td = Typing.offer_condition graph ctx offer_msg_list in
    let ctx = BuildContext.wait graph ctx cond_td.ld.lt.live in

    let offer_arm_filtered = List.filter (fun (offer_arm, _) ->
      match offer_arm with
      | OfferWildcard -> false
      | _ -> true
    ) offer_arms in

    let ctx',wildcard_info =  if is_wildcard_present then (
      let wildcard_arm_expr =
        List.find_map (fun (offer_arm, arm_expr) ->
          match offer_arm with
          | OfferWildcard -> Some arm_expr
          | _ -> None
        ) offer_arms
        |> unwrap_or_err "Wildcard arm not found" e.span
      in
      let branch_cond_wires = 
        List.map (fun (msg_spec,msg_def) ->
          if msg_def.dir = Inp then
            let (wires', msg_valid_port) = WireCollection.add_msg_valid_port graph.thread_id ci.typedefs msg_spec graph.wires in
            graph.wires <- wires';
            msg_valid_port
          else
            if msg_def.handshake_mode == Lang.ValidAck then
              let (wires', msg_ack_port) = WireCollection.add_msg_ack_port graph.thread_id ci.typedefs msg_spec graph.wires in
              graph.wires <- wires';
              msg_ack_port
            else
              let (wires', msg_ack_port) = WireCollection.add_msg_ready_port graph.thread_id ci.typedefs msg_spec graph.wires in
              graph.wires <- wires';
              msg_ack_port
        ) msg_list in

        let wildcard_branch_cond = 
          List.fold_left (fun acc w ->
            let (wires', new_w) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs Or acc (`Single w) graph.wires in
            graph.wires <- wires';
            new_w
          ) (List.hd branch_cond_wires) (List.tl branch_cond_wires)
        in 


        (* create negatition of this *)
        let wires,branch_cond_wire = WireCollection.add_unary graph.thread_id ci.typedefs Not wildcard_branch_cond graph.wires in
        graph.wires <- wires;

        let wire_td = Typing.immediate_data graph (Some branch_cond_wire) `Logic ctx.current in


          let outer_branch_info = {
          branch_cond_v = wire_td.ld;
          branch_cond = TrueFalse;
          branch_count = 2; (* wildcard arm and others *)
          branches_to = [];
          branches_val = [];
        } in
        let (br_side_true, ctx_wildcard) = BuildContext.branch_side graph ctx outer_branch_info 0 in
        let td_result = construct_graphIR graph ci ctx_wildcard wildcard_arm_expr in

      
        let (br_side_false, ctx_true) = BuildContext.branch_side graph ctx outer_branch_info 1 in
        outer_branch_info.branches_to <- [ctx_wildcard.current; ctx_true.current];
        outer_branch_info.branches_val <- [td_result.ld.lt.live];
        (ctx_true, Some (outer_branch_info, br_side_true, br_side_false, td_result,ctx_wildcard))
        (* Process the wildcard arm in the true branch *)
      )
      else(ctx ,None) in
    
    (* Create separate if-branches for each offer arm *)
    let branch_contexts_and_tds = List.mapi (fun idx (offer_arm, arm_expr) ->
      let (msg_spec, msg_def) = List.nth msg_list idx in
      
      (* Create condition wire for this branch *)
      let wire_td = if msg_def.dir = Inp then
        let (wires', msg_valid_port) = WireCollection.add_msg_valid_port graph.thread_id ci.typedefs msg_spec graph.wires in
        graph.wires <- wires';
        Typing.immediate_data graph (Some msg_valid_port) `Logic ctx'.current
      else
        if msg_def.handshake_mode == Lang.ValidAck then
          let (wires', msg_ack_port) = WireCollection.add_msg_ack_port graph.thread_id ci.typedefs msg_spec graph.wires in
          graph.wires <- wires';
          Typing.immediate_data graph (Some msg_ack_port) `Logic ctx'.current
        else
        let (wires', msg_ack_port) = WireCollection.add_msg_ready_port graph.thread_id ci.typedefs msg_spec graph.wires in
        graph.wires <- wires';
        Typing.immediate_data graph (Some msg_ack_port) `Logic ctx'.current
      in
      
      (* Create branch info for this specific arm *)
      let branch_info = {
        branch_cond_v = wire_td.ld;
        branch_cond = TrueFalse;
        branch_count = 2;
        branches_to = [];
        branches_val = [];
      } in
      
      let (br_side_true, ctx_branch) = BuildContext.branch_side graph ctx' branch_info 0 in
      
      (* Process the offer arm in the true branch *)
      let td_result = match offer_arm with
        | OfferSend send_pack ->
            let msg = MessageCollection.lookup_message graph.messages send_pack.send_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer send" e.span in
            if msg.dir <> Out then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let td_data = construct_graphIR graph ci ctx_branch send_pack.send_data in
            let msg_dtype = (List.hd msg.sig_types).dtype in
            let err_string = Printf.sprintf "In offer send: Invalid data type for message %s: expected %s but got %s"
              send_pack.send_msg_spec.endpoint (string_of_data_type msg_dtype) (string_of_data_type td_data.ld.dtype) in
            check_dtype err_string (Some msg_dtype) td_data.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            
            let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.ld.lt.live; ty = EventGraph.Send (send_pack.send_msg_spec, td_data.ld)} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            let ctx' = BuildContext.wait graph ctx_branch ntd.ld.lt.live in
            construct_graphIR graph ci ctx' arm_expr

        | OfferRecv (id, recv_pack) ->
            let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer receive" e.span in
            if msg.dir <> Inp then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let (wires', w) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
            graph.wires <- wires';
            let ntd = Typing.recv_msg_data graph w recv_pack.recv_msg_spec msg ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.ld.lt.live; ty = EventGraph.Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            
            let ctx_with_binding = BuildContext.add_binding ctx_branch id ntd.ld in
            let ctx' = BuildContext.wait graph ctx_with_binding ntd.ld.lt.live in
            construct_graphIR graph ci ctx' arm_expr
          | OfferWildcard ->
            raise (event_graph_error_default "Wildcard offer arm should have been filtered out!" e.span)
      in
      
      (* Create false branch (empty continuation) *)
      let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx' branch_info 1 in
      let td_false = Typing.const_data graph None unit_dtype ctx_false.current in
      
      (* Update branch info *)
      branch_info.branches_to <- [ctx_branch.current; ctx_false.current];
      branch_info.branches_val <- [td_result.ld.lt.live; td_false.ld.lt.live];
      
      BuildContext.branch_merge ctx' [ctx_branch; ctx_false];
      
      let ctx_br = BuildContext.branch graph ctx' branch_info ci.file_name in
      br_side_true.branch_event <- Some ctx_br.current;
      br_side_false.branch_event <- Some ctx_br.current;
      
      (ctx_br, td_result)
    ) offer_arm_filtered in

    (* Merge all branch contexts using Later *)
    (* let split3 lst =
      let rec aux l (acc1, acc2, acc3) =
        match l with
        | [] -> (List.rev acc1, List.rev acc2, List.rev acc3)
        | (x, y, z)::xs -> aux xs (x::acc1, y::acc2, z::acc3)
      in
      aux lst ([], [], [])
    in *)
    let (branch_ctxs, branch_tds) = List.split branch_contexts_and_tds in
    let merged_event = List.fold_left (fun (acc_event:event) (branch_ctx:build_context) ->
      if acc_event.is_recurse || branch_ctx.current.is_recurse then raise (Except.TypeError [Except.Text "Recursive types not supported in offer branch ends"; Except.codespan_local e.span]);
      Typing.event_create graph (`Later (acc_event, branch_ctx.current))
    ) (List.hd branch_ctxs).current (List.tl branch_ctxs) in
    
    (* Merge lifetimes and borrows from all branches *)
    let merged_dead = List.fold_left Utils.list_unordered_join 
      cond_td.ld.lt.dead (List.map (fun td -> td.ld.lt.dead) branch_tds) in
    let merged_borrows = List.fold_left Utils.list_unordered_join 
      [] (List.map (fun td -> td.ld.reg_borrows) branch_tds) in
    
    let lt = {live = merged_event; dead = merged_dead} in
    
    (* Use first branch's result as the representative *)
    let result_w = match branch_tds with
      | [] -> None
      | hd::_ -> hd.ld.w
    in
    let result_dtype = match branch_tds with
      | [] -> unit_dtype
      | hd::_ -> hd.ld.dtype
    in
    
    let td_false = {ld = {w = result_w; lt; reg_borrows = merged_borrows; dtype = result_dtype}} in
    if is_wildcard_present then (
      let (outer_branch_info, br_side_true, br_side_false, td_wildcard,ctx_wildcard) = Option.get wildcard_info in
      (* outer_branch_info.branches_to <- outer_branch_info.branches_to @ [merged_event]; *)
      outer_branch_info.branches_val <- outer_branch_info.branches_val @ [td_false.ld.lt.live];
      BuildContext.branch_merge ctx [ctx'; ctx_wildcard];
      let ctx_br = BuildContext.branch graph ctx' outer_branch_info ci.file_name in
      br_side_true.branch_event <- Some ctx_br.current;
      br_side_false.branch_event <- Some ctx_br.current;
      {ld = {w = td_false.ld.w; lt = {live = ctx_br.current; dead = Utils.list_unordered_join td_false.ld.lt.dead td_wildcard.ld.lt.dead}; reg_borrows = Utils.list_unordered_join td_false.ld.reg_borrows td_wildcard.ld.reg_borrows; dtype = td_false.ld.dtype}}
    ) else
      td_false
    
  | XOffer (offer_arms, state_selector) ->
    (* Create branches for each offer arm - all can start in parallel *)
    (* create a special condition node *)


    let offer_msg_list = List.map (fun (offer_arm, _) ->
      match offer_arm with
      | OfferSend send_pack -> send_pack.send_msg_spec
      | OfferRecv (_, recv_pack) -> recv_pack.recv_msg_spec
      | OfferWildcard -> {endpoint = "*"; msg = "*"}
    ) offer_arms in

    let offer_arm_filtered = List.filter (fun (offer_arm, _) ->
      match offer_arm with
      | OfferWildcard -> false
      | _ -> true
    ) offer_arms in

    let offer_msg_list_filtered = List.filter (fun msg_spec ->
      msg_spec.endpoint <> "*" || msg_spec.msg <> "*"
    ) offer_msg_list in

    let msg_defs = List.map (fun msg_spec ->
      MessageCollection.lookup_message graph.messages msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in offer" e.span
    ) offer_msg_list_filtered in

    let msg_list = List.combine offer_msg_list_filtered msg_defs in


    do_sanity_check_offer msg_list e.span;

    let cond_td = Typing.offer_condition graph ctx offer_msg_list in
    let ctx = BuildContext.wait graph ctx cond_td.ld.lt.live in
    
    (*==================== At this point one of the messages must have been received ==========================================================*)
    (* Now we match 1'd1 with respective valid ready port of branch conditions *)
    let length_offering = List.length offer_arms in
    let bit_len = (Utils.int_log2 length_offering) in

    let find_wire_ctx ct id =
      let binding = Typing.context_lookup ct id in
      let td = unwrap_or_err (Printf.sprintf "Could not find a binding for %s" id)  e.span binding in
      let w = unwrap_or_err (Printf.sprintf "No wire associated with this binding %s" id)  e.span td.binding_val.w in
      let bit_leni = (Utils.int_log2 (List.length offer_arm_filtered)) in
      if w.size <> bit_leni then
        raise (Except.TypeError [Except.Text (Printf.sprintf "State selector wire size mismatch: expected %d but got %d" bit_leni w.size); Except.codespan_local e.span])
      else
      (graph.wires, w)
    in

    let new_wires, sel_w = if Option.is_some state_selector then (find_wire_ctx ctx.cg_lt_ctx (Option.get state_selector)) else WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (bit_len, 0)) graph.wires in
    graph.wires <- new_wires;

let wire_list =
      List.fold_left (fun acc (msg_spec, msg_def) ->
        if msg_def.dir = Inp then
          let (wires', msg_valid_port) = WireCollection.add_msg_valid_port graph.thread_id ci.typedefs msg_spec graph.wires in
          graph.wires <- wires';
          acc @ [msg_valid_port]
        else
          let (wires', msg_ack_port) = WireCollection.add_msg_ready_port graph.thread_id ci.typedefs msg_spec graph.wires in
          graph.wires <- wires';
          acc @ [msg_ack_port]
      ) [] msg_list in
      let is_wildcard_present = List.exists (fun msg_spec ->
            msg_spec.endpoint = "*" && msg_spec.msg = "*"
      ) offer_msg_list in
      let updated_wire_list' =
        if is_wildcard_present && ((List.length wire_list) = 1)  then
          (
            let wires', ww = WireCollection.add_unary graph.thread_id ci.typedefs Not (List.hd wire_list) graph.wires in
            graph.wires <- wires';
            wire_list @ [ww]
          )
        else(
          let ww = List.fold_left (fun hd wire ->
            let (wires', new_wire) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs Or hd (`Single wire) graph.wires in
            graph.wires <- wires';
            new_wire
          ) (List.hd wire_list) (List.tl wire_list) in
          let wc,  ww_not = WireCollection.add_unary graph.thread_id ci.typedefs Not ww graph.wires in
          graph.wires <- wc;
          wire_list @ [ww_not]
        ) in

    let max_len = int_of_float (2. ** float_of_int bit_len) in
    let extended_zero_needed = max_len - length_offering in
    let updated_wire_list =
      if extended_zero_needed > 0 then
        (
        (* add 1 bit wires of zero *)
          List.fold_left (fun acc _ ->
          let (wires', zero_wire) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (1, 0)) graph.wires in
          graph.wires <- wires';
          acc @ [zero_wire]
        ) updated_wire_list' (List.init extended_zero_needed (fun _ -> ()))
        )
      else
        updated_wire_list'
    in
    if List.length updated_wire_list < max_len then
      raise (event_graph_error_default (Printf.sprintf "Compiler error in xoffer: wire list length less than expected! current = %d| expected = %d" (List.length updated_wire_list) max_len) e.span) ;


      let index_values = List.fold_left (fun acc idx ->
        let wc, incr_wr = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (bit_len, idx)) graph.wires in
        graph.wires <- wc;
        let wtd = Typing.immediate_data graph (Some incr_wr) `Logic ctx.current in

        acc @ [wtd]
      ) [] (List.init max_len (fun idx -> idx)) in
      let selector_indexes = List.fold_left (fun acc idx ->
        let wires, wr = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs Add sel_w (`Single (Option.get idx.ld.w)) graph.wires in
          graph.wires <- wires;
          acc @ [wr]
      ) [] index_values in
      let wires,valid_ready_array = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs (List.rev updated_wire_list) graph.wires in
      graph.wires <- wires;

      let sw_cond_wires = List.fold_left (fun acc idx ->
        let (wires', sw_cond_w) = WireCollection.add_slice graph.thread_id valid_ready_array (NonConst idx) (1) graph.wires in
        graph.wires <- wires';
        acc @ [sw_cond_w]
      ) [] selector_indexes in

      let cond_value_pairs = List.combine sw_cond_wires selector_indexes in
      (* take the last value out *)
      let cond_value_pairs_filtered = List.filteri (fun i _ -> i < (max_len - 1)) cond_value_pairs in

      let (wires, cond_w) = WireCollection.add_switch graph.thread_id ci.typedefs cond_value_pairs_filtered (List.nth selector_indexes (max_len - 1)) graph.wires in
      graph.wires <- wires;

    
      let is_wildcard_present = List.exists (fun msg_spec ->
            msg_spec.endpoint = "*" && msg_spec.msg = "*"
      ) offer_msg_list in
    
      let required_branch_conditions = List.filteri (fun i _ -> i < length_offering) index_values in
    let wildcard_arm =
      List.find_opt (fun (offer_arm, _) ->
        match offer_arm with
        | OfferWildcard -> true
        | _ -> false
      ) offer_arms
      in

    let offer_arms_new = if is_wildcard_present then offer_arm_filtered @ [Option.get wildcard_arm] else offer_arm_filtered in
    
    let branch_count = List.length offer_arms in
    let branch_info = {
      branch_cond_v = {w = Some cond_w; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = unit_dtype};
      branch_cond = MatchCases (List.map (fun td -> td.ld) required_branch_conditions);
      branch_count = branch_count;
      branches_to = [];
      branches_val = [];
    } in

    (* Process each offer arm in its own branch *)
    let branch_contexts_and_tds = List.mapi (fun idx (offer_arm, arm_expr) ->
      let (br_side, ctx_branch) = BuildContext.branch_side graph ctx branch_info idx in
      
      let td_result = match offer_arm with
        | OfferSend send_pack ->
            let msg = MessageCollection.lookup_message graph.messages send_pack.send_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer send" e.span in
            if msg.dir <> Out then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let td_data = construct_graphIR graph ci ctx_branch send_pack.send_data in
            let msg_dtype = (List.hd msg.sig_types).dtype in
            let err_string = Printf.sprintf "In offer send: Invalid data type for message %s: expected %s but got %s"
              send_pack.send_msg_spec.endpoint (string_of_data_type msg_dtype) (string_of_data_type td_data.ld.dtype) in
            check_dtype err_string (Some msg_dtype) td_data.ld.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            
            let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.ld.lt.live; ty = EventGraph.Send (send_pack.send_msg_spec, td_data.ld)} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            let ctx' = BuildContext.wait graph ctx_branch ntd.ld.lt.live in
            construct_graphIR graph ci ctx' arm_expr

        | OfferRecv (id, recv_pack) ->
            let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer receive" e.span in
            if msg.dir <> Inp then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let (wires', w) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
            graph.wires <- wires';
            let ntd = Typing.recv_msg_data graph w recv_pack.recv_msg_spec msg ctx_branch.current in
              
            ctx_branch.current.sustained_actions <-
              ({until = ntd.ld.lt.live; ty = EventGraph.Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            
            (* Bind the received value and continue *)
            let ctx_with_binding = BuildContext.add_binding ctx_branch id ntd.ld in
            let ctx' = BuildContext.wait graph ctx_with_binding ntd.ld.lt.live in
            construct_graphIR graph ci ctx' arm_expr
        | OfferWildcard ->
            construct_graphIR graph ci ctx_branch arm_expr
      in
      
      (br_side, ctx_branch, td_result)
    ) offer_arms_new in

    (* Collect branch information *)
    let branch_sides = List.map (fun (br_side, _, _) -> br_side) branch_contexts_and_tds in
    let branch_ctxs = List.map (fun (_, ctx_b, _) -> ctx_b) branch_contexts_and_tds in
    let branch_tds = List.map (fun (_, _, td) -> td) branch_contexts_and_tds in
    
    branch_info.branches_to <- List.map (fun (ctx_b : BuildContext.t) -> ctx_b.current) branch_ctxs;
    branch_info.branches_val <- List.map (fun td -> td.ld.lt.live) branch_tds;
    
    BuildContext.branch_merge ctx branch_ctxs;
    
    let ctx_br = BuildContext.branch graph ctx branch_info ci.file_name in
    List.iter (fun br_side -> br_side.branch_event <- Some ctx_br.current) branch_sides;
    
    (* Merge lifetimes and borrows from all branches *)
    let merged_dead = List.fold_left Utils.list_unordered_join [] (List.map (fun td -> td.ld.lt.dead) branch_tds) in
    let merged_borrows = List.fold_left Utils.list_unordered_join [] (List.map (fun td -> td.ld.reg_borrows) branch_tds) in
    let lt = {live = ctx_br.current; dead = merged_dead} in
    
    (* Determine result wire and dtype *)
    let result_w = match branch_tds with
      | [] -> None
      | hd::_ -> hd.ld.w
    in
    let result_dtype = match branch_tds with
      | [] -> unit_dtype
      | hd::_ -> hd.ld.dtype
    in
    
   {ld = {w = result_w; lt; reg_borrows = merged_borrows; dtype = result_dtype}}



    
  | Recv recv_pack ->
    let ep  = recv_pack.recv_msg_spec.endpoint in
    if not (MessageCollection.endpoint_owned graph.messages ep) then
      raise (event_graph_error_default (Printf.sprintf "Endpoint %s not owned by the process" ep) e.span);
    let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in receive" e.span in
    if msg.dir <> Inp then (
      (* mismatching direction *)
      raise (event_graph_error_default "Mismatching message direction!" e.span)
    );
    let (wires', w) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
    graph.wires <- wires';
    let ntd = Typing.recv_msg_data graph w recv_pack.recv_msg_spec msg ctx.current in
    ctx.current.sustained_actions <-
      ({until = ntd.ld.lt.live; ty = Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx.current.sustained_actions;
    ntd
  | Indirect (e', fieldname) ->
    let td = construct_graphIR graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in indirection" e'.span td.ld.w in
    let (offset_le, len, new_dtype) = TypedefMap.data_type_indirect ci.typedefs ci.macro_defs td.ld.dtype fieldname
      |> unwrap_or_err (Printf.sprintf "Invalid indirection %s" fieldname) e.span in
    let (wires', new_w) = WireCollection.add_slice graph.thread_id w (Const offset_le) len graph.wires in
    graph.wires <- wires';
    {ld = {
      td.ld with
      w = Some new_w;
      dtype = new_dtype
    }
    }
  | Index (e', ind) ->
    let td = construct_graphIR graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in indexing" e'.span td.ld.w in
    let (offset_le, len, new_dtype) =
      TypedefMap.data_type_index ci.typedefs ci.macro_defs
        (construct_graphIR graph ci ctx)
        (binop_td_const e.span Mul)
        td.ld.dtype ind
      |> unwrap_or_err (Printf.sprintf "Invalid indexing %s for datatype %s" (string_of_index ind) (Lang.string_of_data_type td.ld.dtype)) e.span in
    let wire_of (td:node_data) = unwrap_or_err (Printf.sprintf "Invalid indexing for %s in data type %s" (string_of_index ind) (Lang.string_of_data_type td.ld.dtype)) e.span td.ld.w in
    let offset_le_w = MaybeConst.map wire_of offset_le in
    let (wires', new_w) = WireCollection.add_slice graph.thread_id w offset_le_w len graph.wires in
    graph.wires <- wires';
    (
      match offset_le with
      | Const _ -> {ld = {td.ld with w = Some new_w; dtype = new_dtype}}
      | NonConst td_offset ->
          Typing.merged_data graph (Some new_w) new_dtype ctx.current [td.ld; td_offset.ld]
    )
  | Record (record_ty_name, field_exprs, None) ->
    (
      match TypedefMap.data_type_name_resolve ci.typedefs @@ `Named (record_ty_name, []) with
      | Some (`Record record_fields) ->
        (
          match Utils.list_match_reorder (List.map fst record_fields) field_exprs with
          | Some expr_reordered ->
            let tds = List.map2 (fun (field_name, expected_dtype) e' ->
              let td = construct_graphIR graph ci ctx e' in
              let err_string = DTypeCheck.fmt_record_field field_name expected_dtype td.ld.dtype in
              check_dtype err_string (Some expected_dtype) td.ld.dtype e'.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
              (e', td)
            ) record_fields expr_reordered in
            let ws = List.rev_map (fun ((e', td) : expr_node * node_data) ->
              unwrap_or_err "Invalid value in record field" e'.span td.ld.w) tds in
            let (wires', w) = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs ws graph.wires in
            graph.wires <- wires';
            List.map (fun (_, td) -> td.ld) tds |> Typing.merged_data graph (Some w) (`Named (record_ty_name, [])) ctx.current
          | _ -> raise (event_graph_error_default "Invalid record type value!" e.span)
        )
      | _ -> raise (event_graph_error_default "Invalid record type name!" e.span)
    )
  | Record (record_ty_name, field_exprs, Some field_base) ->
      (* record update *)
      let td_base = construct_graphIR graph ci ctx field_base in
      let tds = List.map (fun (field_ident, e') -> (field_ident, e', construct_graphIR graph ci ctx e')) field_exprs in
      let updates =
        (* bruteforce *)
        List.map (fun (field_ident, _e', td) ->
          match TypedefMap.data_type_indirect ci.typedefs ci.macro_defs (`Named (record_ty_name, [])) field_ident with
          | None -> 
            let err_string = Printf.sprintf "In record update: Invalid field %s for record type %s" field_ident record_ty_name in
             raise (event_graph_error_default err_string e.span)
          | Some (offset_le, len, _dtype) -> (offset_le, len, Option.get td.ld.w)
        ) tds in
      let (wires', w) = WireCollection.add_update graph.thread_id ci.typedefs (Option.get td_base.ld.w) updates graph.wires in
      graph.wires <- wires';
      Typing.merged_data graph (Some w) (`Named (record_ty_name, [])) ctx.current (td_base.ld::(List.map (fun (_, _, td) -> td.ld) tds))
  | Construct (cstr_spec, cstr_expr_opt) ->
    (
      match TypedefMap.data_type_name_resolve ci.typedefs @@ `Named (cstr_spec.variant_ty_name, []) with
      | Some (`Variant (dtype_opt, variants)) ->
        let variant_val = `Variant (dtype_opt, variants) in
        let e_dtype_opt = variant_lookup_dtype variant_val cstr_spec.variant in
        (
          match e_dtype_opt, cstr_expr_opt with
          | Some e_dtype, Some cstr_expr ->
            let td = construct_graphIR graph ci ctx cstr_expr in
            (* if td.dtype <> e_dtype then
              raise (Except.TypeError [Text ("In variant construction: Invalid data type for " ^ cstr_spec.variant ^ ": expected " ^ (string_of_data_type e_dtype) ^ " got " ^ (string_of_data_type td.dtype)); Except.codespan_local e.span]); *)
            let w = unwrap_or_err "Invalid value in variant construction" cstr_expr.span td.ld.w in
            let tag_size = variant_tag_size variant_val
            and data_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs e_dtype
            and tot_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs variant_val
            and var_idx = variant_lookup_index variant_val cstr_spec.variant
              |> unwrap_or_err ("Invalid constructor: " ^ cstr_spec.variant) e.span in
            let (wires', w_tag) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs
              (WithLength (tag_size, var_idx)) graph.wires in
            let (wires', new_w) = if tot_size = tag_size + data_size then
              (* no padding *)
              WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [w; w_tag] wires'
            else begin
              (* padding needed *)
              let (wires', w_pad) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs
                (WithLength (tot_size - tag_size - data_size, 0)) wires' in
              WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [w_pad; w; w_tag] wires'
            end in
            graph.wires <- wires';
            {ld = { td.ld with w = Some new_w }}
          | None, None ->
            let tag_size = variant_tag_size variant_val
            and tot_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs variant_val
            and var_idx = variant_lookup_index variant_val cstr_spec.variant
              |> unwrap_or_err ("Invalid constructor: " ^ cstr_spec.variant) e.span in
            let (wires', w_tag) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs
              (WithLength (tag_size, var_idx)) graph.wires in
            let (wires', new_w) = if tot_size = tag_size then
              (wires', w_tag)
            else begin
              let (wires', w_pad) = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs
                (WithLength (tot_size - tag_size, 0)) wires' in
              WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [w_pad; w_tag] wires'
            end in
            graph.wires <- wires';
            Typing.const_data graph (Some new_w)  (`Named (cstr_spec.variant_ty_name, [])) ctx.current
          | _ -> raise (event_graph_error_default "Invalid variant construct expression!" e.span)
        )
      | _ -> raise (event_graph_error_default "Invalid variant type name!" e.span)
    )
  | SharedAssign (id, value_expr) ->
    let shared_info = Hashtbl.find_opt ctx.shared_vars_info id
      |> unwrap_or_err ("Undefined identifier " ^ id) e.span in
    if graph.thread_id = shared_info.assigning_thread then
      let value_td = construct_graphIR graph ci ctx value_expr in
      if not ctx.lt_check_phase then (
        if (Option.is_some shared_info.value.w) || (Option.is_some shared_info.assigned_at) then (
          let prev_assign_action =
            (Option.get shared_info.assigned_at).actions
            |> List.find (fun {d; _} ->
              match d with
              | PutShared (id', _, _) -> id' = id
              | _ -> false
            )
          in
          raise (EventGraphError [
            Text "Shared value can only be assigned in one place!";
            Except.codespan_local e.span;
            Text "Previously assigned at:";
            Except.codespan_local prev_assign_action.span
          ]);
        );
        shared_info.value.w <- value_td.ld.w;
        shared_info.assigned_at <- Some ctx.current;
      );
      ctx.current.actions <- (PutShared (id, shared_info, value_td.ld) |> tag_with_span e.span)::ctx.current.actions;
      Typing.const_data graph None (unit_dtype) ctx.current
    else
      raise (event_graph_error_default "Shared variable assigned in wrong thread" e.span)
  | List li ->
    let tds = List.map (construct_graphIR graph ci ctx) li in
    let ws = List.map (fun td -> unwrap_or_err "Invalid wires!" e.span td.ld.w) tds in
    let (wires', new_w) = WireCollection.add_list graph.thread_id ci.typedefs ws graph.wires
      |> unwrap_or_err "Invalid list!" e.span in
    graph.wires <- wires';
    let td = List.hd tds in
    Typing.merged_data graph (Some new_w) (`Array (td.ld.dtype, ParamEnv.Concrete (List.length tds))) ctx.current (List.map (fun td -> td.ld) tds)
  | Recurse ->
    ctx.current.is_recurse <- true;
    Typing.const_data graph None unit_dtype ctx.current
  | Recursion (id, body) ->
    let new_ctx = BuildContext.add_rec_var_binding ctx id ctx.current.id in
    let endi = construct_graphIR graph ci new_ctx body in 
    if endi.ld.lt.live.id = ctx.current.id then
      SpanPrinter.warn "Recursion may not terminate!" e.span ci.file_name;
    endi 
  | Recursor id ->
    let rec_event_id_opt = BuildContext.lookup_rec_var_binding ctx id in
    if Option.is_none rec_event_id_opt then
      raise (Except.TypeError [Text ("Undefined recursion variable " ^ id); Except.codespan_local e.span]);
    
    let rec_event_id = Option.get rec_event_id_opt in
    let rec_event = Typing.lookup_event graph rec_event_id
      |> unwrap_or_err ("Invalid recursion event id " ^ string_of_int rec_event_id) e.span in
    ctx.current.is_recurse <- true;
    Typing.create_recurse_td rec_event ctx.current.id
  | Until (cond, body) ->
    
    (* Start evaluating the condition - this runs in parallel *)
    let td_cond = construct_graphIR graph ci ctx cond in
    

    let until_info = {
      until_entry =  ctx.current; (* placeholder, will be set *)
      until_stop_cond = td_cond.ld.lt.live;
      until_body_end = ctx.current; (* placeholder, will be set *)
    } in
    
    let body_entry = Typing.event_create graph (`UntilEntry (ctx.current, until_info)) in
    until_info.until_entry <- body_entry;
    
    let ctx_body = {ctx with current = body_entry} in
    let td_body = construct_graphIR graph ci ctx_body body in
    
    let body_end = td_body.ld.lt.live in
    until_info.until_body_end <- body_end;
    
    let exit_event = Typing.event_create graph (`UntilExit until_info) in
    
    let lt = {
      live = exit_event;
      dead = Utils.list_unordered_join td_cond.ld.lt.dead td_body.ld.lt.dead
    } in
    let reg_borrows' = Utils.list_unordered_join td_cond.ld.reg_borrows td_body.ld.reg_borrows in
    {ld = {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}}


  | Tuple _ -> raise (event_graph_error_default "Unimplemented expression!" e.span)

