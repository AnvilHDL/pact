open EventGraph
open EventGraphOps
open Lang

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

module Typing = struct
  type binding = {
    binding_val : timed_data;
    mutable binding_used : bool; (** if the binding has been used (to enforce relevance) *)
  }

  let use_binding binding =
    binding.binding_used <- true;
    binding.binding_val

  type context = binding Utils.string_map

  type build_context = {
    typing_ctx : context;
    current : event;
    shared_vars_info : (identifier, shared_var_info) Hashtbl.t;
    lt_check_phase : bool;
  }

  let event_create g source =
    let event_create_inner () =
      let parents =
        match source with
        | `Root None -> []
        | `Seq (e, _)
        | `Root Some (e, _) -> [e]
        | `Later (e1, e2) -> [e1; e2]
        | `Branch (_, { branches_val; _ }) -> branches_val
        | `UntilEntry (e, info) -> [e; info.until_body_end] (* parent and body_end for recursion *)
        | `UntilExit info -> [info.until_stop_cond; info.until_body_end] (* exit depends on stop condition/as well as the body finishing *)
      in
      let new_preds = List.fold_left
        (fun preds e -> Utils.IntSet.union preds e.preds)
        Utils.IntSet.empty
        parents
      in
      let new_preds = Utils.IntSet.add (g.last_event_id + 1) new_preds in
      let n = {actions = []; sustained_actions = []; source; id = g.last_event_id + 1;
        is_recurse = false;
        outs = []; graph = g; preds = new_preds; removed = false; session_type = None } in
      g.events <- n::g.events;
      g.last_event_id <- n.id;
      n
    in
    (
      match source with
      | `Later (e1, e2) -> (
        if Utils.IntSet.mem e1.id e2.preds then
          e2
        else if Utils.IntSet.mem e2.id e1.preds then
          e1
        else
          event_create_inner ()
      )
      | _ -> event_create_inner ()
    )


  let lifetime_intersect g (a : lifetime) (b : lifetime) =
    {
      live = event_create g (`Later (a.live, b.live));
      dead = Utils.list_unordered_join a.dead b.dead;
    }

  let cycles_data g (n : int) (current : event) =
    let live_event = event_create g (`Seq (current, `Cycles n)) in
    {w = None; lt = {live = live_event; dead = [(live_event, `Eternal)]}; reg_borrows = []; dtype = unit_dtype}
  let sync_data g (current : event) (td: timed_data) =
    let ev = event_create g (`Later (current, td.lt.live)) in
    {td with lt = {td.lt with live = ev}}

  let offer_condition g (ctx : build_context) (m_list : message_specifier list) : timed_data =
  let live_event = event_create g (`Seq (ctx.current, `Choice m_list)) in
    {w = None; lt = {live = live_event; dead = [(live_event, `Eternal)]}; reg_borrows = []; dtype = unit_dtype}
  let immediate_data _g (w : wire option) dtype (current : event) = {w; lt = lifetime_immediate current; reg_borrows = []; dtype}
  let const_data _g (w : wire option) dtype (current : event) = {w; lt = lifetime_const current; reg_borrows = []; dtype}
  let merged_data g (w : wire option) dtype (current : event) (tds : timed_data list) =
    let lts = List.map (fun x -> x.lt) tds in
    match lts with
    | [] -> const_data g w dtype current
    | lt::lts' ->
      let lt' = List.fold_left (lifetime_intersect g) lt lts' in
      let reg_borrows' = List.concat_map (fun x -> x.reg_borrows) tds in
      {w; lt = lt'; reg_borrows = reg_borrows'; dtype}
  let derived_data (w : wire option) (td : timed_data) = {td with w}
  let send_msg_data g (msg : message_specifier) (current : event) =
    let live_event = event_create g (`Seq (current, `Send msg)) in
    {w = None; lt = {live = live_event; dead = [(live_event, `Eternal)]}; reg_borrows = []; dtype = unit_dtype}

  let sync_event_data g ident gtd current =
    let event_synced = event_create g (`Seq (current, `Sync ident)) in
    let dpat = gtd.glt.e in
    (
      match dpat with
      | `Cycles _ -> ()
      | _ -> raise (Except.UnimplementedError [Text "Non-static lifetime for shared data is unsupported!"])
    );
    {w = gtd.w; lt = {live = event_synced; dead = [(event_synced, dpat)]}; reg_borrows = []; dtype = gtd.gdtype}

  let recv_msg_data g (w : wire option) (msg : message_specifier) (msg_def : message_def) (current : event) =
    let event_received = event_create g (`Seq (current, `Recv msg)) in
    let stype = List.hd msg_def.sig_types in
    let e = delay_pat_globalise msg.endpoint stype.lifetime.e in
    {w; lt = {live = event_received; dead = [(event_received, e)]}; reg_borrows = []; dtype = stype.dtype}

  let context_add (ctx : context) (v : identifier) (d : timed_data) : context =
    Utils.StringMap.add v {binding_val = d; binding_used = false} ctx
  let context_empty : context = Utils.StringMap.empty
  let context_lookup (ctx : context) (v : identifier) = Utils.StringMap.find_opt v ctx
  (* checks if lt lives at least as long as required *)

  let context_clear_used =
    Utils.StringMap.map (fun r -> {r with binding_used = false})

  module BuildContext = struct
    type t = build_context
    let create_empty g si lt_check_phase: t = {
      typing_ctx = context_empty;
      current = event_create g (`Root None);
      shared_vars_info = si;
      lt_check_phase;
    }

    let clear_bindings (ctx : t) : t =
      {ctx with typing_ctx = context_empty}
    let add_binding (ctx : t) (v : identifier) (d : timed_data) : t =
      {ctx with typing_ctx = context_add ctx.typing_ctx v d}
    let wait g (ctx : t) (other : event) : t =
      {ctx with current = event_create g (`Later (ctx.current, other))}

    (* returns a pair of contexts for *)
    let branch_side g (ctx : t) (bi : branch_info) (sel : int) : branch_side_info * t  =
      let br_side_info = {branch_event = None; owner_branch = bi; branch_side_sel = sel} in
      let event_side_root = event_create g (`Root (Some (ctx.current, br_side_info))) in
      (br_side_info, {ctx with current = event_side_root; typing_ctx = context_clear_used ctx.typing_ctx})

    let branch g (ctx : t) (br_info : branch_info) : t =
      {ctx with current = event_create g (`Branch (ctx.current, br_info))}

    (* merge the used state in context *)
    let branch_merge ctx br_ctxs =
      let ctx1 = List.hd br_ctxs in
      let other_ctxs = List.tl br_ctxs in
      Utils.StringMap.iter (fun ident r ->
        if r.binding_used
            && (List.for_all
                (fun ctx2 -> (Utils.StringMap.find ident ctx2.typing_ctx).binding_used)
               other_ctxs) then (
          (Utils.StringMap.find ident ctx.typing_ctx).binding_used <- true
        )
      ) ctx1.typing_ctx
  end


end

type build_context = Typing.build_context
module BuildContext = Typing.BuildContext


let binop_td_const graph (ci:cunit_info) _ctx span op n td =
  let w = unwrap_or_err "Invalid value" span td.w in
  let sz = TypedefMap.data_type_size ci.typedefs ci.macro_defs td.dtype in
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
  {td with w = Some wres; dtype = `Array (`Logic, ParamEnv.Concrete sz')}


let binop_td_td graph (ci:cunit_info) ctx span op td1 td2 =
  let w1 = unwrap_or_err "Invalid value" span td1.w in
  let w2 = unwrap_or_err "Invalid value" span td2.w in
  let sz1 = TypedefMap.data_type_size ci.typedefs ci.macro_defs td1.dtype
  and sz2 = TypedefMap.data_type_size ci.typedefs ci.macro_defs td2.dtype in
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
  Typing.merged_data graph (Some wres) new_dtype ctx.current [td1; td2]

module DTypeCheck = struct
  let warn msg span file_name =
    Printf.eprintf "[Warning] %s\n" msg;
    SpanPrinter.print_code_span ~indent:2 ~trunc:(-5) stderr file_name span;
    flush stderr

  let type_error msg span =
    raise (Except.TypeError [Text msg; Except.codespan_local span])


  let get_size typedefs macro_defs dtype =
    try Some (TypedefMap.data_type_size typedefs macro_defs dtype)
    with _ -> None

  let fmt_mismatch ~context ~expected ~got =
    Printf.sprintf "%s: expected %s but got %s"
      context (string_of_data_type expected) (string_of_data_type got)

  let fmt_mismatch_opt ~context ~expected ~got =
    Printf.sprintf "%s: expected %s but got %s"
      context (string_of_data_type_opt expected) (string_of_data_type got)

  let fmt_size_mismatch ~context ~expected ~got ~expected_size ~got_size =
    Printf.sprintf "%s: expected %s (size %d) but got %s (size %d)"
      context (string_of_data_type expected) expected_size
      (string_of_data_type got) got_size

  (** Format assignment type error *)
  let fmt_assign lval expected got =
    fmt_mismatch
      ~context:(Printf.sprintf "In assignment: Invalid data type for %s" (string_of_lvalue lval))
      ~expected ~got

  let fmt_func_arg func_name arg_name expected got =
    fmt_mismatch
      ~context:(Printf.sprintf "In function call %s: Invalid argument type for %s" func_name arg_name)
      ~expected ~got

  let fmt_binop op dtype1 dtype2 =
    Printf.sprintf "In binary operation %s: Invalid argument types: %s and %s"
      (string_of_binop op) (string_of_data_type dtype1) (string_of_data_type dtype2)

  let fmt_send endpoint expected got =
    fmt_mismatch
      ~context:(Printf.sprintf "In send: Invalid data type for message %s" endpoint)
      ~expected ~got

  let fmt_record_field field_name expected got =
    fmt_mismatch
      ~context:(Printf.sprintf "In record construction: Invalid data type for field %s" field_name)
      ~expected ~got

  let fmt_let_binding ident expected got =
    fmt_mismatch_opt
      ~context:(Printf.sprintf "Invalid data type for %s" ident)
      ~expected ~got

  let fmt_simple got =
    Printf.sprintf "Invalid data type: %s" (string_of_data_type got)

  let check ~typedefs ~macro_defs ~err_string ~expected ~got ~span ~file_name ~weak_mode =
    if expected = got then
      ()
    else
      let sz_expected = get_size typedefs macro_defs expected in
      let sz_got = get_size typedefs macro_defs got in
      match sz_expected, sz_got with
      | Some se, Some sg when se <> sg ->
        (* sizes don't match - always raise error *)
        let size_err = fmt_size_mismatch
          ~context:"Type size mismatch"
          ~expected ~got ~expected_size:se ~got_size:sg in
        type_error size_err span
      | Some _, Some _ ->
        if weak_mode then
          warn err_string span file_name
        else
          type_error err_string span
      | _ ->
        raise (Except.TypeError [
          Text ("Cannot determine type size for " ^ (string_of_data_type expected) ^ " or " ^ (string_of_data_type got));
          Except.codespan_local span
        ])
end

let check_dtype err_string dtype1 dtype2 span file_name allow typedefs macro_defs =
  match dtype1 with
  | Some dt1 ->
    DTypeCheck.check
      ~typedefs ~macro_defs
      ~err_string ~expected:dt1 ~got:dtype2
      ~span ~file_name ~weak_mode:allow
  | None -> ()

let rec recurse_unfold expr_full_node expr_node =
  let unfold = recurse_unfold expr_full_node in
  if expr_node.d = Recurse then
    expr_full_node
  else
    let expr' = match expr_node.d with
    | Literal _ | Identifier _
    | Cycle _ | Sync _
    | Ready _ | Read _ | Probe _
    | Debug DebugFinish
    | Recv _ -> expr_node.d
    | Call (ident, expr_nodes) ->
      Call (ident, List.map unfold expr_nodes)
    | Assign (lval, expr_node') ->
      Assign (lval, unfold expr_node')
    | Binop (op, e1, e2) ->
      ( match e2 with
        | `List es2 ->
          let es2' = List.map unfold es2 in
          let e1' = unfold e1 in
          Binop (op, e1', `List es2')
        | `Single e2' ->
          let e2n = unfold e2' in
          Binop (op, unfold e1, (`Single e2n))
      )
    | Unop (op, expr_node') ->
      Unop (op, unfold expr_node')
    | Tuple expr_nodes ->
      Tuple (List.map unfold expr_nodes)
    | Let (idents, dtype, e) ->
      Let (idents, dtype, unfold e)
    | Join (e1, e2) ->
      Join (unfold e1, unfold e2)
    | Wait (e1, e2) ->
      Wait (unfold e1, unfold e2)
    | IfExpr (e1, e2, e3) ->
      IfExpr (unfold e1, unfold e2, unfold e3)
    | TrySend (sp, e1, e2) ->
      let sp = {sp with send_data = unfold sp.send_data} in
      TrySend (sp, unfold e1, unfold e2)
    | TryRecv (ident, rp, e1, e2) ->
      TryRecv (ident, rp, unfold e1, unfold e2)
    | Construct (cs, e') ->
      Construct (cs, Option.map unfold e')
    | Record (ident, vs, base) ->
      Record (ident,
        List.map (fun (i, e) -> (i, unfold e)) vs,
        Option.map unfold base
      )
    | Index (e', idx) ->
      Index (unfold e', idx)
    | Indirect (e', ident) ->
      Indirect (unfold e', ident)
    | Cast (e', dtype) ->
      Cast (unfold e', dtype)
    | Concat (es, is_flat) ->
      Concat (List.map unfold es, is_flat)
    | Match (e, arms) ->
      Match (unfold e,
        List.map (fun (m, eop) -> (m, Option.map unfold eop)) arms
      )
    | Debug (DebugPrint (format, es)) ->
      Debug (DebugPrint (format, List.map unfold es))
    | Send sp ->
      Send {sp with send_data = unfold sp.send_data}
    | SharedAssign (ident, e') ->
      SharedAssign (ident, unfold e')
    | List es ->
      List (List.map unfold es)
    | XOffer (arms, selector) ->
      XOffer (
        List.map (fun (arm_type, e_body) ->
          (arm_type, unfold e_body)
        ) arms,
        selector
      )
    | Offer arms ->
      Offer (
        List.map (fun (arm_type, e_body) ->
          (arm_type, unfold e_body)
        ) arms
      )
    | Until (cond, body) ->
      Until (unfold cond, unfold body)
    | Recurse -> failwith "Shouldn't reach here!"
    in
    {expr_node with d = expr'}

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
        (visit_expr graph ci ctx)
        (binop_td_const Mul)
        lval_info'.lval_dtype idx
      |> unwrap_or_err "Invalid lvalue indexing" span in
    let le_n = MaybeConst.add (binop_td_const Add) (binop_td_td Add) le' le
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
    let le_n = MaybeConst.add_const le (binop_td_const Add) le'
    in
    {
      lval_range = {lval_info'.lval_range with subreg_range_interval = (le_n, len)};
      lval_dtype = dtype
    }





and visit_expr (graph : event_graph) (ci : cunit_info)
                    (ctx : build_context) (e : expr_node) : timed_data =
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
      let ctx_val = Typing.context_lookup ctx.typing_ctx ident in
      let macro_val = List.assoc_opt ident (List.map (fun (macro : macro_def) ->(macro.id, macro.value)) ci.macro_defs) in
      (match ctx_val, macro_val with
        | Some _, Some _ ->
          raise (event_graph_error_default ("Conflicting Identifier " ^ ident ^ " declarations found") e.span)
        | Some binding, None -> Typing.use_binding binding |> Typing.sync_data graph ctx.current
        | None, Some value ->
          let sz = Utils.int_log2 (value + 1) in
          let (wires', w) = WireCollection.add_literal graph.thread_id
              ci.typedefs ci.macro_defs
              (WithLength (sz, value)) graph.wires in
            graph.wires <- wires';
            Typing.const_data graph (Some w) (`Array (`Logic, ParamEnv.Concrete sz)) ctx.current
        | None, None ->
          Typing.context_lookup ctx.typing_ctx ident
          |> unwrap_or_err ("Undefined identifier: " ^ ident) e.span
          |> Typing.use_binding |> Typing.sync_data graph ctx.current
      )

  | Assign (lval, e') ->
    let td = visit_expr graph ci ctx e' in
    let lvi = lvalue_info_of graph ci ctx e.span lval in
    let err_string = DTypeCheck.fmt_assign lval lvi.lval_dtype td.dtype in
    check_dtype err_string (Some lvi.lval_dtype) td.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
    ctx.current.actions <- (RegAssign (lvi, td) |> tag_with_span e.span)::ctx.current.actions;
    Typing.cycles_data graph 1 ctx.current
  | Call (id, arg_list) ->
      let func = List.find_opt (fun (f: Lang.func_def) -> f.name = id) ci.func_defs
        |> unwrap_or_err ("Undefined function: " ^ id) e.span in
      let td_args = List.map (visit_expr graph ci ctx) arg_list in
      let ctx' = BuildContext.clear_bindings ctx |> ref in
      if List.length td_args <> List.length func.args then
        raise (event_graph_error_default "Arguments missing in function call" e.span);
        List.iter2 (fun td arg ->
        (
          let _ = td.w in (* added for tc*)
          match arg.arg_type with
            | Some gtype ->
              let err_string = DTypeCheck.fmt_func_arg id arg.arg_name gtype td.dtype in
              check_dtype err_string (Some gtype) td.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            | None -> ()
        );
        ctx' := BuildContext.add_binding !ctx' arg.arg_name td
      ) td_args func.args;
      visit_expr graph ci !ctx' func.body
  | Binop (binop, e1, e2) ->
    (
      let td1 = visit_expr graph ci ctx e1 in
      let w1 = unwrap_or_err "Invalid value" e1.span td1.w in
      match e2 with
      | `List ws2 ->
        let td2_list = List.map (fun e2 ->
          let td2 = visit_expr graph ci ctx e2 in
          td2
        ) ws2 in
        let w2_list = List.map (fun td2 ->
          unwrap_or_err "Invalid value of second operator" e1.span td2.w
        ) td2_list in
        let (wires', w) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs binop w1 (`List w2_list) graph.wires in
        graph.wires <- wires';
        let new_dtype = `Array (`Logic, ParamEnv.Concrete w.size) in
        Typing.merged_data graph (Some w) new_dtype ctx.current (List.concat [[td1]; td2_list])
      | `Single e ->
        let td2 = visit_expr graph ci ctx e in
        let w2 = unwrap_or_err "Invalid value of second operator" e1.span td2.w in
        let (wires', w) = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs binop w1 (`Single w2) graph.wires in
        graph.wires <- wires';
        let err_string = DTypeCheck.fmt_binop binop td1.dtype td2.dtype in
        check_dtype err_string (Some td1.dtype) td2.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        
        let new_dtype = match binop with
        | LAnd | LOr | Lt | Gt | Lte | Gte | Eq | Neq ->
          `Logic
        | _ ->
          td1.dtype
        in 
        
        Typing.merged_data graph (Some w) new_dtype ctx.current [td1; td2]
    )
  | Unop (unop, e') ->
    let td = visit_expr graph ci ctx e' in
    let w' = unwrap_or_err "Invalid value" e'.span td.w in
    let (wires', w) = WireCollection.add_unary graph.thread_id ci.typedefs unop w' graph.wires in
    graph.wires <- wires';
    Typing.derived_data (Some w) td
  | Tuple [] -> Typing.const_data graph None (unit_dtype) ctx.current
  | Let (_idents, _, e) -> visit_expr graph ci ctx e
  | Join (e1, e2) ->
    let td1 = visit_expr graph ci ctx e1 in
    (
      match e1.d with
      | Let (["_"],dtype ,_) -> 
        let err_string = DTypeCheck.fmt_simple td1.dtype in
        check_dtype err_string dtype td1.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let td = visit_expr graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.lt td.lt in
        {td with lt} (* forcing the bound value to be awaited *)
      | Let ([], dtype, _) ->
        let err_string = DTypeCheck.fmt_mismatch_opt ~context:"Invalid data type" ~expected:dtype ~got:td1.dtype in
        check_dtype err_string dtype td1.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let td = visit_expr graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.lt td.lt in
        {td with lt} (* forcing the bound value to be awaited *)
      | Let ([ident],dtype, _) ->
          let err_string = DTypeCheck.fmt_let_binding ident dtype td1.dtype in
          check_dtype err_string dtype td1.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
          let ctx' = BuildContext.add_binding ctx ident td1 in
          let td = visit_expr graph ci ctx' e2 in
          (* check if the binding is used *)
          let binding = Typing.context_lookup ctx'.typing_ctx ident |> Option.get in
          (* no need to wait if the value is current *)
          if td1.lt.live.id <> ctx.current.id && not binding.binding_used then (
            (* raise (event_graph_error_default "Value is potentially not awaited!" e1.span) *)
            Printf.eprintf "[Warning] Value bound to %s is potentially not awaited!\n" ident;
            (SpanPrinter.print_code_span ~indent:2 ~trunc:(-5) stderr ci.file_name e1.span)
          ;
          );
          td
      | Let _ -> raise (event_graph_error_default "Discarding expression results!" e.span)
      | _ ->
        let td = visit_expr graph ci ctx e2 in
        let lt = Typing.lifetime_intersect graph td1.lt td.lt in
        {td with lt} (* forcing the bound value to be awaited *)
    )
  | Wait (e1, e2) ->
    let td1 = visit_expr graph ci ctx e1 in
    (
      match e1.d with
      | Let (["_"], dtype, _) ->
        let err_string = DTypeCheck.fmt_simple td1.dtype in
        check_dtype err_string dtype td1.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let ctx' = BuildContext.wait graph ctx td1.lt.live in
        visit_expr graph ci ctx' e2
      | Let ([], dtype, _) ->
        let err_string = DTypeCheck.fmt_simple td1.dtype in
        check_dtype err_string dtype td1.dtype e1.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        let ctx' = BuildContext.wait graph ctx td1.lt.live in
        visit_expr graph ci ctx' e2
      | Let ([ident], dtype, _) ->
        let err_string = DTypeCheck.fmt_let_binding ident dtype td1.dtype in
        check_dtype err_string dtype td1.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
        (* add the binding to the context *)
        let ctx' = BuildContext.wait graph ctx td1.lt.live in
        let ctx' = BuildContext.add_binding ctx' ident td1 in
        visit_expr graph ci ctx' e2
      | Let _ -> raise (event_graph_error_default "Discarding expression results!" e.span)
      | _ ->
        let ctx' = BuildContext.wait graph ctx td1.lt.live in
        visit_expr graph ci ctx' e2
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
    let td1 = visit_expr graph ci ctx e1 in
    (* TODO: type checking *)
    let w1 = unwrap_or_err "Invalid condition" e1.span td1.w in
    let ctx' = BuildContext.wait graph ctx td1.lt.live in
    let branch_info = {
      branch_cond_v = td1;
      branch_cond = TrueFalse;
      branch_count = 2; (* for if-else *)
      branches_to = [];
      branches_val = [];
    } in

    let (br_side_true, ctx_true) = BuildContext.branch_side graph ctx' branch_info 0 in
    let td2 = visit_expr graph ci ctx_true e2 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx' branch_info 1 in
    let td3 = visit_expr graph ci ctx_false e3 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td2.lt.live; td3.lt.live];

    BuildContext.branch_merge ctx' [ctx_true; ctx_false];

    let ctx_br = BuildContext.branch graph ctx' branch_info in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.lt.dead td2.lt.dead |> Utils.list_unordered_join td3.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.reg_borrows td2.reg_borrows |> Utils.list_unordered_join td3.reg_borrows in
    (
      match td2.w, td3.w with
      | None, None -> {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}
      | Some w2, Some w3 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w1, w2)] w3 graph.wires in
        graph.wires <- wires';
        {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.dtype}
      | _ -> raise (event_graph_error_default "Invalid if expression!" e.span)
    )
  | TrySend (send_pack, e1, e2) ->
    (* data to send *)
    let msg = MessageCollection.lookup_message graph.messages send_pack.send_msg_spec ci.channel_classes
      |> unwrap_or_err "Invalid message specifier in try send" e.span in
    let td_send_data = visit_expr graph ci ctx send_pack.send_data in
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
    let td1 = visit_expr graph ci ctx_true e1 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx branch_info 1 in
    let td2 = visit_expr graph ci ctx_false e2 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td1.lt.live; td2.lt.live];

    BuildContext.branch_merge ctx [ctx_true; ctx_false];

    ctx_true.current.actions <- (ImmediateSend (send_pack.send_msg_spec, td_send_data) |> tag_with_span e.span)::ctx_true.current.actions;

    let ctx_br = BuildContext.branch graph ctx branch_info in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.lt.dead td2.lt.dead |> Utils.list_unordered_join td_cond.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.reg_borrows td2.reg_borrows |> Utils.list_unordered_join td_cond.reg_borrows in
    (
      match td1.w, td2.w with
      | None, None -> {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}
      | Some w1, Some w2 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w_cond, w1)] w2 graph.wires in
        graph.wires <- wires';
        {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.dtype}
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
    let td1 = visit_expr graph ci ctx_true e1 in
    let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx branch_info 1 in
    let td2 = visit_expr graph ci ctx_false e2 in

    branch_info.branches_to <- [ctx_true.current; ctx_false.current];
    branch_info.branches_val <- [td1.lt.live; td2.lt.live];

    BuildContext.branch_merge ctx [ctx_true_no_binding; ctx_false];

    ctx_true.current.actions <- (ImmediateRecv recv_pack.recv_msg_spec |> tag_with_span e.span)::ctx_true.current.actions;

    let ctx_br = BuildContext.branch graph ctx branch_info in
    br_side_true.branch_event <- Some ctx_br.current;
    br_side_false.branch_event <- Some ctx_br.current;
    let lt = {live = ctx_br.current; (* branch event is reached when either split event is reached *)
      dead = Utils.list_unordered_join td1.lt.dead td2.lt.dead |> Utils.list_unordered_join td_cond.lt.dead} in
    let reg_borrows' = Utils.list_unordered_join td1.reg_borrows td2.reg_borrows |> Utils.list_unordered_join td_cond.reg_borrows in
    (
      match td1.w, td2.w with
      | None, None -> {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}
      | Some w1, Some w2 ->
      (* TODO: check that the data types are the same *)
        let (wires', w) = WireCollection.add_switch graph.thread_id ci.typedefs [(w_cond, w1)] w2 graph.wires in
        graph.wires <- wires';
        {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td2.dtype}
      | _ -> raise (event_graph_error_default "Invalid try recv expression!" e.span)
    )

  | Match (match_v, match_arms) ->
    let td_v = visit_expr graph ci ctx match_v in
    let w_v = unwrap_or_err "Invalid match expression" match_v.span td_v.w in
    let ctx' = BuildContext.wait graph ctx td_v.lt.live in
    let branch_info = {
      branch_cond_v = td_v;
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
        let td_pats = List.map (fun (pat, _) -> visit_expr graph ci ctx' pat) match_arms in
        (* make sure that the patterns are all constants *)
        List.iter2
          (fun ((pat, _) : expr_node * expr_node option) td ->
            let valid =
              match td.w with
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
            let td = visit_expr graph ci ctx @@ Option.get body in
            ((ctx, br_side, td), (ctx.current, td.lt.live))
          )
          match_arms
        in
        let (br_side_default, ctx_default) = BuildContext.branch_side graph ctx' branch_info (branch_info.branch_count - 1) in
        let td_default = visit_expr graph ci ctx_default @@ Option.get @@ snd default_arm in

        let (branches, branches_events) = List.split branches in
        let (branches_to, branches_val) = List.split branches_events in
        branch_info.branches_to <- branches_to @ [ctx_default.current];
        branch_info.branches_val <- branches_val @ [td_default.lt.live];

        BuildContext.branch_merge ctx' @@ ctx_default::(List.map (fun (ctx, _, _) -> ctx) branches);
        let ctx_br = BuildContext.branch graph ctx' branch_info in
        List.iter
          (fun (_, br_side, _) ->
            br_side.branch_event <- Some ctx_br.current
          )
          branches;
        br_side_default.branch_event <- Some ctx_br.current;
        let lt = {
          live = ctx_br.current;
          dead = List.fold_left (fun l (_, _, td) -> Utils.list_unordered_join l td.lt.dead) td_v.lt.dead branches;
        } in
        let reg_borrows' = List.fold_left (fun l (_, _, td) -> Utils.list_unordered_join l td.reg_borrows) td_v.reg_borrows branches in
        branch_info.branch_cond <- MatchCases td_pats;
        if List.for_all (fun (_, _, td_val) -> Option.is_none td_val.w) branches then
          {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}
        else (
          let (wires', w) = WireCollection.add_cases graph.thread_id ci.typedefs w_v
            (List.map2 (fun td_pat (_, _, td_val) -> (Option.get td_pat.w, Option.get td_val.w)) td_pats branches) (match td_default.w with | Some w -> w | None -> raise (event_graph_error_default "Invalid match expression (exactly one default case expected)!" e.span))
            graph.wires in
          graph.wires <- wires';
          {w = Some w; lt; reg_borrows = reg_borrows'; dtype = td_default.dtype}
        )
      | _ -> raise @@ event_graph_error_default "Invalid match expression (atleast one default case expected)!" e.span
    )
  | Cast (e', dtype) ->
    let td = visit_expr graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in cast" e'.span td.w in
    let target_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs dtype in
    if w.size > target_size then (
      (* Truncate: take slice of the wire to match target size *)
      let base_i = MaybeConst.Const 0 in
      let wires', w' = WireCollection.add_slice graph.thread_id w base_i target_size graph.wires in
      graph.wires <- wires';
      Typing.merged_data graph (Some w') dtype ctx.current [td]
    ) else if w.size < target_size then (
      (* Extend: pad with zeros to match target size *)
      let pad_len = target_size - w.size in
      let wires', pad_w = WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (pad_len, 0)) graph.wires in
      let wires', w' = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs [pad_w; w] wires' in
      graph.wires <- wires';
      Typing.merged_data graph (Some w') dtype ctx.current [td]
    ) else (
      (* Sizes match, just update type *)
      Typing.merged_data graph (Some w) dtype ctx.current [td]
    )
  | Concat (es, is_flat) ->
    let tds = List.map (fun e' -> (e', visit_expr graph ci ctx e')) es in
    let ws = List.map (fun ((e', td) : expr_node * timed_data) -> unwrap_or_err "Invalid value in concat" e'.span td.w) tds in
    let (wires', w) = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs ws graph.wires in
    graph.wires <- wires';
    let tdtype = List.map (fun ((_, td): expr_node * timed_data) -> td.dtype) tds in
    if not (List.for_all (fun d -> d = List.hd tdtype) tdtype) && (not is_flat) then
      raise (Except.TypeError [Text ("In concat: Incompatible types: " ^ (String.concat ", " (List.map string_of_data_type tdtype))); Except.codespan_local e.span]);
    let new_dtype = ( 
      match is_flat with 
      | false -> `Array (List.hd tdtype, ParamEnv.Concrete (List.length es))
      | _ -> `Array (`Logic, ParamEnv.Concrete (w.size))
    ) in
    List.map snd tds |> Typing.merged_data graph (Some w) new_dtype ctx.current
  |  Read rlval ->
    let reg_ident = Lang.get_lvalue_reg_id rlval in
    let r = Utils.StringMap.find_opt reg_ident graph.regs
      |> unwrap_or_err ("Undefined register " ^ reg_ident) e.span in    
    let (wires'', w'') = WireCollection.add_reg_read graph.thread_id ci.typedefs ci.macro_defs r graph.wires in
    graph.wires <- wires'';
    let td = {w = Some w''; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = r.d_type} in
    let get_borrow_info in_off le dt w lval td' =
      match lval with 
        | Reg _ -> (dt,in_off,le,w,td')
        | Indexed (lv, idx) ->
          let inner_info = lvalue_info_of graph ci ctx e.span lv in
          let inner_le = fst inner_info.lval_range.subreg_range_interval in
          let inner_dtype = inner_info.lval_dtype in
          let (offset_le, len, dt') = TypedefMap.data_type_index ci.typedefs ci.macro_defs
            (visit_expr graph ci ctx)
            (binop_td_const e.span Mul)
            inner_dtype idx |> unwrap_or_err (Printf.sprintf "Invalid indexing %s for datatype %s" (string_of_index idx) (Lang.string_of_data_type inner_dtype)) e.span in
          let total_offset_le = MaybeConst.add (binop_td_const e.span Add) (_binop_td_td e.span Add) offset_le inner_le in
          let off_i = MaybeConst.map_off total_offset_le in
          let (off, le') = if off_i < 0 then (
            Printf.eprintf "[Warning] The offset is not a constant value for %s, borrowing full range\n" reg_ident;
            (0, len)
          ) else (off_i, len) in
          let (wire', w') = WireCollection.add_slice graph.thread_id w (MaybeConst.map (fun td -> unwrap_or_err "Invalid indexing in lvalue" e.span td.w) total_offset_le) le' graph.wires in
          graph.wires <- wire';
          let new_td = match total_offset_le with
            | MaybeConst.NonConst td_offset -> Typing.merged_data graph (Some w') dt' ctx.current [td'; td_offset]
            | MaybeConst.Const _ -> {td' with w = Some w'; dtype = dt'}
          in
          (dt', off, le', w', new_td)
        | Indirected (lval_inner, field_id) -> 
          let lval_info_inner = lvalue_info_of graph ci ctx e.span lval_inner in
          let (inner_le, _inner_len) = lval_info_inner.lval_range.subreg_range_interval in
          let (field_offset_le, len, new_dtype) = TypedefMap.data_type_indirect ci.typedefs ci.macro_defs lval_info_inner.lval_dtype field_id
            |> unwrap_or_err (Printf.sprintf "Invalid indirection %s" field_id) e.span in
          (* total offset = inner offset + field offset *)
          let total_offset_le = MaybeConst.add_const field_offset_le (binop_td_const e.span Add) inner_le in
          let off_i = MaybeConst.map_off total_offset_le in
          let (off, le') = if off_i < 0 then (
            Printf.eprintf "[Warning] The offset is not a constant value for indirection %s, borrowing full range\n" field_id;
            (0, len)
          ) else (off_i, len) in
          let (wi', new_w) = WireCollection.add_slice graph.thread_id w (MaybeConst.map (fun td -> unwrap_or_err "Invalid indexing in indirection" e.span td.w) total_offset_le) le' graph.wires in
          graph.wires <- wi';
          let new_td = match total_offset_le with
            | MaybeConst.Const _ -> {td' with w = Some new_w; dtype = new_dtype}
            | MaybeConst.NonConst td_offset -> Typing.merged_data graph (Some new_w) new_dtype ctx.current [td'; td_offset]
          in
          (new_dtype, off, le', new_w, new_td)
    in
    let full_sz = TypedefMap.data_type_size ci.typedefs ci.macro_defs r.d_type in
    let (_dt,off,le,_w,td'') = get_borrow_info 0 full_sz r.d_type w'' rlval td in
    let borrow = {borrow_range = sub_reg_range reg_ident off le; borrow_start = ctx.current; borrow_source_span = e.span} in
    { td'' with dtype = _dt; reg_borrows = borrow :: td''.reg_borrows }
  | Debug op ->
    (
      match op with
      | DebugPrint (s, e_list) ->
        let timed_ws = List.map (visit_expr graph ci ctx) e_list in
        let all_w = List.for_all(
          fun td ->
            match td.w with
            | Some _ -> true
            | None -> false
        ) timed_ws in 
        if not all_w then
          raise (Except.TypeError [Text "Invalid value in debug print"; Except.codespan_local e.span]);
        ctx.current.actions <- (let open EventGraph in DebugPrint (s, timed_ws) |> tag_with_span e.span)::ctx.current.actions;
        {w = None; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = unit_dtype}
      | DebugFinish ->
        ctx.current.actions <- (let open EventGraph in tag_with_span e.span DebugFinish)::ctx.current.actions;
        {w = None; lt = EventGraphOps.lifetime_const ctx.current; reg_borrows = []; dtype = unit_dtype}
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
    let td = visit_expr graph ci ctx send_pack.send_data in
    let msg_dtype = (List.hd msg.sig_types).dtype in
    let err_string = DTypeCheck.fmt_send send_pack.send_msg_spec.endpoint msg_dtype td.dtype in
    check_dtype err_string (Some msg_dtype) td.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
    let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx.current in
    ctx.current.sustained_actions <-
      ({
        until = ntd.lt.live;
        ty = Send (send_pack.send_msg_spec, td)
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
    let ctx = BuildContext.wait graph ctx cond_td.lt.live in

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
          branch_cond_v = wire_td;
          branch_cond = TrueFalse;
          branch_count = 2; (* wildcard arm and others *)
          branches_to = [];
          branches_val = [];
        } in
        let (br_side_true, ctx_wildcard) = BuildContext.branch_side graph ctx outer_branch_info 0 in
        let td_result = visit_expr graph ci ctx_wildcard wildcard_arm_expr in

      
        let (br_side_false, ctx_true) = BuildContext.branch_side graph ctx outer_branch_info 1 in
        outer_branch_info.branches_to <- [ctx_wildcard.current; ctx_true.current];
        outer_branch_info.branches_val <- [td_result.lt.live];
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
        branch_cond_v = wire_td;
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
            
            let td_data = visit_expr graph ci ctx_branch send_pack.send_data in
            let msg_dtype = (List.hd msg.sig_types).dtype in
            let err_string = Printf.sprintf "In offer send: Invalid data type for message %s: expected %s but got %s"
              send_pack.send_msg_spec.endpoint (string_of_data_type msg_dtype) (string_of_data_type td_data.dtype) in
            check_dtype err_string (Some msg_dtype) td_data.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            
            let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.lt.live; ty = EventGraph.Send (send_pack.send_msg_spec, td_data)} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            let ctx' = BuildContext.wait graph ctx_branch ntd.lt.live in
            visit_expr graph ci ctx' arm_expr

        | OfferRecv (id, recv_pack) ->
            let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer receive" e.span in
            if msg.dir <> Inp then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let (wires', w) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
            graph.wires <- wires';
            let ntd = Typing.recv_msg_data graph w recv_pack.recv_msg_spec msg ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.lt.live; ty = EventGraph.Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            
            let ctx_with_binding = BuildContext.add_binding ctx_branch id ntd in
            let ctx' = BuildContext.wait graph ctx_with_binding ntd.lt.live in
            visit_expr graph ci ctx' arm_expr
          | OfferWildcard ->
            raise (event_graph_error_default "Wildcard offer arm should have been filtered out!" e.span)
      in
      
      (* Create false branch (empty continuation) *)
      let (br_side_false, ctx_false) = BuildContext.branch_side graph ctx' branch_info 1 in
      let td_false = Typing.const_data graph None unit_dtype ctx_false.current in
      
      (* Update branch info *)
      branch_info.branches_to <- [ctx_branch.current; ctx_false.current];
      branch_info.branches_val <- [td_result.lt.live; td_false.lt.live];
      
      BuildContext.branch_merge ctx' [ctx_branch; ctx_false];
      
      let ctx_br = BuildContext.branch graph ctx' branch_info in
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
    let merged_event = List.fold_left (fun acc_event (branch_ctx:build_context) ->
      Typing.event_create graph (`Later (acc_event, branch_ctx.current))
    ) (List.hd branch_ctxs).current (List.tl branch_ctxs) in
    
    (* Merge lifetimes and borrows from all branches *)
    let merged_dead = List.fold_left Utils.list_unordered_join 
      cond_td.lt.dead (List.map (fun td -> td.lt.dead) branch_tds) in
    let merged_borrows = List.fold_left Utils.list_unordered_join 
      [] (List.map (fun td -> td.reg_borrows) branch_tds) in
    
    let lt = {live = merged_event; dead = merged_dead} in
    
    (* Use first branch's result as the representative *)
    let result_w = match branch_tds with
      | [] -> None
      | hd::_ -> hd.w
    in
    let result_dtype = match branch_tds with
      | [] -> unit_dtype
      | hd::_ -> hd.dtype
    in
    
    let td_false = {w = result_w; lt; reg_borrows = merged_borrows; dtype = result_dtype} in
    if is_wildcard_present then (
      let (outer_branch_info, br_side_true, br_side_false, td_wildcard,ctx_wildcard) = Option.get wildcard_info in
      outer_branch_info.branches_to <- outer_branch_info.branches_to @ [merged_event];
      outer_branch_info.branches_val <- outer_branch_info.branches_val @ [td_false.lt.live];
      BuildContext.branch_merge ctx [ctx'; ctx_wildcard];
      let ctx_br = BuildContext.branch graph ctx' outer_branch_info in
      br_side_true.branch_event <- Some ctx_br.current;
      br_side_false.branch_event <- Some ctx_br.current;
      {w = td_false.w; lt = {live = ctx_br.current; dead = Utils.list_unordered_join td_false.lt.dead td_wildcard.lt.dead}; reg_borrows = Utils.list_unordered_join td_false.reg_borrows td_wildcard.reg_borrows; dtype = td_false.dtype}
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
    let ctx = BuildContext.wait graph ctx cond_td.lt.live in
    
    (*==================== At this point one of the messages must have been received ==========================================================*)
    (* Now we match 1'd1 with respective valid ready port of branch conditions *)
    let length_offering = List.length offer_arm_filtered in
    let bit_len = (Utils.int_log2 length_offering) in

    let find_wire_ctx ct id =
      let binding = Typing.context_lookup ct id in
      let td = unwrap_or_err (Printf.sprintf "Could not find a binding for %s" id)  e.span binding in
      let w = unwrap_or_err (Printf.sprintf "No wire associated with this binding %s" id)  e.span td.binding_val.w in
      if w.size <> bit_len then
        raise (Except.TypeError [Except.Text (Printf.sprintf "State selector wire size mismatch: expected %d but got %d" bit_len w.size); Except.codespan_local e.span])
      else
      (graph.wires, w)
    in

    let new_wires, sel_w = if Option.is_some state_selector then (find_wire_ctx ctx.typing_ctx (Option.get state_selector)) else WireCollection.add_literal graph.thread_id ci.typedefs ci.macro_defs (WithLength (bit_len, 0)) graph.wires in
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
        let wires, wr = WireCollection.add_binary graph.thread_id ci.typedefs ci.macro_defs Add sel_w (`Single (Option.get idx.w)) graph.wires in
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
      let cond_value_pairs_filtered = cond_value_pairs |> List.take (max_len - 1) in

      let (wires, cond_w) = WireCollection.add_switch graph.thread_id ci.typedefs cond_value_pairs_filtered (List.nth selector_indexes (max_len - 1)) graph.wires in
      graph.wires <- wires;

    
      let is_wildcard_present = List.exists (fun msg_spec ->
            msg_spec.endpoint = "*" && msg_spec.msg = "*"
      ) offer_msg_list in
    
      let required_branch_conditions = List.take length_offering index_values in
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
      branch_cond = MatchCases required_branch_conditions;
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
            
            let td_data = visit_expr graph ci ctx_branch send_pack.send_data in
            let msg_dtype = (List.hd msg.sig_types).dtype in
            let err_string = Printf.sprintf "In offer send: Invalid data type for message %s: expected %s but got %s"
              send_pack.send_msg_spec.endpoint (string_of_data_type msg_dtype) (string_of_data_type td_data.dtype) in
            check_dtype err_string (Some msg_dtype) td_data.dtype e.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
            
            let ntd = Typing.send_msg_data graph send_pack.send_msg_spec ctx_branch.current in
            ctx_branch.current.sustained_actions <-
              ({until = ntd.lt.live; ty = EventGraph.Send (send_pack.send_msg_spec, td_data)} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            let ctx' = BuildContext.wait graph ctx_branch ntd.lt.live in
            visit_expr graph ci ctx' arm_expr

        | OfferRecv (id, recv_pack) ->
            let msg = MessageCollection.lookup_message graph.messages recv_pack.recv_msg_spec ci.channel_classes
              |> unwrap_or_err "Invalid message specifier in offer receive" e.span in
            if msg.dir <> Inp then
              raise (event_graph_error_default "Mismatching message direction!" e.span);
            
            let (wires', w) = WireCollection.add_msg_port graph.thread_id ci.typedefs ci.macro_defs recv_pack.recv_msg_spec 0 msg graph.wires in
            graph.wires <- wires';
            let ntd = Typing.recv_msg_data graph w recv_pack.recv_msg_spec msg ctx_branch.current in
              
            ctx_branch.current.sustained_actions <-
              ({until = ntd.lt.live; ty = EventGraph.Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx_branch.current.sustained_actions;
            
            (* Bind the received value and continue *)
            let ctx_with_binding = BuildContext.add_binding ctx_branch id ntd in
            let ctx' = BuildContext.wait graph ctx_with_binding ntd.lt.live in
            visit_expr graph ci ctx' arm_expr
        | OfferWildcard ->
            visit_expr graph ci ctx_branch arm_expr
      in
      
      (br_side, ctx_branch, td_result)
    ) offer_arms_new in

    (* Collect branch information *)
    let branch_sides = List.map (fun (br_side, _, _) -> br_side) branch_contexts_and_tds in
    let branch_ctxs = List.map (fun (_, ctx_b, _) -> ctx_b) branch_contexts_and_tds in
    let branch_tds = List.map (fun (_, _, td) -> td) branch_contexts_and_tds in
    
    branch_info.branches_to <- List.map (fun (ctx_b : BuildContext.t) -> ctx_b.current) branch_ctxs;
    branch_info.branches_val <- List.map (fun td -> td.lt.live) branch_tds;
    
    BuildContext.branch_merge ctx branch_ctxs;
    
    let ctx_br = BuildContext.branch graph ctx branch_info in
    List.iter (fun br_side -> br_side.branch_event <- Some ctx_br.current) branch_sides;
    
    (* Merge lifetimes and borrows from all branches *)
    let merged_dead = List.fold_left Utils.list_unordered_join [] (List.map (fun td -> td.lt.dead) branch_tds) in
    let merged_borrows = List.fold_left Utils.list_unordered_join [] (List.map (fun td -> td.reg_borrows) branch_tds) in
    let lt = {live = ctx_br.current; dead = merged_dead} in
    
    (* Determine result wire and dtype *)
    let result_w = match branch_tds with
      | [] -> None
      | hd::_ -> hd.w
    in
    let result_dtype = match branch_tds with
      | [] -> unit_dtype
      | hd::_ -> hd.dtype
    in
    
    {w = result_w; lt; reg_borrows = merged_borrows; dtype = result_dtype}



    
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
      ({until = ntd.lt.live; ty = Recv recv_pack.recv_msg_spec} |> tag_with_span e.span)::ctx.current.sustained_actions;
    ntd
  | Indirect (e', fieldname) ->
    let td = visit_expr graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in indirection" e'.span td.w in
    let (offset_le, len, new_dtype) = TypedefMap.data_type_indirect ci.typedefs ci.macro_defs td.dtype fieldname
      |> unwrap_or_err (Printf.sprintf "Invalid indirection %s" fieldname) e.span in
    let (wires', new_w) = WireCollection.add_slice graph.thread_id w (Const offset_le) len graph.wires in
    graph.wires <- wires';
    {
      td with
      w = Some new_w;
      dtype = new_dtype
    }
  | Index (e', ind) ->
    let td = visit_expr graph ci ctx e' in
    let w = unwrap_or_err "Invalid value in indexing" e'.span td.w in
    let (offset_le, len, new_dtype) =
      TypedefMap.data_type_index ci.typedefs ci.macro_defs
        (visit_expr graph ci ctx)
        (binop_td_const e.span Mul)
        td.dtype ind
      |> unwrap_or_err (Printf.sprintf "Invalid indexing %s for datatype %s" (string_of_index ind) (Lang.string_of_data_type td.dtype)) e.span in
  let wire_of (td:timed_data) = unwrap_or_err (Printf.sprintf "Invalid indexing for %s in data type %s" (string_of_index ind) (Lang.string_of_data_type td.dtype)) e.span td.w in
    let offset_le_w = MaybeConst.map wire_of offset_le in
    let (wires', new_w) = WireCollection.add_slice graph.thread_id w offset_le_w len graph.wires in
    graph.wires <- wires';
    (
      match offset_le with
      | Const _ -> {td with w = Some new_w; dtype = new_dtype}
      | NonConst td_offset ->
          Typing.merged_data graph (Some new_w) new_dtype ctx.current [td; td_offset]
    )
  | Record (record_ty_name, field_exprs, None) ->
    (
      match TypedefMap.data_type_name_resolve ci.typedefs @@ `Named (record_ty_name, []) with
      | Some (`Record record_fields) ->
        (
          match Utils.list_match_reorder (List.map fst record_fields) field_exprs with
          | Some expr_reordered ->
            let tds = List.map2 (fun (field_name, expected_dtype) e' ->
              let td = visit_expr graph ci ctx e' in
              let err_string = DTypeCheck.fmt_record_field field_name expected_dtype td.dtype in
              check_dtype err_string (Some expected_dtype) td.dtype e'.span ci.file_name ci.weak_typecasts ci.typedefs ci.macro_defs;
              (e', td)
            ) record_fields expr_reordered in
            let ws = List.rev_map (fun ((e', {w; _}) : expr_node * timed_data) ->
              unwrap_or_err "Invalid value in record field" e'.span w) tds in
            let (wires', w) = WireCollection.add_concat graph.thread_id ci.typedefs ci.macro_defs ws graph.wires in
            graph.wires <- wires';
            List.map snd tds |> Typing.merged_data graph (Some w) (`Named (record_ty_name, [])) ctx.current
          | _ -> raise (event_graph_error_default "Invalid record type value!" e.span)
        )
      | _ -> raise (event_graph_error_default "Invalid record type name!" e.span)
    )
  | Record (record_ty_name, field_exprs, Some field_base) ->
      (* record update *)
      let td_base = visit_expr graph ci ctx field_base in
      let tds = List.map (fun (field_ident, e') -> (field_ident, e', visit_expr graph ci ctx e')) field_exprs in
      let updates =
        (* bruteforce *)
        List.map (fun (field_ident, _e', td) ->
          match TypedefMap.data_type_indirect ci.typedefs ci.macro_defs (`Named (record_ty_name, [])) field_ident with
          | None -> 
            let err_string = Printf.sprintf "In record update: Invalid field %s for record type %s" field_ident record_ty_name in
             raise (event_graph_error_default err_string e.span)
          | Some (offset_le, len, _dtype) -> (offset_le, len, Option.get td.w)
        ) tds in
      let (wires', w) = WireCollection.add_update graph.thread_id ci.typedefs (Option.get td_base.w) updates graph.wires in
      graph.wires <- wires';
      Typing.merged_data graph (Some w) (`Named (record_ty_name, [])) ctx.current (td_base::(List.map (fun (_, _, td) -> td) tds))
  | Construct (cstr_spec, cstr_expr_opt) ->
    (
      match TypedefMap.data_type_name_resolve ci.typedefs @@ `Named (cstr_spec.variant_ty_name, []) with
      | Some (`Variant _ as dtype) ->
        let e_dtype_opt = variant_lookup_dtype dtype cstr_spec.variant in
        (
          match e_dtype_opt, cstr_expr_opt with
          | Some e_dtype, Some cstr_expr ->
            let td = visit_expr graph ci ctx cstr_expr in
            (* if td.dtype <> e_dtype then
              raise (Except.TypeError [Text ("In variant construction: Invalid data type for " ^ cstr_spec.variant ^ ": expected " ^ (string_of_data_type e_dtype) ^ " got " ^ (string_of_data_type td.dtype)); Except.codespan_local e.span]); *)
            let w = unwrap_or_err "Invalid value in variant construction" cstr_expr.span td.w in
            let tag_size = variant_tag_size dtype
            and data_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs e_dtype
            and tot_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs dtype
            and var_idx = variant_lookup_index dtype cstr_spec.variant
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
            { td with w = Some new_w }
          | None, None ->
            let tag_size = variant_tag_size dtype
            and tot_size = TypedefMap.data_type_size ci.typedefs ci.macro_defs dtype
            and var_idx = variant_lookup_index dtype cstr_spec.variant
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
      let value_td = visit_expr graph ci ctx value_expr in
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
        shared_info.value.w <- value_td.w;
        shared_info.assigned_at <- Some ctx.current;
      );
      ctx.current.actions <- (PutShared (id, shared_info, value_td) |> tag_with_span e.span)::ctx.current.actions;
      Typing.const_data graph None (unit_dtype) ctx.current
    else
      raise (event_graph_error_default "Shared variable assigned in wrong thread" e.span)
  | List li ->
    let tds = List.map (visit_expr graph ci ctx) li in
    let ws = List.map (fun td -> unwrap_or_err "Invalid wires!" e.span td.w) tds in
    let (wires', new_w) = WireCollection.add_list graph.thread_id ci.typedefs ws graph.wires
      |> unwrap_or_err "Invalid list!" e.span in
    graph.wires <- wires';
    let td = List.hd tds in
    Typing.merged_data graph (Some new_w) (`Array (td.dtype, ParamEnv.Concrete (List.length tds))) ctx.current tds
  | Recurse ->
    ctx.current.is_recurse <- true;
    Typing.const_data graph None unit_dtype ctx.current
  | Until (cond, body) ->
    
    (* Start evaluating the condition - this runs in parallel *)
    let td_cond = visit_expr graph ci ctx cond in
    

    let until_info = {
      until_entry =  ctx.current; (* placeholder, will be set *)
      until_stop_cond = td_cond.lt.live;
      until_body_end = ctx.current; (* placeholder, will be set *)
    } in
    
    let body_entry = Typing.event_create graph (`UntilEntry (ctx.current, until_info)) in
    until_info.until_entry <- body_entry;
    
    let ctx_body = {ctx with current = body_entry} in
    let td_body = visit_expr graph ci ctx_body body in
    
    let body_end = td_body.lt.live in
    until_info.until_body_end <- body_end;
    
    let exit_event = Typing.event_create graph (`UntilExit until_info) in
    
    let lt = {
      live = exit_event;
      dead = Utils.list_unordered_join td_cond.lt.dead td_body.lt.dead
    } in
    let reg_borrows' = Utils.list_unordered_join td_cond.reg_borrows td_body.reg_borrows in
    {w = None; lt; reg_borrows = reg_borrows'; dtype = unit_dtype}


  | Tuple _ -> raise (event_graph_error_default "Unimplemented expression!" e.span)


module IntHashTbl = Hashtbl.Make(Int)

(* unfold until sufficient for lifetime checks *)
let recurse_unfold_for_checks ci shared_vars_info graph expr_node =
  let tmp_graph = {graph with last_event_id = -1} in
  let td = visit_expr tmp_graph ci
    (BuildContext.create_empty tmp_graph shared_vars_info true)
    expr_node in
  (* now just check the total *)
  let root = List.find (fun e -> e.source = `Root None) tmp_graph.events in
  let recurse = List.find (fun e -> e.is_recurse) tmp_graph.events in
  let dists = GraphAnalysis.event_min_distance_with_later tmp_graph.events root root in
  let full_dist = IntHashTbl.find dists td.lt.live.id in
  let recurse_dist = IntHashTbl.find dists recurse.id in
  if recurse_dist = 0 then
    raise (event_graph_error_default "Recurse delay must be greater than 0!" expr_node.span);
  (* the number of times to unfold is minimum for the recurse time to first pass the end event *)
  let unfold_times = full_dist / recurse_dist in
  let cur_expr = ref expr_node in
  for _ = 1 to unfold_times do
    cur_expr := recurse_unfold !cur_expr expr_node
  done;
  !cur_expr
(* Builds the graph representation for each process To Do: Add support for commands outside loop (be executed once or continuosly)*)
let build_proc (config : Config.compile_config) sched module_name param_values
              (ci' : cunit_info) (proc : proc_def) : proc_graph =
  let proc =
    if param_values = [] then
      proc
    else
      ParamConcretise.concretise_proc param_values proc
  in
  let macro_defs_extended =
    List.fold_left2 (fun acc (p : Lang.param) (pval : param_value) ->
      match p.param_ty, pval with
      | IntParam, IntParamValue v ->
        {
          id = p.param_name;
          value = v;
        } :: acc
      | _ -> acc
    ) ci'.macro_defs proc.params param_values in

  
  let ci = {
    file_name = ci'.file_name;
    typedefs = ci'.typedefs;
    channel_classes = ci'.channel_classes;
    macro_defs = macro_defs_extended;
    func_defs = ci'.func_defs;
    session_defs = ci'.session_defs;
    weak_typecasts = ci'.weak_typecasts;
  } in

  match proc.body with
  | Native body ->
    let msg_collection = MessageCollection.create body.channels
                                      proc.args body.spawns ci.channel_classes in
    let spawns =
    List.map (fun (s : spawn_def ast_node) ->
      let module_name = BuildScheduler.add_proc_task sched ci.file_name s.span s.d.proc s.d.compile_params in
      (module_name, s)
    ) body.spawns in
    let shared_vars_info = Hashtbl.create (List.length body.shared_vars) in
    List.iter (fun sv ->
      let v = {
        w = None;
        glt = sv.d.shared_lifetime;
        gdtype = unit_dtype; (* explicitly annotate? *)
      } in
      let r = {
        assigning_thread = sv.d.assigning_thread;
        value = v;
        assigned_at = None;
      } in
        Hashtbl.add shared_vars_info sv.d.ident r
      ) body.shared_vars;
      let endpoint_collection = List.map (fun (p:endpoint_def ast_node) -> (p.d.name, p.d.channel_class)) proc.args in
      let channel_local_sty = List.map (fun p -> (match (MessageCollection.lookup_channel_class ci.channel_classes (snd p)) with Some c -> c.local_sty | None -> None))endpoint_collection in

      let protocol_list =
        List.map2 (fun (ep_name, _) (sty_opt: session_type ast_node option) ->
          match sty_opt with
          | Some sty -> Some (ep_name, sty) 
          | None -> None
        ) endpoint_collection channel_local_sty
      in
      let protocol_list_filtered = List.filter Option.is_some protocol_list |> List.map Option.get in
      (* create hash table for fast lookup of endpoint name with protocol *)
      let protocol_map = Hashtbl.create (List.length protocol_list_filtered) in
      List.iter (fun (ep_name, proto) -> Hashtbl.add protocol_map ep_name proto) protocol_list_filtered;
      if (config.verbose) then Printf.eprintf "[Info] Protocol list for process %s: %s\n" module_name (String.concat ", " (List.map(fun f -> Lang.string_of_protocol (snd f).d) protocol_list_filtered));
      
      let proc_interface_protocol = 
        match proc.interface with
        | Some intf ->
          let session = List.find_opt (fun (s : session_def ast_node) -> s.d.name = intf.d) ci.session_defs
            |> unwrap_or_err ("Undefined interface " ^ intf.d) intf.span in
          Some (session.d.body)
        | None -> None
      in
      if body.threads = [] then
        raise (Except.TypeError [Text (Printf.sprintf "Process %s must have at least one thread!" proc.name)]);

      let proc_threads = List.mapi (fun i ((e, reset_by) : expr_node * message_specifier option) ->
        let graph = {
          thread_id = i;
          events = [];
          wires = WireCollection.empty;
          channels = List.map data_of_ast_node body.channels;
          messages = msg_collection;
          spawns = body.spawns;
          regs = List.map (fun (reg : Lang.reg_def ast_node) ->
                (reg.d.name, reg.d)) body.regs |> Utils.StringMap.of_list;
          last_event_id = -1;
          is_general_recursive = false;
          thread_codespan = e.span;
          comb = false;
          protocols = protocol_map;
          interface_protocol =  proc_interface_protocol;
        } in
        (* Bruteforce treatment: just run twice *)
        let graph_opt = if (not config.disable_lt_checks) || config.two_round_graph then (
          let tmp_graph = {graph with last_event_id = -1} in
          let td = visit_expr tmp_graph ci
            (BuildContext.create_empty tmp_graph shared_vars_info true)
            (recurse_unfold_for_checks ci shared_vars_info graph e) in
          tmp_graph.last_event_id <- (EventGraphOps.find_last_event tmp_graph).id;
          tmp_graph.is_general_recursive <- tmp_graph.last_event_id <> td.lt.live.id;
          (* Optimisation *)
          let tmp_graph = GraphOpt.optimize config true ci tmp_graph in
          if not config.disable_lt_checks then (
            LifetimeCheck.lifetime_check config ci tmp_graph
          );
          if config.two_round_graph then
            Some tmp_graph
          else
            None
        ) else None in
        let g = match graph_opt with
        | Some graph -> graph
        | None -> (
            (* discard after type checking *)
            let ctx = (BuildContext.create_empty graph shared_vars_info false) in
            let td = visit_expr graph ci ctx e in
            if not config.disable_session_checks then
            (
              (match proc_interface_protocol with
              | Some _ -> if(i == 0 ) then SessionCheck.check_session config graph module_name else Printf.eprintf "[Warning] Skipping session type checks for thread %d in process %s\n" i module_name
              | None -> Printf.eprintf "[Warning] No interface specified for process %s, skipping session type checks\n" module_name)
            );
            graph.last_event_id <- (EventGraphOps.find_last_event graph).id;
            graph.is_general_recursive <- graph.last_event_id <> td.lt.live.id;
            let g' = GraphOpt.optimize config false ci graph in
            GraphOpt.combinational_codegen config g' ci
        ) in
        (g, reset_by)
      ) body.threads in
      {name = module_name; extern_module = None;
        threads = proc_threads; shared_vars_info; messages = msg_collection;
        proc_body = proc.body; spawns = List.map (fun (ident, spawn) -> (ident, spawn)) spawns}
    | Extern (extern_mod, _extern_body) ->
      let msg_collection = MessageCollection.create [] proc.args [] ci.channel_classes in
      {name = module_name; extern_module = Some extern_mod; threads = [];
        shared_vars_info = Hashtbl.create 0; messages = msg_collection;
        proc_body = proc.body; spawns = []}

let build (config : Config.compile_config) sched module_name param_values (cunit : compilation_unit) =
  let macro_defs = cunit.macro_defs in
  let typedefs = TypedefMap.of_list cunit.type_defs in
  let func_defs = cunit.func_defs in
  let wty = config.weak_typecasts in
  let ci = {
    file_name = Option.get cunit.cunit_file_name;
    typedefs =typedefs;
    channel_classes = cunit.channel_classes;
    session_defs = cunit.session_defs;
    macro_defs = macro_defs;
    func_defs =func_defs;
    weak_typecasts = wty
  } in

  let lookup_interface (interfaces : session_def ast_node list) (intf : identifier) : session_def ast_node option =
    List.find_opt (fun (s:session_def ast_node) -> s.d.name = intf) interfaces
  in

  let add_proc_args (proc : proc_def) =
    if Option.is_some proc.interface then
      let intf = Option.get proc.interface in
      let session = lookup_interface cunit.session_defs intf.d
        |> unwrap_or_err ("Undefined interface " ^ intf.d) intf.span in
      let session_params = session.d.params in
      proc.args <- session_params

    in

  List.iter add_proc_args cunit.procs;



  (* Add channel defs and correct spawn def from interface and pools *)

 let lookup_channel_inst_from_pools (p : pool_inst) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
  let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = p.p_ty) p_defs in
  match pool_def_opt with
  | Some pool_def ->
      pool_def.d.pool_channels
  | None ->
    raise (Except.TypeError [Text ("Undefined interface pool " ^ p.p_id); Except.codespan_local default_span])  
  in

  let lookup_pool_inst_from_pools (id : identifier) (p_defs : (interface_pool_def ast_node) list) (default_span : code_span) =
    let pool_def_opt = List.find_opt (fun (pd : interface_pool_def ast_node) -> pd.d.pool_id = id) p_defs in
    match pool_def_opt with
    | Some pool_def ->
        pool_def
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool " ^ id); Except.codespan_local default_span])
  in

  let lookup_pool_ty_from_id (id : identifier) (p_defs : (pool_inst ast_node) list) (default_span : code_span) =
    let pool_inst_opt = List.find_opt (fun (pi : pool_inst ast_node) -> pi.d.p_id = id) p_defs in
    match pool_inst_opt with
    | Some pool_inst ->
        pool_inst.d.p_ty
    | None ->
      raise (Except.TypeError [Text ("Undefined interface pool instance " ^ id); Except.codespan_local default_span])
  in


  
  let get_params_from_interface_params (ip : ifc_instantiation) (p_defs : (interface_pool_def ast_node) list) (ifc_list : (pool_inst ast_node) list) (default_span : code_span) =
    let pi = lookup_pool_ty_from_id ip.pid ifc_list default_span in
    let pool_def = lookup_pool_inst_from_pools pi p_defs default_span in
    let interface_opt = List.find_opt (fun p -> p.d.inf_mem_id = ip.pifc_id) pool_def.d.interface_members in
    match interface_opt with
    | Some interface_member ->
      (
        match interface_member.d.interface_class_id with
        | Some intf_id ->
          List.map (fun param -> Lang.SingleEp param) intf_id.params
        | None ->
          raise (Except.TypeError [Text ("Currently only interface instantiation is supported in pool members, but got none for " ^ ip.pifc_id ^ " in pool " ^ ip.pid); Except.codespan_local default_span])
      )
    | None ->
      raise (Except.TypeError [Text ("Undefined interface member " ^ ip.pifc_id ^ " in pool " ^ ip.pid); Except.codespan_local default_span])
  in
    
  let lookup_session_types_from_pool_inst (id : identifier) (p_defs : (interface_pool_def ast_node) list) (s_defs : (session_def ast_node)list) (default_span : code_span) =
    let pool_def = lookup_pool_inst_from_pools id p_defs default_span in

    let session_defs = List.map (fun im ->
      match im.d.interface_class_id with
      | Some intf_id ->
        (
          let session_opt = lookup_interface s_defs intf_id.id in
          match session_opt with
          | Some session -> (session.d.body, intf_id.id)
          | None ->
            raise (Except.TypeError [Text ("Undefined Session type " ^ intf_id.id ^ " in pool member " ^ im.d.inf_mem_id); Except.codespan_local default_span])
        )
      | None ->
        raise (Except.TypeError [Text ("Currently only interface instantiation is supported in pool members, but got none for " ^ im.d.inf_mem_id ^ " in pool " ^ id);
          Except.codespan_local default_span])

    ) pool_def.d.interface_members in
    session_defs
      
 in

  List.iter (fun (proc : proc_def) ->
    match proc.body with
    | Extern _ -> ()
    | Native p ->
      List.iter (fun (ps : pool_inst ast_node) ->
        let channels = lookup_channel_inst_from_pools ps.d cunit.pools ps.span in
        p.channels <- p.channels @ channels ;
        let session_with_id = lookup_session_types_from_pool_inst ps.d.p_ty cunit.pools cunit.session_defs ps.span in

        (* (if List.length session_with_id > 2 then
          raise (Except.UnimplementedError [Text "Currently only up to two session types are supported in pool instances!"; Except.codespan_local ps.span])
        else *)
          (* let session1 = snd (List.hd session_with_id) in
          let session2 = snd (List.nth session_with_id 1) in
          let id1 = fst (List.hd session_with_id) in
          let id2 = fst (List.nth session_with_id 1) in *)
          
          (* Preprocess session types to replace interface parameters with actual endpoint names *)
          let preprocess_session_type endpoint_mapping (sty : Lang.session_type) : Lang.session_type =
            let replace_endpoint_in_msg_spec (msg_spec : Lang.message_specifier) : Lang.message_specifier =
              match Utils.StringMap.find_opt msg_spec.endpoint endpoint_mapping with
              | Some new_endpoint -> {msg_spec with endpoint = new_endpoint}
              | None -> msg_spec
            in
            
            let replace_in_atomic_action (action : Lang.atomic_action) : Lang.atomic_action =
              match action with
              | Lang.AtomBMsg msg_spec -> Lang.AtomBMsg (replace_endpoint_in_msg_spec msg_spec)
              | Lang.AtomNBMsg msg_spec -> Lang.AtomNBMsg (replace_endpoint_in_msg_spec msg_spec)
            in
            
            let replace_in_action_with_gap (action : Lang.atomic_action_with_gap) : Lang.atomic_action_with_gap =
              match action with
              | Lang.AtomDelay n -> Lang.AtomDelay n
              | Lang.AtomicAct atomic -> Lang.AtomicAct (replace_in_atomic_action atomic)
              | _ -> raise (Except.UnimplementedError [Text ("Unsupported atomic action with gap in preprocessing!"^(string_of_atomic_action_with_gap action)); Except.codespan_local ps.span]) 
            in
            
            let rec preprocess_sty (sty : Lang.session_type) : Lang.session_type =
              match sty with
              | Lang.StySeq (s1, s2) -> Lang.StySeq (preprocess_sty s1, preprocess_sty s2)
              | Lang.StyChoice (s1, s2) -> Lang.StyChoice (preprocess_sty s1, preprocess_sty s2)
              | Lang.StyParallel (s1, s2) -> Lang.StyParallel (preprocess_sty s1, preprocess_sty s2)
              | Lang.StyFuture s -> Lang.StyFuture (preprocess_sty s)
              | Lang.StyAtom action -> Lang.StyAtom (replace_in_action_with_gap action)
              | Lang.StyXOffer offerings ->
                  let process_offering (off : Lang.offering_session_type) : Lang.offering_session_type =
                    {
                      trigger = replace_in_action_with_gap off.trigger;
                      continuation = Option.map preprocess_sty off.continuation;
                    }
                  in
                  Lang.StyXOffer (List.map process_offering offerings)
              | Lang.StyOffer offerings ->
                  let process_offering (off : Lang.offering_session_type) : Lang.offering_session_type =
                    {
                      trigger = replace_in_action_with_gap off.trigger;
                      continuation = Option.map preprocess_sty off.continuation;
                    }
                  in
                  Lang.StyOffer (List.map process_offering offerings)
              | Lang.StyTrue -> Lang.StyTrue
              | _ -> raise (Except.UnimplementedError [Text "Unsupported session type with interface parameters in preprocessing!"])
            in
            preprocess_sty sty
          in
          
          (* Build endpoint mapping from interface params to actual endpoints from channels *)
          (* Additionally, map both left and right endpoints to the left endpoint name *)
          let build_endpoint_mapping (interface_member : Lang.interface_mem_def ast_node) (pool_channels : Lang.channel_def ast_node list) : identifier Utils.string_map =
            match interface_member.d.interface_class_id with
            | Some intf_inst ->
                (* Look up the interface definition to get parameter names *)
                let interface_opt = lookup_interface cunit.session_defs intf_inst.id in
                (match interface_opt with
                | Some interface_def ->
                    (* Map interface parameter names to actual endpoint names from channels *)
                    (* interface_def.d.params is a list of endpoint_def ast_node *)
                    (* intf_inst.params is a list of identifier (actual endpoint names) *)
                    let endpoint_param_names = List.map (fun (ep : Lang.endpoint_def ast_node) -> ep.d.name) interface_def.d.params in
                    let actual_endpoints = intf_inst.params in
                    
                    (* Build set of actual endpoints used by this interface *)
                    let actual_endpoints_set = List.fold_left (fun set ep ->
                      Utils.StringSet.add ep set
                    ) Utils.StringSet.empty actual_endpoints in
                    
                    (* Create unification map ONLY for channels where at least one endpoint is used by this interface *)
                    let relevant_unification_map = List.fold_left (fun map (chan : Lang.channel_def ast_node) ->
                      let left_used = Utils.StringSet.mem chan.d.endpoint_left actual_endpoints_set in
                      let right_used = Utils.StringSet.mem chan.d.endpoint_right actual_endpoints_set in
                      if left_used || right_used then
                        (* At least one endpoint is used - unify both to left *)
                        Utils.StringMap.add chan.d.endpoint_right chan.d.endpoint_left map
                      else
                        map
                    ) Utils.StringMap.empty pool_channels in
                    
                    (* Build base mapping, applying unification if actual_ep is a right endpoint *)
                    let base_mapping = List.fold_left2 (fun map param_name actual_ep ->
                      let unified_ep = match Utils.StringMap.find_opt actual_ep relevant_unification_map with
                        | Some left_ep -> left_ep  (* actual_ep is a right endpoint, use left instead *)
                        | None -> actual_ep        (* actual_ep is already a left endpoint or standalone *)
                      in
                      Utils.StringMap.add param_name unified_ep map
                    ) Utils.StringMap.empty endpoint_param_names actual_endpoints in
                    
                    (* Merge: add relevant unifications for direct endpoint-to-endpoint mapping within this interface *)
                    Utils.StringMap.fold Utils.StringMap.add relevant_unification_map base_mapping
                | None -> Utils.StringMap.empty)
            | None -> Utils.StringMap.empty
          in
          
          (* Apply preprocessing to all session types in the pool instance *)
          let pool_def = lookup_pool_inst_from_pools ps.d.p_ty cunit.pools ps.span in
          let session_with_id = List.map2 (fun (sty_node, _) interface_member ->
            let endpoint_mapping = build_endpoint_mapping interface_member pool_def.d.pool_channels in
            let preprocessed_sty = preprocess_session_type endpoint_mapping sty_node.d in
            ({sty_node with d = preprocessed_sty}, interface_member.d.inf_mem_id)
          ) session_with_id pool_def.d.interface_members in

          (* Map each left endpoint to the list of all interface IDs that use it *)
          (* This includes interfaces that use the left endpoint directly OR use its paired right endpoint *)

          
          if config.verbose then
          (
            List.iter (fun ((session : session_type ast_node), intf_id) ->
              Printf.eprintf "[Info] Preprocessed session type for interface %s in pool instance %s of process %s:\n%s\n"
                intf_id ps.d.p_id module_name (Lang.string_of_protocol session.d)
            ) session_with_id
          );
          let ep_itfc_id_map = SessionCompatiblityv2.create_ep_id_intfc_id_map pool_def in

          if not config.disable_compat_checks then
          (
              let check, err = SessionCompatiblityv2.compatiblity_check_multiparty session_with_id ep_itfc_id_map config.verbose_max ps.span in
              let ast_spans = List.map (fun ((session : session_type ast_node),_) -> Except.codespan_local session.span) session_with_id in
              if check then Printf.eprintf "[Info] Compatibility check passed for pool instance %s in process %s\n" ps.d.p_id module_name
              else
                raise (Except.TypeError (
                  Text ("Incompatibility detected between interfaces in pool instance " ^ ps.d.p_id ^ ": " ^ err)
                  :: ast_spans
                ))
              
                
          )
      ) p.pool_insts ;

      (* Now we add the parameters of the spawn *)
      List.iter (fun (s : spawn_def ast_node) ->
        (* let interface_params =  *)
        if Option.is_some s.d.interface_params then
          let interface_params = Option.get s.d.interface_params in
          List.iter (fun ip ->
            let params = get_params_from_interface_params ip cunit.pools  p.pool_insts s.span in
            s.d.params <- s.d.params @ params
          )interface_params
      ) p.spawns

  ) cunit.procs;




  

  (* check for type compatibility *)

  (* List.iter (fun (proc : proc_def) ->
    match proc.body with
    | Extern _ -> ()
    | Native p ->
      if List.length p.interfaces = 0 then
        ()
      else if List.length p.interfaces != 2  then
        raise (Except.UnimplementedError [Text "The compatiblity check currently only supports two interfaces!"; Except.codespan_local (List.hd p.interfaces).span])
      else
      (
          let intf1 = lookup_interface cunit.session_defs (List.nth p.interfaces 0).d in 
          let intf2 = lookup_interface cunit.session_defs (List.nth p.interfaces 1).d in
          if Option.is_none intf1 || Option.is_none intf2 then
            raise (Except.TypeError [Text "Undefined interface in compatiblity check!"; Except.codespan_local (List.hd p.interfaces).span]);
          let intf1 = Option.get intf1 in
          let intf2 = Option.get intf2 in
          let result, err = SessionCompatiblity.check_compatibility intf1.body intf2.body intf1.name intf2.name config.verbose (List.hd p.interfaces).span in
          if not result then
            raise (Except.TypeError [Text ("Incompatibility detected between interfaces " ^ intf1.name ^ " and " ^ intf2.name ^ ": " ^ err); 
              Except.codespan_local intf1.body.span; 
              Except.codespan_local intf2.body.span]
            )
      )

  ) cunit.procs; *)

  let graphs = List.map (build_proc config sched module_name param_values ci ) cunit.procs in
  {
    event_graphs = graphs;
    typedefs;
    macro_defs;
    channel_classes = cunit.channel_classes;
    external_event_graphs = [];
  }

let syntax_tree_precheck (_config : Config.compile_config) cunit =
  (* just check if the channel definitions have well-formed sync modes *)
  List.iter (fun cc ->
    let msg_set = ref Utils.StringSet.empty in
    List.iter (fun (msg : message_def) ->
      if Utils.StringSet.mem msg.name !msg_set then
        raise (Except.TypeError [Text "Duplicate message!"; Except.codespan_local msg.span])
      else (
        msg_set := Utils.StringSet.add msg.name !msg_set
      )
    ) cc.messages;
    List.iter (fun (msg : message_def) ->
      List.iter (fun {lifetime = lt_d; _} ->
        match lt_d.e with
        | `Cycles _ | `Eternal -> ()
        | `Message_with_offset (msg_name, _, _) ->
          if not @@ Utils.StringSet.mem msg_name !msg_set then
            raise (Except.TypeError [Text "Undefined message specified in delay pattern!"; Except.codespan_local msg.span])
      ) msg.sig_types;
      let check_dependent_msg msg_name =
        if msg_name = msg.name then
          raise (Except.TypeError [Text "Self-referential dependent sync mode is not allowed!"; Except.codespan_local msg.span]);
        if not @@ Utils.StringSet.mem msg_name !msg_set then
          raise (Except.TypeError [Text "Undefined message specified in dynamic sync mode!"; Except.codespan_local msg.span])
      in
      match msg.send_sync, msg.recv_sync with
      | Static (o_n, n), Static (o_m, m) ->
        if n <> m || o_n <> o_m then (* the cycle counts on both sides must be equal *)
          raise (Except.TypeError [Text "Static sync mode must be symmetric!"; Except.codespan_local msg.span])
      | Static _, Dependent (msg_name, _)
      | Dependent (msg_name, _), Static _
      | Dynamic, Dependent (msg_name, _) ->
        check_dependent_msg msg_name
      | Dependent _, Dynamic ->
        raise (Except.TypeError [Text "Dependent sync mode cannot be mixed with other sync mode!"; Except.codespan_local msg.span])
      | Dependent (msg1, n1), Dependent (msg2, n2) ->
        if msg1 <> msg2 || n1 <> n2 then
          raise (Except.TypeError [Text "Dependent sync mode must be symmetric!"; Except.codespan_local msg.span]);
        check_dependent_msg msg1
      | _ -> ()
    ) cc.messages
  ) cunit.channel_classes;
