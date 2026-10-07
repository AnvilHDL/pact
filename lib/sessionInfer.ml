(* Type inference abs(P): erase data, keep communication, control and timing. *)
open Lang

let seq a b = match a, b with
  | StySkip, x | x, StySkip -> x
  | _ -> StySeq (a, b)

let par a b = match a, b with
  | StySkip, x | x, StySkip -> x
  | _ -> StyParallel (a, b)

let atom (msg : message_specifier) = function
  | Instant -> AtomNBMsg msg
  | Blocking -> AtomBMsg msg

let send_atom (sp : send_pack) = atom sp.send_msg_spec sp.send_handshake
let recv_atom (rp : recv_pack) = atom rp.recv_msg_spec rp.recv_handshake

let arm_trigger = function
  | OfferAtom (OfferSend sp) -> AtomicAct (send_atom sp)
  | OfferAtom (OfferRecv (_, rp)) -> AtomicAct (recv_atom rp)
  | OfferAtom OfferWildcard -> AtomDelay 0
  | OfferConjunction atoms ->
      AtomConjunction (List.filter_map (function
        | OfferSend sp -> Some (send_atom sp)
        | OfferRecv (_, rp) -> Some (recv_atom rp)
        | OfferWildcard -> None) atoms)

let unsupported (e : expr_node) what =
  raise (Except.TypeError [ Text ("Type inference does not support " ^ what); Except.codespan_local e.span ])

let rec abs (funcs : func_def list) (e : expr_node) : session_type =
  let abs = abs funcs in
  (* Subexpressions start together and finish when all have. *)
  let all es = List.fold_left (fun acc e -> par acc (abs e)) StySkip es in
  let arm (offer_arm, body) = { trigger = arm_trigger offer_arm; continuation = Some (abs body) } in
  let attempt trigger then_e else_e =
    StyXOffer [ { trigger = AtomicAct trigger; continuation = Some (abs then_e) };
                { trigger = AtomDelay 0; continuation = Some (abs else_e) } ]
  in
  match e.d with
  | Literal _ | Identifier _ | Read _ | Ready _ | Probe _ | Sync _ | Debug _ -> StySkip
  | Tuple es | List es | Concat (es, _) -> all es
  | Binop (_, a, `Single b) -> all [ a; b ]
  | Binop (_, a, `List bs) -> all (a :: bs)
  | Unop (_, a) | Cast (a, _) | Indirect (a, _) | SharedAssign (_, a) | Let (_, _, a) -> abs a
  | Index (a, Single i) -> all [ a; i ]
  | Index (a, Range (i, n)) -> all [ a; i; n ]
  | Construct (_, v) -> all (Option.to_list v)
  | Record (_, fields, base) -> all (List.map snd fields @ Option.to_list base)
  | Call (id, args) ->
      (match List.find_opt (fun (f : func_def) -> f.name = id) funcs with
       | Some f -> seq (all args) (abs f.body)
       | None -> unsupported e ("an unknown function " ^ id))
  (* A register write takes one cycle. *)
  | Assign (_, v) -> par (abs v) (StyAtom (AtomDelay 1))
  | Join (a, b) -> par (abs a) (abs b)
  | Wait (a, b) -> seq (abs a) (abs b)
  | Cycle n -> if n <= 0 then StySkip else StyAtom (AtomDelay n)
  (* Only [fair if] and [fair xoffer] give fair choices. *)
  | IfExpr (c, t, f, fair) ->
      seq (abs c) (if fair then StyFairChoice (abs t, abs f) else StyChoice (abs t, abs f))
  | Match (v, arms) ->
      let bodies = List.map (fun (_, body) -> match body with Some b -> abs b | None -> StySkip) arms in
      (match List.rev bodies with
       | [] -> abs v
       | last :: rest -> seq (abs v) (List.fold_left (fun acc b -> StyChoice (b, acc)) last rest))
  | Send sp -> seq (abs sp.send_data) (StyAtom (AtomicAct (send_atom sp)))
  | Recv rp -> StyAtom (AtomicAct (recv_atom rp))
  | TrySend (sp, t, f) -> seq (abs sp.send_data) (attempt (send_atom sp) t f)
  | TryRecv (_, rp, t, f) -> attempt (recv_atom rp) t f
  | XOffer (arms, _, fair) -> if fair then StyFairXOffer (List.map arm arms) else StyXOffer (List.map arm arms)
  | Offer arms -> StyOffer (List.map arm arms)
  | OfferMatch (arms, cases) ->
      StyOfferMatch (List.map arm arms,
        List.map (fun (match_on, body) -> { match_on; match_body = abs body }) cases)
  | Recursion (id, body) -> StyRec (id, abs body)
  | Recursor id -> StyVar id
  | Recurse -> unsupported e "an anonymous recurse"

(* Whether an expression sends or receives anything (unknown calls count as yes). *)
let communicates funcs e =
  let rec has_msg sty = match sty with
    | StyAtom (AtomicAct _ | AtomConjunction _) | StyOffer _ | StyXOffer _ | StyFairXOffer _ | StyOfferMatch _ -> true
    | StySeq (a, b) | StyChoice (a, b) | StyFairChoice (a, b) | StyParallel (a, b) | StyLet (_, a, b) -> has_msg a || has_msg b
    | StyFuture a | StyRec (_, a) | StyForall (_, _, _, a, _) | StyAtom (AtomTerminal a) -> has_msg a
    | StyAtom (AtomDelay _) | StySkip | StyEnd _ | StyVar _ -> false
  in
  try has_msg (abs funcs e) with _ -> true

(* The type of one loop iteration; the loop body ends in recurse, which repetition restores. *)
let infer_thread funcs (thread : expr_node) =
  match thread.d with
  | Wait (body, { d = Recurse; _ }) -> abs funcs body
  | _ -> abs funcs thread


(* (pool instance, member, process, inferred type) for each spawn; interface i is thread i. *)
let spawned_member_types (procs : proc_def list) (funcs : func_def list) (body : proc_def_body) =
  List.concat_map (fun (sp : spawn_def ast_node) ->
    match sp.d.interface_params, List.find_opt (fun (p : proc_def) -> p.name = sp.d.proc) procs with
    | Some insts, Some { body = Native child; _ } ->
        List.concat (List.mapi (fun i (inst : ifc_instantiation) ->
          match List.nth_opt child.threads i with
          | Some (thread, _) ->
              let sty = infer_thread funcs thread in
              CliOutput.info "Inferred type of %s for %s.%s: %s" sp.d.proc inst.pid inst.pifc_id
                (string_of_protocol sty);
              [ (inst.pid, inst.pifc_id, sp.d.proc, sty) ]
          | None -> []) insts)
    | _ -> []) body.spawns

(* Inferred member types for every pool instantiated in [procs], keyed by (pool type, member). *)
let pool_member_types (procs : proc_def list) (funcs : func_def list) =
  let tbl = Hashtbl.create 16 in
  List.iter (fun (proc : proc_def) ->
    match proc.body with
    | Native body ->
        List.iter (fun (pool_inst, member, _, sty) ->
          match List.find_opt (fun (pi : pool_inst ast_node) -> pi.d.p_id = pool_inst) body.pool_insts with
          | Some pi when not (Hashtbl.mem tbl (pi.d.p_ty, member)) -> Hashtbl.replace tbl (pi.d.p_ty, member) sty
          | _ -> ()) (spawned_member_types procs funcs body)
    | Extern _ -> ()) procs;
  tbl
