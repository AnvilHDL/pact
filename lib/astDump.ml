(* Graph of a parsed compilation unit, as DOT. *)

open Lang

let escape s =
  let b = Buffer.create (String.length s) in
  String.iter (function
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | c -> Buffer.add_char b c) s;
  Buffer.contents b

let send_kw (sp : send_pack) = match sp.send_handshake with Instant -> "isend" | Blocking -> "send"
let recv_kw (rp : recv_pack) = match rp.recv_handshake with Instant -> "irecv" | Blocking -> "recv"

let channel_lifetime (lt : sig_lifetime_chan_local) = match lt.e with
  | `Cycles n -> Printf.sprintf "#%d" n
  | `Eternal -> "E"
  | `Message_with_offset (msg, offset, plus) ->
    Printf.sprintf "%s%+d" msg (if plus then offset else -offset)

(* Literals as written in source; digits are stored least significant first. *)
let literal = function
  | Binary (n, bits) -> Printf.sprintf "%d'b%s" n (String.concat "" (List.rev_map string_of_digit bits))
  | Decimal (n, ds) -> Printf.sprintf "%d'd%s" n (String.concat "" (List.rev_map string_of_digit ds))
  | Hexadecimal (n, hs) -> Printf.sprintf "%d'h%s" n (String.concat "" (List.rev_map string_of_digit hs))
  | WithLength (n, v) -> Printf.sprintf "%d'd%d" n v
  | NoLength v -> string_of_int v

let rec lvalue = function
  | Reg r -> r
  | Indexed (lv, idx) -> lvalue lv ^ "[" ^ string_of_index idx ^ "]"
  | Indirected (lv, f) -> lvalue lv ^ "." ^ f

(* Label of an expression and its children, each with an optional edge label. *)
let expr_parts (e : expr) : string * (string option * expr_node) list =
  let plain es = List.map (fun x -> (None, x)) es in
  let arm_label = function
    | OfferSend sp -> send_kw sp ^ " " ^ string_of_msg_spec sp.send_msg_spec
    | OfferRecv (id, rp) -> id ^ " = " ^ recv_kw rp ^ " " ^ string_of_msg_spec rp.recv_msg_spec
    | OfferWildcard -> "else"
  in
  let arm_data = function
    | OfferSend sp -> [(Some "data", sp.send_data)]
    | _ -> []
  in
  let arms name list =
    (name, List.concat_map (fun (arm, body) ->
      let label, data = match arm with
        | OfferAtom a -> (arm_label a, arm_data a)
        | OfferConjunction atoms ->
          ("{" ^ String.concat "; " (List.map arm_label atoms) ^ "}",
           List.concat_map arm_data atoms)
      in
      data @ [(Some label, body)]) list)
  in
  match e with
  | Literal l -> (literal l, [])
  | Identifier i -> (i, [])
  | Call (f, args) -> ("call " ^ f, plain args)
  | Assign (lv, v) -> ("set " ^ lvalue lv, [(Some ":=", v)])
  | Binop (op, a, `Single b) -> (string_of_binop op, [(Some "lhs", a); (Some "rhs", b)])
  | Binop (op, a, `List bs) -> (string_of_binop op, (Some "lhs", a) :: plain bs)
  | Unop (op, a) -> (string_of_unop op, [(None, a)])
  | Tuple es -> ("tuple", plain es)
  | Let (ids, dt, v) ->
    ("let " ^ String.concat ", " ids
     ^ (match dt with Some t -> " : " ^ string_of_data_type t | None -> ""), [(None, v)])
  | Join (a, b) -> (";", [(Some "first", a); (Some "then", b)])
  | Wait (a, b) -> (">>", [(Some "first", a); (Some "then", b)])
  | Cycle n -> (Printf.sprintf "cycle %d" n, [])
  | Sync i -> ("sync " ^ i, [])
  | IfExpr (c, t, f) -> ("if", [(Some "cond", c); (Some "then", t); (Some "else", f)])
  | TryRecv (id, rp, ok, fail) ->
    (Printf.sprintf "try %s = %s %s" id (recv_kw rp) (string_of_msg_spec rp.recv_msg_spec),
     [(Some "ok", ok); (Some "else", fail)])
  | TrySend (sp, ok, fail) ->
    (Printf.sprintf "try %s %s" (send_kw sp) (string_of_msg_spec sp.send_msg_spec),
     [(Some "data", sp.send_data); (Some "ok", ok); (Some "else", fail)])
  | Construct (cs, v) -> (cs.variant_ty_name ^ "::" ^ cs.variant, plain (Option.to_list v))
  | Record (name, fields, base) ->
    ("record " ^ name,
     List.map (fun (f, v) -> (Some f, v)) fields
     @ List.map (fun b -> (Some "base", b)) (Option.to_list base))
  | Index (a, idx) -> ("[" ^ string_of_index idx ^ "]", [(None, a)])
  | Indirect (a, f) -> ("." ^ f, [(None, a)])
  | Concat (es, _) -> ("concat", plain es)
  | Cast (a, dt) -> ("cast " ^ string_of_data_type dt, [(None, a)])
  | Ready m -> ("ready " ^ string_of_msg_spec m, [])
  | Probe m -> ("probe " ^ string_of_msg_spec m, [])
  | Match (subject, cases) ->
    ("match",
     (Some "subject", subject)
     :: List.concat_map (fun (pat, body) ->
          (Some "case", pat) :: List.map (fun b -> (Some "=>", b)) (Option.to_list body)) cases)
  | XOffer (list, sel) ->
    arms ("xoffer" ^ (match sel with Some s -> " " ^ s | None -> "")) list
  | Offer list -> arms "offer" list
  | OfferMatch (list, cases) ->
    let label, kids = arms "offer" list in
    (label ^ " match", kids @ List.map (fun (on, body) -> (Some (string_of_match_on on), body)) cases)
  | Read lv -> ("*" ^ lvalue lv, [])
  | Debug (DebugPrint (fmt, es)) -> ("dprint \"" ^ fmt ^ "\"", plain es)
  | Debug DebugFinish -> ("dfinish", [])
  | Send sp -> (send_kw sp ^ " " ^ string_of_msg_spec sp.send_msg_spec, [(Some "data", sp.send_data)])
  | Recv rp -> (recv_kw rp ^ " " ^ string_of_msg_spec rp.recv_msg_spec, [])
  | SharedAssign (i, v) -> ("put " ^ i, [(None, v)])
  | List es -> ("list", plain es)
  | Recursion (id, body) -> ("rec " ^ id, [(None, body)])
  | Recursor id -> ("recurse " ^ id, [])
  | Recurse -> ("recurse", [])

let print (cunit : compilation_unit) out =
  let counter = ref 0 in
  let node ?(shape = "box") ?(style = "") label =
    incr counter;
    let id = Printf.sprintf "n%d" !counter in
    Printf.fprintf out "  %s [label=\"%s\", shape=%s%s];\n" id (escape label) shape
      (if style = "" then "" else ", style=" ^ style);
    id
  in
  let edge ?label a b =
    match label with
    | Some l -> Printf.fprintf out "  %s -> %s [label=\"%s\"];\n" a b (escape l)
    | None -> Printf.fprintf out "  %s -> %s;\n" a b
  in
  let rec expr (e : expr_node) =
    let label, kids = expr_parts e.d in
    let id = node ~shape:(if kids = [] then "plaintext" else "ellipse") label in
    List.iter (fun (role, k) -> edge ?label:role id (expr k)) kids;
    id
  in
  let group parent title = let id = node ~style:"rounded" title in edge parent id; id in
  Printf.fprintf out "digraph ast {\n  node [fontname=\"monospace\"];\n";
  let root = node ~style:"bold" (Option.value cunit.cunit_file_name ~default:"<stdin>") in

  if cunit.type_defs <> [] then begin
    let g = group root "types" in
    List.iter (fun (t : type_def) ->
      edge g (node (t.name ^ " = " ^ string_of_data_type t.body))) cunit.type_defs
  end;

  List.iter (fun (cc : channel_class_def) ->
    let messages = List.map (fun (m : message_def) ->
      let sigs = List.map (fun (s : sig_type_chan_local) ->
        string_of_data_type s.dtype ^ "@" ^ channel_lifetime s.lifetime) m.sig_types in
      let handshake = match m.handshake_mode with
        | Some ValidAck -> " >>" | Some ValidReady -> " <<" | None -> "" in
      Printf.sprintf "%s %s : (%s)%s" (match m.dir with Inp -> "left" | Out -> "right")
        m.name (String.concat ", " sigs) handshake) cc.messages in
    edge root (node (String.concat "\n" (("chan " ^ cc.name) :: messages)))) cunit.channel_classes;

  if cunit.session_defs <> [] then begin
    let g = group root "interfaces" in
    List.iter (fun (s : session_def ast_node) ->
      edge g (node (s.d.name ^ " = " ^ string_of_protocol s.d.body.d))) cunit.session_defs
  end;

  List.iter (fun (pool : interface_pool_def ast_node) ->
    edge root (node ("pool " ^ pool.d.pool_id ^ "\n"
      ^ String.concat ", " (List.map (fun (m : interface_mem_def ast_node) -> m.d.inf_mem_id)
          pool.d.interface_members)))) cunit.pools;

  List.iter (fun (proc : proc_def) ->
    let p = node ~style:"bold"
      (Printf.sprintf "proc %s(%s)" proc.name
         (String.concat ", " (List.map (fun (ep : endpoint_def ast_node) ->
            ep.d.name ^ " : " ^ ep.d.channel_class) proc.args))) in
    edge root p;
    match proc.body with
    | Extern (mod_name, _) -> edge p (node ("extern " ^ mod_name))
    | Native body ->
      let decls =
        List.map (fun (r : reg_def ast_node) ->
          "reg " ^ r.d.name ^ " : " ^ string_of_data_type r.d.d_type) body.regs
        @ List.map (fun (c : channel_def ast_node) ->
          Printf.sprintf "chan %s -- %s : %s" c.d.endpoint_left c.d.endpoint_right c.d.channel_class) body.channels
        @ List.map (fun (s : spawn_def ast_node) -> "spawn " ^ s.d.proc) body.spawns
      in
      if decls <> [] then edge p (node (String.concat "\n" decls));
      List.iteri (fun i ((e : expr_node), _) ->
        edge ~label:(Printf.sprintf "thread %d" i) p (expr e)) body.threads) cunit.procs;
  Printf.fprintf out "}\n"
