(** JSON AST for the language server: schema v0.2.0 (Anvil v0.1.0 plus Pact constructs), with resolved definitions and session states. *)

open Lang

let schema_version = "v0.2.0"

module SM = Utils.StringMap

type json = Yojson.Basic.t

(* JSON helpers *)

let str s : json = `String s
let int n : json = `Int n
let bool b : json = `Bool b
let list f xs : json = `List (List.map f xs)
let opt f = function None -> `Null | Some x -> f x
let kind name fields : json = `Assoc (("kind", `String name) :: fields)

let code_span (s : Lang.code_span) : json =
  if s = code_span_dummy then `Null
  else
    let pos (p : Lexing.position) =
      `Assoc [("line", `Int p.pos_lnum); ("col", `Int (SourceColumn.utf16_column p))]
    in
    `Assoc [
      ("file_name", if s.st.pos_fname = "" then `Null else `String s.st.pos_fname);
      ("start", pos s.st);
      ("end", pos s.ed);
    ]

(** Removes duplicates, keeping the first occurrence of each element. *)
let dedup l = List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [x]) [] l

(** An [ast_node] wrapping [data], linked to the definitions [defs]. *)
let node ?(defs = []) (span : Lang.code_span) (data : json) : json =
  let defs = dedup (List.filter (fun s -> s <> code_span_dummy) defs) in
  kind "ast_node"
    ([("data", data); ("span", code_span span)]
     @ if defs = [] then [] else [("def_span", list code_span defs)])

let span_within (inner : Lang.code_span) (outer : Lang.code_span) =
  inner.st.pos_fname = outer.st.pos_fname
  && inner.st.pos_cnum >= outer.st.pos_cnum
  && inner.ed.pos_cnum <= outer.ed.pos_cnum

(* Name resolution *)

type endpoint = {
  ep_span : Lang.code_span; (** the defining endpoint or channel *)
  ep_class : identifier; (** its channel class *)
}

type scope = {
  types : type_def SM.t;
  macros : macro_def SM.t;
  funcs : func_def SM.t;
  procs : proc_def SM.t;
  classes : channel_class_def SM.t;
  interfaces : session_def ast_node SM.t;
  pools : interface_pool_def ast_node SM.t;
  regs : reg_def ast_node SM.t;
  endpoints : endpoint SM.t;
  pool_insts : pool_inst ast_node SM.t;
  shared : Lang.code_span SM.t;
  bindings : (Lang.code_span * data_type option) SM.t;
      (** [let], [try], offer-arm and function-argument bindings *)
  recursions : Lang.code_span SM.t; (** [rec X { ... }] blocks *)
  session_at : Lang.code_span -> (Lang.session_type option * Lang.session_type option) option;
      (** session type before/after the expression at a span; [None] = complete *)
}

(** Adds a binding unless already defined, so the first definition wins. *)
let add_first name v m = if SM.mem name m then m else SM.add name v m

let global_scope session_at (cunits : compilation_unit list) : scope =
  let collect f key = List.fold_left (fun m c ->
    List.fold_left (fun m x -> add_first (key x) x m) m (f c)) SM.empty cunits
  in
  {
    types = collect (fun c -> c.type_defs) (fun (t : type_def) -> t.name);
    macros = collect (fun c -> c.macro_defs) (fun (m : macro_def) -> m.id);
    funcs = collect (fun c -> c.func_defs) (fun (f : func_def) -> f.name);
    procs = collect (fun c -> c.procs @ c._extern_procs) (fun (p : proc_def) -> p.name);
    classes = collect (fun c -> c.channel_classes) (fun (cc : channel_class_def) -> cc.name);
    interfaces = collect (fun c -> c.session_defs) (fun (s : session_def ast_node) -> s.d.name);
    pools = collect (fun c -> c.pools) (fun (p : interface_pool_def ast_node) -> p.d.pool_id);
    regs = SM.empty;
    endpoints = SM.empty;
    pool_insts = SM.empty;
    shared = SM.empty;
    bindings = SM.empty;
    recursions = SM.empty;
    session_at;
  }

let bind sc name span dtype = { sc with bindings = SM.add name (span, dtype) sc.bindings }

(** [ep[i][j]] refers to the endpoint [ep]. *)
let endpoint_name (ep : identifier) =
  match String.index_opt ep '[' with Some i -> String.sub ep 0 i | None -> ep

let add_endpoint_defs (eps : endpoint_def ast_node list) m =
  List.fold_left (fun m (ep : endpoint_def ast_node) ->
    SM.add ep.d.name { ep_span = ep.span; ep_class = ep.d.channel_class } m) m eps

let add_channel_defs (chans : channel_def ast_node list) m =
  List.fold_left (fun m (ch : channel_def ast_node) ->
    let ep = { ep_span = ch.span; ep_class = ch.d.channel_class } in
    SM.add ch.d.endpoint_left ep m |> SM.add ch.d.endpoint_right ep) m chans

let find_message sc class_name msg_name : message_def option =
  match SM.find_opt class_name sc.classes with
  | Some cc -> List.find_opt (fun (m : message_def) -> m.name = msg_name) cc.messages
  | None -> None

(** The endpoint and message definitions of a message specifier. *)
let message_defs sc (ms : message_specifier) : Lang.code_span list =
  match SM.find_opt (endpoint_name ms.endpoint) sc.endpoints with
  | None -> []
  | Some ep ->
    ep.ep_span :: (find_message sc ep.ep_class ms.msg |> Option.map (fun (m : message_def) -> m.span) |> Option.to_list)

let message_dtype sc (ms : message_specifier) : data_type option =
  match SM.find_opt (endpoint_name ms.endpoint) sc.endpoints with
  | None -> None
  | Some ep ->
    (match find_message sc ep.ep_class ms.msg with
     | Some { sig_types = [st]; _ } -> Some st.dtype
     | _ -> None)

(** Resolves named types (following aliases) to their underlying data type. *)
let rec resolve_dtype ?(depth = 0) sc (dt : data_type) : data_type =
  match dt with
  | `Named (n, _) when depth < 16 ->
    (match SM.find_opt n sc.types with
     | Some td -> resolve_dtype ~depth:(depth + 1) sc td.body
     | None -> dt)
  | _ -> dt

let type_defs_of sc (dt : data_type) : Lang.code_span list =
  match dt with
  | `Named (n, _) -> SM.find_opt n sc.types |> Option.map (fun (t : type_def) -> t.span) |> Option.to_list
  | _ -> []

let field_of sc (dt : data_type option) (field : identifier) : (Lang.code_span * data_type) option =
  match Option.map (resolve_dtype sc) dt with
  | Some (`Record fields) ->
    List.find_map (fun (f : (identifier * data_type) ast_node) ->
      let (n, t) = f.d in if n = field then Some (f.span, t) else None) fields
  | _ -> None

(** A record field by name when the record type is unknown, if exactly one record type has it. *)
let unique_field sc (field : identifier) : Lang.code_span option =
  let spans = SM.fold (fun _ (td : type_def) acc ->
    match td.body with
    | `Record fields ->
      List.filter_map (fun (f : (identifier * data_type) ast_node) -> if fst f.d = field then Some f.span else None) fields @ acc
    | _ -> acc) sc.types []
  in
  match spans with [s] -> Some s | _ -> None

(** Field definitions for an access to [field] of a value of type [dt]. *)
let field_defs sc (dt : data_type option) (field : identifier) : Lang.code_span list * data_type option =
  match field_of sc dt field with
  | Some (span, t) -> ([span], Some t)
  | None when dt = None -> (Option.to_list (unique_field sc field), None)
  | None -> ([], None)

let element_dtype sc (dt : data_type option) : data_type option =
  match Option.map (resolve_dtype sc) dt with
  | Some (`Array (t, _)) -> Some t
  | _ -> None

(** The register and field definitions an lvalue refers to, and its type. *)
let rec lvalue_info sc (lv : lvalue) : Lang.code_span list * data_type option =
  match lv with
  | Reg r ->
    (match SM.find_opt r sc.regs with
     | Some reg -> ([reg.span], Some reg.d.d_type)
     | None -> ([], None))
  | Indexed (lv', _) ->
    let (defs, dt) = lvalue_info sc lv' in
    (defs, element_dtype sc dt)
  | Indirected (lv', field) ->
    let (defs, dt) = lvalue_info sc lv' in
    let (fdefs, fdt) = field_defs sc dt field in
    (defs @ fdefs, fdt)

(** The data type of an expression, where it is evident without type checking. *)
let rec expr_dtype sc (e : expr_node) : data_type option =
  match e.d with
  | Read lv -> snd (lvalue_info sc lv)
  | Identifier id -> (match SM.find_opt id sc.bindings with Some (_, dt) -> dt | None -> None)
  | Indirect (e', field) -> snd (field_defs sc (expr_dtype sc e') field)
  | Index (e', _) -> element_dtype sc (expr_dtype sc e')
  | Recv rp -> message_dtype sc rp.recv_msg_spec
  | Construct (cs, _) -> Some (`Named (cs.variant_ty_name, []))
  | Record (t, _, _) -> Some (`Named (t, []))
  | Cast (_, dt) -> Some dt
  | _ -> None

(* Basic constructs *)

let rec param_expr = function
  | ParamEnv.PE_Int n -> string_of_int n
  | PE_Id s -> s
  | PE_Add (a, b) -> Printf.sprintf "(%s + %s)" (param_expr a) (param_expr b)
  | PE_Sub (a, b) -> Printf.sprintf "(%s - %s)" (param_expr a) (param_expr b)
  | PE_Mul (a, b) -> Printf.sprintf "(%s * %s)" (param_expr a) (param_expr b)
  | PE_Div (a, b) -> Printf.sprintf "(%s / %s)" (param_expr a) (param_expr b)

(** A size; arithmetic expressions are emitted as [param]. *)
let int_maybe_param (p : int maybe_param) : json =
  match p with
  | ParamEnv.Concrete n -> `Assoc [("value", int n)]
  | Param s -> `Assoc [("param", str s)]
  | Expr e -> `Assoc [("param", str (param_expr e))]

let param (p : param) =
  kind "param" [
    ("name", str p.param_name);
    ("type", str (match p.param_ty with IntParam -> "int" | TypeParam -> "type"));
  ]

let message_specifier (ms : message_specifier) =
  kind "message_specifier" [("endpoint", str ms.endpoint); ("msg", str ms.msg)]

let literal (l : literal) : json =
  let digits ds = list (fun d -> int (value_of_digit d)) ds in
  match l with
  | Binary (n, bits) -> kind "literal" [("type", str "binary"); ("length", int n); ("digits", digits bits)]
  | Decimal (n, ds) -> kind "literal" [("type", str "decimal"); ("length", int n); ("digits", digits ds)]
  | Hexadecimal (n, hs) -> kind "literal" [("type", str "hex"); ("length", int n); ("digits", digits hs)]
  | WithLength (n, v) -> kind "literal" [("type", str "with_length"); ("length", int n); ("value", int v)]
  | NoLength v -> kind "literal" [("type", str "no_length"); ("value", int v)]

let rec data_type (dt : data_type) : json =
  kind "data_type" (
    match dt with
    | `Logic -> [("type", str "logic")]
    | `Array (t, size) -> [("type", str "array"); ("element", data_type t); ("size", int_maybe_param size)]
    | `Tuple ts -> [("type", str "tuple"); ("elements", list data_type ts)]
    | `Record fields ->
      (* the parser stores record fields in reverse order *)
      [("type", str "record");
       ("elements", list (fun (f : (identifier * Lang.data_type) ast_node) ->
          let (name, t) = f.d in
          node f.span (kind "type_element_def" [("name", str name); ("data_type", data_type t)]))
          (List.rev fields))]
    | `Variant (t, elems) ->
      [("type", str "variant");
       ("data_type", opt data_type t);
       ("elements", list (fun (v : (identifier * Lang.data_type option * Lang.literal option) ast_node) ->
          let (name, t, lit) = v.d in
          node v.span (kind "type_element_def" [
            ("name", str name); ("data_type", opt data_type t); ("literal", opt literal lit)]))
          elems)]
    | `Opaque name -> [("type", str "opaque"); ("name", str name)]
    | `Named (name, params) -> [("type", str "named"); ("name", str name); ("params", list param_value params)]
  )

and param_value (pv : param_value) : json =
  match pv with
  | IntParamValue n -> kind "param_value" [("type", str "int"); ("value", int n)]
  | TypeParamValue dt -> kind "param_value" [("type", str "type"); ("data_type", data_type dt)]

let rec array_dimensions (d : array_dimensions) : json =
  match d with
  | OneDim n -> kind "array_dimensions" [("type", str "one"); ("size", int_maybe_param n)]
  | MultiDim (n, sub) ->
    kind "array_dimensions" [("type", str "multi"); ("size", int_maybe_param n); ("sub", array_dimensions sub)]

let rec array_index_concrete (i : array_index_concrete) : json =
  match i with
  | IndexSingle n -> kind "array_index_concrete" [("type", str "single"); ("index", int n)]
  | IndexRange (s, n) -> kind "array_index_concrete" [("type", str "range"); ("start", int s); ("size", int n)]
  | IndexMultiDimRange (s, n, sub) ->
    kind "array_index_concrete" [("type", str "multi_range"); ("start", int s); ("size", int n); ("sub", array_index_concrete sub)]
  | IndexMultiDimSingle (n, sub) ->
    kind "array_index_concrete" [("type", str "multi_single"); ("index", int n); ("sub", array_index_concrete sub)]

let delay_pat (d : delay_pat) : json =
  kind "delay_pat" (
    match d with
    | `Cycles n -> [("type", str "cycles"); ("value", int n)]
    | `Message_with_offset (ms, o, plus) ->
      [("type", str "message"); ("value", message_specifier ms); ("offset", int (if plus then o else -o))]
    | `Eternal -> [("type", str "eternal")])

let delay_pat_chan_local (d : delay_pat_chan_local) : json =
  kind "delay_pat_chan_local" (
    match d with
    | `Cycles n -> [("type", str "cycles"); ("value", int n)]
    | `Message_with_offset (m, o, plus) ->
      [("type", str "message"); ("value", str m); ("offset", int (if plus then o else -o))]
    | `Eternal -> [("type", str "eternal")])

let sig_type_chan_local (st : sig_type_chan_local) =
  kind "sig_type_chan_local" [
    ("data_type", data_type st.dtype);
    ("lifetime", kind "sig_lifetime_chan_local" [("ending", delay_pat_chan_local st.lifetime.e)]);
  ]

let sync_mode (m : message_sync_mode) =
  kind "message_sync_mode" (
    match m with
    | Dynamic -> [("type", str "dynamic")]
    | Static (init, interval) -> [("type", str "static"); ("init", int init); ("interval", int interval)]
    | Dependent (msg, delay) -> [("type", str "dependent"); ("msg", str msg); ("delay", int delay)])

let handshake (h : handshake_kind) = str (match h with Blocking -> "blocking" | Instant -> "instant")

(* Session types *)

let rec session_type (s : session_type) : json =
  let sty ty fields = kind "session_type" (("type", str ty) :: fields) in
  match s with
  | StyEnd id -> sty "end" [("id", str id)]
  | StySeq (a, b) -> sty "seq" [("first", session_type a); ("then", session_type b)]
  | StyChoice (a, b) -> sty "choice" [("left", session_type a); ("right", session_type b)]
  | StyFairChoice (a, b) -> sty "fair_choice" [("left", session_type a); ("right", session_type b)]
  | StyParallel (a, b) -> sty "parallel" [("left", session_type a); ("right", session_type b)]
  | StyAtom a -> sty "atom" [("action", session_action a)]
  | StyFuture s -> sty "future" [("body", session_type s)]
  | StySkip -> sty "skip" []
  | StyOffer arms -> sty "offer" [("arms", list offering arms)]
  | StyXOffer arms -> sty "xoffer" [("arms", list offering arms)]
  | StyFairXOffer arms -> sty "fair_xoffer" [("arms", list offering arms)]
  | StyOfferMatch (arms, cases) ->
    sty "offer_match" [
      ("arms", list offering arms);
      ("cases", list (fun (c : offer_match_case) ->
         kind "session_match_case" [
           ("on", opt (list message_specifier) c.match_on);
           ("body", session_type c.match_body)]) cases)]
  | StyLet (id, v, body) -> sty "let" [("id", str id); ("value", session_type v); ("body", session_type body)]
  | StyRec (id, body) -> sty "rec" [("id", str id); ("body", session_type body)]
  | StyVar id -> sty "var" [("id", str id)]
  | StyForall (op, id, QuantRange (lo, hi), body, excluded) ->
    sty "forall" [
      ("op", str (match op with QuantSum -> "choice" | QuantProduct -> "parallel" | QuantOffer -> "offer" | QuantXOffer -> "xoffer"));
      ("id", str id);
      ("range", `Assoc [("from", int lo); ("to", int hi)]);
      ("excluded", list int (match excluded with
         | None -> [] | Some (QuantSingleInt n) -> [n] | Some (QuantIntList ns) -> ns));
      ("body", session_type body)]

and session_action (a : atomic_action_with_gap) : json =
  let act ty fields = kind "session_action" (("type", str ty) :: fields) in
  let message = function
    | AtomBMsg ms -> act "message" [("blocking", bool true); ("msg_spec", message_specifier ms)]
    | AtomNBMsg ms -> act "message" [("blocking", bool false); ("msg_spec", message_specifier ms)]
  in
  match a with
  | AtomDelay n -> act "delay" [("cycles", int n)]
  | AtomicAct m -> message m
  | AtomTerminal s -> act "terminal" [("session_type", session_type s)]
  | AtomConjunction ms -> act "conjunction" [("actions", list message ms)]

and offering (o : offering_session_type) : json =
  kind "session_offering" [
    ("trigger", session_action o.trigger);
    ("continuation", opt session_type o.continuation);
  ]

(** A session type in Pact syntax, parenthesised by precedence ([F] > [+] > [||] > [;]). *)
let rec session_text ?(prec = 0) (s : session_type) : string =
  let paren level text = if prec > level then "(" ^ text ^ ")" else text in
  match s with
  | StySkip -> "()"
  | StyEnd id -> "$" ^ id
  | StySeq (a, b) -> paren 0 (session_text ~prec:1 a ^ " ; " ^ session_text b)
  | StyParallel (a, b) -> paren 1 (session_text ~prec:1 a ^ " || " ^ session_text ~prec:2 b)
  | StyChoice (a, b) -> paren 2 (session_text ~prec:2 a ^ " + " ^ session_text ~prec:3 b)
  | StyFairChoice (a, b) -> paren 2 (session_text ~prec:2 a ^ " ++ " ^ session_text ~prec:3 b)
  | StyFuture s -> paren 3 ("F " ^ session_text ~prec:3 s)
  | StyAtom a -> action_text a
  | StyOffer arms -> "&(" ^ offerings_text arms ^ ")"
  | StyXOffer arms -> "^(" ^ offerings_text arms ^ ")"
  | StyFairXOffer arms -> "^^(" ^ offerings_text arms ^ ")"
  | StyOfferMatch (arms, cases) ->
    "&(" ^ offerings_text arms ^ ").(" ^ String.concat ", " (List.map (fun (c : offer_match_case) ->
      let on = match c.match_on with
        | None -> "*"
        | Some [m] -> string_of_msg_spec m
        | Some ms -> "{" ^ String.concat ", " (List.map string_of_msg_spec ms) ^ "}"
      in
      on ^ " : " ^ session_text c.match_body) cases) ^ ")"
  | StyLet (id, v, body) ->
    paren 0 ("let " ^ id ^ " = " ^ session_text ~prec:3 v ^ " in " ^ session_text ~prec:3 body)
  | StyRec (id, body) -> paren 0 ("rec " ^ id ^ " . " ^ session_text ~prec:3 body)
  | StyVar id -> id
  | StyForall (op, id, QuantRange (lo, hi), body, excluded) ->
    let excluded = match excluded with
      | None -> ""
      | Some (QuantSingleInt n) -> Printf.sprintf " not %d" n
      | Some (QuantIntList ns) -> " not (" ^ String.concat ", " (List.map string_of_int ns) ^ ")"
    in
    let op, body = match op, body with
      | QuantOffer, StyOffer arms -> ("&", offerings_text arms)
      | QuantXOffer, StyXOffer arms -> ("^", offerings_text arms)
      | QuantProduct, _ -> ("||", session_text body)
      | _ -> ("+", session_text body)
    in
    Printf.sprintf "forall (%s : [%d..%d]%s) %s { %s }" id lo hi excluded op body

and action_text (a : atomic_action_with_gap) : string =
  let message = function
    | AtomBMsg ms -> string_of_msg_spec ms
    | AtomNBMsg ms -> "#" ^ string_of_msg_spec ms
  in
  match a with
  | AtomDelay 0 -> "*"
  | AtomDelay n -> "#" ^ string_of_int n
  | AtomicAct m -> message m
  | AtomTerminal s -> "$ " ^ session_text ~prec:3 s
  | AtomConjunction ms -> "{" ^ String.concat ", " (List.map message ms) ^ "}"

and offerings_text (arms : offering_session_type list) : string =
  String.concat ", " (List.map (fun (o : offering_session_type) ->
    match o.continuation with
    | None -> action_text o.trigger
    | Some c -> action_text o.trigger ^ " : " ^ session_text c) arms)

(** Nodes for the session-type names within [within], linked to their definitions. *)
let session_refs sc ~endpoints ?protocol_class (refs : session_ref list) (within : Lang.code_span) : json =
  let refs = List.filter (function
    | SessionMsgRef (_, s) | SessionVarRef (_, s) | SessionBinderRef (_, s, _) -> span_within s within) refs
  in
  let binders = List.filter_map (function
    | SessionBinderRef (id, s, scope) -> Some (id, s, scope) | _ -> None) refs
  in
  let size (s : Lang.code_span) = s.ed.pos_cnum - s.st.pos_cnum in
  let innermost_binder id span =
    List.filter (fun (b, _, scope) -> b = id && span_within span scope) binders
    |> List.sort (fun (_, _, a) (_, _, b) -> compare (size a) (size b))
    |> function (_, s, _) :: _ -> [s] | [] -> []
  in
  list (fun r ->
    match r with
    | SessionMsgRef (ms, span) ->
      let defs = match protocol_class with
        | Some cls -> find_message sc cls ms.msg |> Option.map (fun (m : message_def) -> m.span) |> Option.to_list
        | None -> message_defs { sc with endpoints } ms
      in
      node ~defs span (kind "session_message" [("endpoint", str ms.endpoint); ("msg", str ms.msg)])
    | SessionVarRef (id, span) ->
      node ~defs:(innermost_binder id span) span (kind "session_var" [("var", str id)])
    | SessionBinderRef (id, span, _) ->
      node span (kind "session_binder" [("name", str id)])) refs

(* Expressions *)

let rec expr_node sc (e : expr_node) : json =
  let (defs, data) = expr sc e in
  let data =
    match sc.session_at e.span, data with
    | Some (before, after), `Assoc fields when before <> after ->
      let text = opt (fun s -> str (session_text s)) in
      `Assoc (fields @ [("session", `Assoc [("before", text before); ("after", text after)])])
    | _ -> data
  in
  node ~defs e.span data

and expr sc (e : expr_node) : Lang.code_span list * json =
  let x = expr_node sc in
  let ex ty fields = kind "expr" (("type", str ty) :: fields) in
  match e.d with
  | Literal l -> ([], ex "literal" [("value", literal l)])
  | Identifier id ->
    let defs = match SM.find_opt id sc.bindings with
      | Some (s, _) -> [s]
      | None ->
        (match SM.find_opt id sc.macros with
         | Some m -> [m.span]
         | None -> SM.find_opt id sc.shared |> Option.to_list)
    in
    (defs, ex "identifier" [("id", str id)])
  | Call (f, args) ->
    (SM.find_opt f sc.funcs |> Option.map (fun (f : func_def) -> f.span) |> Option.to_list,
     ex "Call" [("function", str f); ("args", list x args)])
  | Assign (lv, v) ->
    (fst (lvalue_info sc lv), ex "assign" [("lvalue", lvalue sc lv); ("expr", x v)])
  | Binop (op, a, b) ->
    ([], ex "binop" [
       ("op", str (binop_name op));
       ("lhs", x a);
       ("rhs", match b with
         | `Single v -> kind "singleton_or_list" [("type", str "single"); ("value", x v)]
         | `List vs -> kind "singleton_or_list" [("type", str "list"); ("values", list x vs)])])
  | Unop (op, a) ->
    ([], ex "unop" [
       ("op", str (match op with Neg -> "neg" | Not -> "not" | AndAll -> "and_all" | OrAll -> "or_all"));
       ("expr", x a)])
  | Tuple es -> ([], ex "tuple" [("elements", list x es)])
  | Let (ids, dt, v) ->
    (Option.fold ~none:[] ~some:(type_defs_of sc) dt,
     ex "let" [("data_type", opt data_type dt); ("ids", list str ids); ("expr", x v)])
  | Join (a, b) | Wait (a, b) ->
    (* a [let] on the left binds its names in the right-hand side *)
    let sc' = match a.d with
      | Let (ids, dt, v) ->
        let dt = match dt, ids with
          | Some _, _ -> dt
          | None, [_] -> expr_dtype sc v
          | None, _ -> None
        in
        List.fold_left (fun sc id -> bind sc id a.span (if List.length ids = 1 then dt else None)) sc ids
      | _ -> sc
    in
    let ty = match e.d with Join _ -> "join" | _ -> "wait" in
    ([], ex ty [("lhs", x a); ("rhs", expr_node sc' b)])
  | Cycle n -> ([], ex "cycle" [("cycles", int n)])
  | Sync id -> (SM.find_opt id sc.shared |> Option.to_list, ex "sync" [("id", str id)])
  | IfExpr (c, t, f, fair) -> ([], ex "if_expr" [("cond", x c); ("then", x t); ("else", x f); ("fair", bool fair)])
  | TryRecv (id, rp, t, f) ->
    let sc' = bind sc id e.span (message_dtype sc rp.recv_msg_spec) in
    ([], ex "try_recv" [("id", str id); ("recv_pack", recv_pack sc rp); ("then", expr_node sc' t); ("else", x f)])
  | TrySend (sp, t, f) ->
    ([], ex "try_send" [("send_pack", send_pack sc sp); ("then", x t); ("else", x f)])
  | Construct (cs, arg) ->
    let (variant_defs, type_defs) = match SM.find_opt cs.variant_ty_name sc.types with
      | Some td ->
        let variants = match td.body with
          | `Variant (_, vs) ->
            List.filter_map (fun (v : (identifier * Lang.data_type option * Lang.literal option) ast_node) ->
              let (n, _, _) = v.d in if n = cs.variant then Some v.span else None) vs
          | _ -> []
        in
        (variants, [td.span])
      | None -> ([], [])
    in
    (variant_defs @ type_defs,
     ex "construct" [
       ("spec", kind "constructor_spec" [("type_name", str cs.variant_ty_name); ("name", str cs.variant)]);
       ("arg", opt x arg)])
  | Record (ty, fields, base) ->
    let dt = Some (`Named (ty, [])) in
    (type_defs_of sc (`Named (ty, [])),
     ex "record" [
       ("type_name", str ty);
       ("elements", list (fun ((id, v) : identifier * expr_node) ->
          node ~defs:(fst (field_defs sc dt id)) v.span (kind "record_element" [("id", str id); ("value", x v)]))
          fields);
       ("base", opt x base)])
  | Index (a, idx) -> ([], ex "index" [("expr", x a); ("index", index sc idx)])
  | Indirect (a, field) ->
    (fst (field_defs sc (expr_dtype sc a) field), ex "indirect" [("expr", x a); ("field", str field)])
  | Concat (es, flat) -> ([], ex "concat" [("elements", list x es); ("flat", bool flat)])
  | Cast (a, dt) -> (type_defs_of sc dt, ex "cast" [("expr", x a); ("data_type", data_type dt)])
  | Ready ms -> (message_defs sc ms, ex "ready" [("msg_spec", message_specifier ms)])
  | Probe ms -> (message_defs sc ms, ex "probe" [("msg_spec", message_specifier ms)])
  | Match (v, branches) ->
    ([], ex "match" [
       ("expr", x v);
       ("branches", list (fun (pat, br) ->
          kind "branch" [("pattern", x pat); ("branch", opt x br)]) branches)])
  | XOffer (arms, selector, fair) ->
    ([], ex "xoffer" [
       ("fair", bool fair);
       ("arms", list (offer_arm sc) arms);
       ("selector", opt (fun (id, order) ->
          `Assoc [("id", str id); ("order", str (match order with OrderRotate -> "rotate" | OrderTree -> "tree"))])
          selector)])
  | Offer arms -> ([], ex "offer" [("arms", list (offer_arm sc) arms)])
  | OfferMatch (arms, cases) ->
    ([], ex "offer_match" [
       ("arms", list (offer_arm sc) arms);
       ("cases", list (fun ((on, body) : offer_match_arm) ->
          kind "offer_match_case" [("on", opt (list message_specifier) on); ("body", x body)]) cases)])
  | Read lv -> (fst (lvalue_info sc lv), ex "read" [("target", lvalue sc lv)])
  | Debug (DebugPrint (msg, args)) ->
    ([], ex "debug" [("op", kind "debug_op" [("type", str "debug_print"); ("msg", str msg); ("args", list x args)])])
  | Debug DebugFinish -> ([], ex "debug" [("op", kind "debug_op" [("type", str "debug_finish")])])
  | Send sp -> ([], ex "send" [("send_pack", send_pack sc sp)])
  | Recv rp -> ([], ex "recv" [("recv_pack", recv_pack sc rp)])
  | SharedAssign (id, v) -> (SM.find_opt id sc.shared |> Option.to_list, ex "shared_assign" [("id", str id); ("expr", x v)])
  | List es -> ([], ex "list" [("elements", list x es)])
  | Recursion (id, body) ->
    let sc' = { sc with recursions = SM.add id e.span sc.recursions } in
    ([], ex "recursion" [("id", str id); ("body", expr_node sc' body)])
  | Recursor id -> (SM.find_opt id sc.recursions |> Option.to_list, ex "recursor" [("id", str id)])
  | Recurse -> ([], ex "recurse" [])

and binop_name = function
  | Add -> "add" | Sub -> "sub" | Xor -> "xor" | And -> "and" | Or -> "or"
  | Lt -> "lt" | Gt -> "gt" | Lte -> "lte" | Gte -> "gte" | Shl -> "shl" | Shr -> "shr"
  | Eq -> "eq" | Neq -> "neq" | Mul -> "mul" | In -> "in" | LAnd -> "land" | LOr -> "lor"

and msg_spec_node sc (ms : message_specifier) (span : Lang.code_span) =
  node ~defs:(message_defs sc ms) span (message_specifier ms)

and send_pack sc (sp : send_pack) =
  kind "send_pack" [
    ("msg_spec", msg_spec_node sc sp.send_msg_spec sp.send_msg_span);
    ("data", expr_node sc sp.send_data);
    ("handshake", handshake sp.send_handshake);
  ]

and recv_pack sc (rp : recv_pack) =
  kind "recv_pack" [
    ("msg_spec", msg_spec_node sc rp.recv_msg_spec rp.recv_msg_span);
    ("handshake", handshake rp.recv_handshake);
  ]

and offer_arm sc ((arm, body) : offer_arm_type * expr_node) =
  let atoms = match arm with OfferAtom a -> [a] | OfferConjunction l -> l in
  (* [x = recv ...] binds [x] in the arm body; the arm itself has no span *)
  let sc' = List.fold_left (fun sc a ->
    match a with
    | OfferRecv (id, rp) -> bind sc id body.span (message_dtype sc rp.recv_msg_spec)
    | _ -> sc) sc atoms
  in
  let atom a =
    match a with
    | OfferSend sp -> kind "offer_arm_atom" [("type", str "send"); ("send_pack", send_pack sc sp)]
    | OfferRecv (id, rp) -> kind "offer_arm_atom" [("type", str "recv"); ("id", str id); ("recv_pack", recv_pack sc rp)]
    | OfferWildcard -> kind "offer_arm_atom" [("type", str "wildcard")]
  in
  kind "offer_arm" [
    ("type", str (match arm with OfferAtom _ -> "atom" | OfferConjunction _ -> "conjunction"));
    ("atoms", list atom atoms);
    ("body", expr_node sc' body);
  ]

and lvalue sc (lv : lvalue) : json =
  match lv with
  | Reg r -> kind "lvalue" [("type", str "reg"); ("id", str r)]
  | Indexed (lv', idx) -> kind "lvalue" [("type", str "indexed"); ("lvalue", lvalue sc lv'); ("index", index sc idx)]
  | Indirected (lv', field) -> kind "lvalue" [("type", str "indirected"); ("lvalue", lvalue sc lv'); ("field", str field)]

and index sc (idx : index) : json =
  match idx with
  | Single e -> kind "index" [("type", str "single"); ("expr", expr_node sc e)]
  | Range (a, b) -> kind "index" [("type", str "range"); ("start", expr_node sc a); ("size", expr_node sc b)]

(* Definitions *)

let class_defs sc (cls : identifier) =
  SM.find_opt cls sc.classes |> Option.map (fun (cc : channel_class_def) -> cc.span) |> Option.to_list

let endpoint_def sc (ep : endpoint_def ast_node) =
  let e = ep.d in
  node ~defs:(class_defs sc e.channel_class) ep.span (kind "endpoint_def" [
    ("name", str e.name);
    ("channel_class", str e.channel_class);
    ("channel_params", list param_value e.channel_params);
    ("dir", str (match e.dir with Left -> "left" | Right -> "right"));
    ("foreign", bool e.foreign);
    ("opp", opt str e.opp);
    ("num_instances", opt array_dimensions e.num_instances);
  ])

let channel_def sc (ch : channel_def ast_node) =
  let c = ch.d in
  node ~defs:(class_defs sc c.channel_class) ch.span (kind "channel_def" [
    ("channel_class", str c.channel_class);
    ("channel_params", list param_value c.channel_params);
    ("endpoint_left", str c.endpoint_left);
    ("endpoint_right", str c.endpoint_right);
    ("visibility", str (match c.visibility with
       | BothForeign -> "both_foreign" | LeftForeign -> "left_foreign" | RightForeign -> "right_foreign"));
    ("num_instances", opt array_dimensions c.n_instances);
  ])

let message_def (m : message_def) =
  kind "message_def" [
    ("name", str m.name);
    ("dir", str (match m.dir with Inp -> "in" | Out -> "out"));
    ("send_sync", sync_mode m.send_sync);
    ("recv_sync", sync_mode m.recv_sync);
    ("sig_types", list sig_type_chan_local m.sig_types);
    ("span", code_span m.span);
    ("handshake", opt (fun h -> str (match h with ValidAck -> "valid_ack" | ValidReady -> "valid_ready")) m.handshake_mode);
  ]

let channel_class_def sc refs (cc : channel_class_def) =
  kind "channel_class_def" [
    ("name", str cc.name);
    ("messages", list message_def cc.messages);
    ("params", list param cc.params);
    ("span", code_span cc.span);
    ("protocol", opt (fun (p : Lang.session_type ast_node) ->
       kind "protocol" [
         ("session_type", node p.span (session_type p.d));
         ("refs", session_refs sc ~endpoints:SM.empty ~protocol_class:cc.name refs p.span)])
       cc.local_sty);
  ]

let type_def (t : type_def) =
  kind "type_def" [
    ("name", str t.name);
    ("data_type", data_type t.body);
    ("params", list param t.params);
    ("span", code_span t.span);
  ]

let macro_def (m : macro_def) =
  kind "macro_def" [("id", str m.id); ("value", int m.value); ("span", code_span m.span)]

let typed_arg (a : typed_arg) =
  kind "typed_arg" [("name", str a.arg_name); ("data_type", opt data_type a.arg_type); ("span", code_span a.span)]

let func_def sc (f : func_def) =
  let sc' = List.fold_left (fun sc (a : typed_arg) -> bind sc a.arg_name a.span a.arg_type) sc f.args in
  kind "func_def" [
    ("name", str f.name);
    ("args", list typed_arg f.args);
    ("body", expr_node sc' f.body);
    ("span", code_span f.span);
  ]

let import_directive (i : import_directive) =
  kind "import_directive" [("file_name", str i.file_name); ("is_extern", bool i.is_extern); ("span", code_span i.span)]

let interface_defs sc (name : identifier) =
  SM.find_opt name sc.interfaces |> Option.map (fun (s : session_def ast_node) -> s.span) |> Option.to_list

let interface_def sc refs (n : session_def ast_node) =
  let s = n.d in
  let endpoints = add_endpoint_defs s.params SM.empty in
  node n.span (kind "interface_def" [
    ("name", str s.name);
    ("params", list (endpoint_def sc) s.params);
    ("data_params", list param s.data_params);
    ("session_type", node s.body.span (session_type s.body.d));
    ("refs", session_refs sc ~endpoints refs n.span);
  ])

let pool_def sc refs (n : interface_pool_def ast_node) =
  let p = n.d in
  let endpoints = add_channel_defs p.pool_channels SM.empty in
  let member (m : interface_mem_def ast_node) =
    let defs = match m.d.interface_class_id with
      | Some inst -> interface_defs sc inst.id
      | None -> []
    in
    node ~defs m.span (kind "pool_member" [
      ("name", str m.d.inf_mem_id);
      ("interface", opt (fun (i : interface_instantiation) -> str i.id) m.d.interface_class_id);
      ("endpoints", list str (match m.d.interface_class_id with Some i -> i.params | None -> []));
      ("session_type", opt session_type m.d.interface_def);
      ("refs", session_refs sc ~endpoints refs m.span);
    ])
  in
  node n.span (kind "pool_def" [
    ("name", str p.pool_id);
    ("channels", list (channel_def sc) p.pool_channels);
    ("members", list member p.interface_members);
  ])

(** The scope inside a process: registers, endpoints (including interface ones), pools and shared values. *)
let proc_scope sc (p : proc_def) : scope =
  let interface_endpoints = List.concat_map (fun (i : identifier ast_node) ->
    match SM.find_opt i.d sc.interfaces with
    | Some s -> s.d.params
    | None -> []) p.interface
  in
  let endpoints = SM.empty |> add_endpoint_defs interface_endpoints |> add_endpoint_defs p.args in
  match p.body with
  | Extern _ -> { sc with endpoints }
  | Native body ->
    {
      sc with
      regs = List.fold_left (fun m (r : reg_def ast_node) -> SM.add r.d.name r m) SM.empty body.regs;
      endpoints = add_channel_defs body.channels endpoints;
      pool_insts = List.fold_left (fun m (pi : pool_inst ast_node) -> SM.add pi.d.p_id pi m) SM.empty body.pool_insts;
      shared = List.fold_left (fun m (v : shared_var_def ast_node) -> SM.add v.d.ident v.span m) SM.empty body.shared_vars;
    }

let spawn_def sc (sp : spawn_def ast_node) =
  let s = sp.d in
  let defs =
    (SM.find_opt s.proc sc.procs |> Option.map (fun (p : proc_def) -> p.span) |> Option.to_list)
    @ List.concat_map (fun (i : ifc_instantiation) ->
        SM.find_opt i.pid sc.pool_insts |> Option.map (fun (pi : pool_inst ast_node) -> pi.span) |> Option.to_list)
      (Option.value ~default:[] s.interface_params)
  in
  node ~defs sp.span (kind "spawn_def" [
    ("proc", str s.proc);
    ("params", list (fun a ->
       match a with
       | SingleEp ep -> kind "args_spawn" [("type", str "single"); ("endpoint", str ep)]
       | IndexedEp (ep, idx) ->
         kind "args_spawn" [("type", str "indexed"); ("endpoint", str ep); ("dimensions", array_index_concrete idx)])
       s.params);
    ("compile_params", list param_value s.compile_params);
    ("interface_params", opt (list (fun (i : ifc_instantiation) ->
       `Assoc [("pool", str i.pid); ("member", str i.pifc_id)])) s.interface_params);
  ])

let proc_body sc (body : proc_def_body_maybe_extern) =
  match body with
  | Native b ->
    kind "proc_def_body" [
      ("type", str "native");
      ("channels", list (channel_def sc) b.channels);
      ("spawns", list (spawn_def sc) b.spawns);
      ("regs", list (fun (r : reg_def ast_node) ->
         node ~defs:(type_defs_of sc r.d.d_type) r.span (kind "reg_def" [
           ("name", str r.d.name); ("data_type", data_type r.d.d_type); ("init", opt str r.d.init)])) b.regs);
      ("shared_vars", list (fun (v : shared_var_def ast_node) ->
         node v.span (kind "shared_var_def" [
           ("ident", str v.d.ident);
           ("assigning_thread", int v.d.assigning_thread);
           ("shared_lifetime", kind "sig_lifetime" [("ending", delay_pat v.d.shared_lifetime.e)])])) b.shared_vars);
      ("threads", list (fun ((e, rst) : expr_node * message_specifier option) ->
         kind "thread" [("expr", expr_node sc e); ("span", code_span e.span); ("rst", opt message_specifier rst)])
         b.threads);
      ("pool_insts", list (fun (pi : pool_inst ast_node) ->
         let defs = SM.find_opt pi.d.p_ty sc.pools |> Option.map (fun (p : interface_pool_def ast_node) -> p.span) |> Option.to_list in
         node ~defs pi.span (kind "pool_inst" [("name", str pi.d.p_id); ("pool", str pi.d.p_ty)])) b.pool_insts);
    ]
  | Extern (module_name, b) ->
    kind "proc_def_body" [
      ("type", str "extern");
      ("module_name", str module_name);
      ("named_ports", list (fun (name, ty) -> `Assoc [("name", str name); ("type", str ty)]) b.named_ports);
      ("msg_ports", list (fun (ms, data, valid, ack) ->
         `Assoc [
           ("msg_spec", message_specifier ms);
           ("data_port", opt str data);
           ("valid_port", opt str valid);
           ("ack_port", opt str ack)]) b.msg_ports);
    ]

let proc_def sc (p : proc_def) =
  let sc' = proc_scope sc p in
  kind "proc_def" [
    ("name", str p.name);
    ("args", list (endpoint_def sc) p.args);
    ("body", proc_body sc' p.body);
    ("params", list param p.params);
    ("span", code_span p.span);
    ("interfaces", list (fun (i : identifier ast_node) ->
       node ~defs:(interface_defs sc i.d) i.span (kind "interface_ref" [("interface", str i.d)])) p.interface);
  ]

let compilation_unit sc (c : compilation_unit) =
  kind "compilation_unit" [
    ("schema", str schema_version);
    ("file_name", opt str c.cunit_file_name);
    ("channel_classes", list (channel_class_def sc c.session_refs) c.channel_classes);
    ("type_defs", list type_def c.type_defs);
    ("macro_defs", list macro_def c.macro_defs);
    ("func_defs", list (func_def sc) c.func_defs);
    ("procs", list (proc_def sc) c.procs);
    ("imports", list import_directive c.imports);
    ("_extern_procs", list (proc_def sc) c._extern_procs);
    ("interfaces", list (interface_def sc c.session_refs) c.session_defs);
    ("pools", list (pool_def sc c.session_refs) c.pools);
  ]

(** Session types before and after the expression at [span], from {!SessionTrace}. *)
let traced_session_at (span : Lang.code_span) =
  SessionTrace.find span
  |> Option.map (fun ((start_ev, end_ev) : EventGraph.event * EventGraph.event) ->
    let residual (ev : EventGraph.event) = Option.map (fun (n : Lang.session_type ast_node) -> n.d) ev.session_type in
    (residual start_ev, residual end_ev))

(** Serialises the compilation units, resolving names across all of them. *)
let of_compilation_units ?(session_at = fun _ -> None) (cunits : compilation_unit list) : json =
  let sc = global_scope session_at cunits in
  list (compilation_unit sc) cunits
