(** This module includes definitions relevant to the language constructs, including
those that are part of the AST created during parsing. *)

(** A span of source code. *)
type code_span = {
  st : Lexing.position; (** start of the span *)
  ed : Lexing.position; (** end of the span *)
}

(** A dummy code span that does not represent any valid span. *)
let code_span_dummy = { st = Lexing.dummy_pos; ed = Lexing.dummy_pos }

type 'a maybe_param = 'a ParamEnv.maybe_param

type identifier = string

(** A node in AST. Containing the data plus the code span info. *)
type 'a ast_node = {
  span : code_span;
  d : 'a;
}

(** Construct an AST node with specified data and span. *)
let ast_node_of_data st ed d = { span = {st; ed}; d }
let tag_with_span s d = { span = s; d }
let dummy_ast_node_of_data d = { span = code_span_dummy; d }

let data_of_ast_node n = n.d

(** Type of a parameter. *)
type param_type =
  | IntParam (** an integer constant *)
  | TypeParam (** a type *)

(** A compile-time parameter. *)
type param = {
  param_name : identifier;
  param_ty : param_type;
}

(** This identifies a message type within the context of a process.
It consists of the {{!endpoint}endpoint name} and the {{!msg}message type name}.
*)
type message_specifier = {
  endpoint : identifier;
  msg : identifier;
}

let string_of_msg_spec (msg_spec : message_specifier) : string =
  msg_spec.endpoint ^ "." ^ msg_spec.msg

(** A delay pattern that matches a set of delays. *)
type delay_pat = [
  | `Cycles of int (** elapse of a number of cycles *)
  | `Message_with_offset of (message_specifier*int*bool) (** sending/receiving of a message of a specific type with an offset *)
  | `Eternal (** matches no delays *)
]

(** A delay pattern local to a specific channel. Being channel-local means that the message type
does not include an endpoint name component. *)
type delay_pat_chan_local = [ `Cycles of int | `Eternal | `Message_with_offset of (identifier * int * bool) ]

let string_of_delay_pat (t : delay_pat) : string =
  match t with
  | `Cycles n -> Printf.sprintf "#%d" n
  | `Message_with_offset (msg_spec, offset, plus) ->
      Printf.sprintf "%s%+d" (string_of_msg_spec msg_spec) (if plus then offset else -offset)
  | `Eternal -> "E"

(** Lifetime signature, specifying that the lifetime lasts until matching {{!sig_lifetime.e}ending} delay patterns. *)
type sig_lifetime = { e: delay_pat; }

(** Same as {!sig_lifetime} but local to a channel. *)
type sig_lifetime_chan_local = { e: delay_pat_chan_local; }

let string_of_lifetime (lt : sig_lifetime) : string =
  Printf.sprintf "%s" (string_of_delay_pat lt.e)

let sig_lifetime_this_cycle_chan_local : sig_lifetime_chan_local =
  { e = `Cycles 1 }

let sig_lifetime_const_chan_local : sig_lifetime_chan_local =
  { e = `Eternal }

let sig_lifetime_this_cycle : sig_lifetime =
  { e = `Cycles 1 }

let sig_lifetime_const : sig_lifetime =
  { e = `Eternal }


(** Direction of an endpoint. *)
type endpoint_direction = Left | Right

(** Atomic actions for session types *)
type atomic_action =
  | AtomBMsg of message_specifier (** atomic blocking message action *)
  | AtomNBMsg of message_specifier (** atomic non-blocking message action *)

and atomic_action_with_gap =
  | AtomDelay of int (** atomic delay action *)
  | AtomicAct of atomic_action
  | AtomTerminal of session_type (** terminal action for interface session types *)
  | AtomConjunction of atomic_action list

and session_type =
  | StyEnd of identifier (** progress marker $ *)
  | StySeq of session_type * session_type (** sequence *)
  | StyChoice of session_type * session_type (** internal choice (+ operator) *)
  | StyXOffer of offering_session_type list (** dual choice (XOR operator) *)
  | StyFairChoice of session_type * session_type (** fair internal choice *)
  | StyFairXOffer of offering_session_type list (** fair exclusive offer *)
  | StyAtom of atomic_action_with_gap (** single atomic action *)
  | StyParallel of session_type * session_type (** parallel composition of session types *)
  | StyFuture of session_type (** future operator (F) **)
  | StySkip (** skip session type **)
  | StyOffer of offering_session_type list (** offer operator (dual of choice) **)
  | StyOfferMatch of offering_session_type list * offer_match_case list
    (** offer continued by the case for exactly the arms taken *)
  | StyLet of identifier * session_type * session_type (** let binding for session types **)
  | StyRec of identifier * session_type (** recursive session type **)
  | StyVar of identifier (** [metaprogramming] session type variable **)
  | StyForall of quant_operator*identifier*quant_type*session_type*(quant_member option)  (** [metaprogramming] session type variable **)


and quant_operator =
  | QuantSum      (** ∑ - internal choice *)
  | QuantProduct  (** ∏ - parallel composition *)
  | QuantOffer    (** ∧ - external choice (offer) *)
  | QuantXOffer   (** ⊕ - exclusive choice *)

and quant_type =
  | QuantRange of int*int

and quant_member =
  | QuantSingleInt of int
  | QuantIntList of int list


and offering_session_type = {
  trigger: atomic_action_with_gap;
  continuation: session_type option;
}

(** A case of an offer match: the messages of the arms taken, or [None] for
    every combination not listed. *)
and offer_match_case = {
  match_on : message_specifier list option;
  match_body : session_type;
}




(** A data type. *) 
type bit = [`Z0 | `Z1]
type digit = [`Z0 | `Z1 | `Z2 | `Z3 | `Z4 | `Z5 | `Z6 | `Z7 | `Z8 | `Z9]
type hexit = [`Z0 | `Z1 | `Z2 | `Z3 | `Z4 | `Z5 | `Z6 | `Z7 | `Z8 | `Z9 |
            `Za | `Zb | `Zc | `Zd | `Ze | `Zf]
type all_digit = hexit

type literal =
| Binary of int * bit list
| Decimal of int * digit list
| Hexadecimal of int * hexit list
| WithLength of int * int
| NoLength of int


let string_of_digit d : string =
  match d with
  | `Z0 -> "0"
  | `Z1 -> "1"
  | `Z2 -> "2"
  | `Z3 -> "3"
  | `Z4 -> "4"
  | `Z5 -> "5"
  | `Z6 -> "6"
  | `Z7 -> "7"
  | `Z8 -> "8"
  | `Z9 -> "9"
  | `Za -> "a"
  | `Zb -> "b"
  | `Zc -> "c"
  | `Zd -> "d"
  | `Ze -> "e"
  | `Zf -> "f"

let value_of_digit d : int =
  match d with
  | `Z0 -> 0x0
  | `Z1 -> 0x1
  | `Z2 -> 0x2
  | `Z3 -> 0x3
  | `Z4 -> 0x4
  | `Z5 -> 0x5
  | `Z6 -> 0x6
  | `Z7 -> 0x7
  | `Z8 -> 0x8
  | `Z9 -> 0x9
  | `Za -> 0xa
  | `Zb -> 0xb
  | `Zc -> 0xc
  | `Zd -> 0xd
  | `Ze -> 0xe
  | `Zf -> 0xf



let literal_bit_len (lit : literal) : int option =
  match lit with
  | Binary (n, _) | Decimal (n, _) | Hexadecimal (n, _) | WithLength (n, _) -> Some n
  | NoLength v -> Some (Utils.int_log2 (v + 1))

let literal_eval (lit : literal) : int =
  match lit with
  | Binary (_, b) ->
      List.fold_left (fun n x -> n * 2 + (value_of_digit x)) 0 b
  | Decimal (_, d) ->
      List.fold_left (fun n x -> n * 10 + (value_of_digit x)) 0 d
  | Hexadecimal (_, h) ->
      List.fold_left (fun n x -> n * 16 + (value_of_digit x)) 0 h
  | WithLength (_, v) -> v
  | NoLength v -> v

let dtype_of_literal (lit : literal) =
  let n = literal_bit_len lit |> Option.get in
  match n with
  | 1 -> `Logic
  | _ -> `Array (`Logic, ParamEnv.Concrete n)

(** A data type. *)
type data_type = [
  | `Logic
  | `Array of data_type * int maybe_param
  | `Variant of (data_type option)*((identifier * (data_type option)*(literal option)) ast_node list) (** ADT sum type *)
  | `Record of (identifier * data_type) ast_node list (** ADT product type *)
  | `Tuple of data_type list
  | `Opaque of identifier (** type reserved for internal purposes *)
  | `Named of identifier * param_value list (** named type which can be concretised
                                            parameter values; the name itself might be
                                            a parameter *)
  (* | `Endpoint of endpoint_def * first-class endpoints *)
]
and param_value =
  | IntParamValue of int
  | TypeParamValue of data_type

(** Endpoint definition. A pair is
created once a channel class
is instantiated. *)
type array_dimm_concrete =
  | OneDimmension of int
  | MultiDimmension of int * array_dimm_concrete

type array_index_concrete =
  | IndexSingle of int
  | IndexRange of (int *int)
  | IndexMultiDimRange of (int * int * array_index_concrete)
  | IndexMultiDimSingle of (int*array_index_concrete)
  


type array_dimensions =
  | OneDim of (int maybe_param)
  | MultiDim of (int maybe_param)*(array_dimensions)


type endpoint_def = {
  name: identifier;
  channel_class: identifier;
  channel_params: param_value list;
  dir: endpoint_direction; (** direction of the endpoint *)
  (* used by this process? *)
  foreign: bool; (** must this endpoint be passed to other processes rather than
  used within this process? *)
  opp: identifier option; (** if the endpoint is created locally, the other endpoint associated
  with the same channel *)
  num_instances : array_dimensions option (** number of instances for arrayed channels *)
}

(** A macro definition. *)

type macro_def = {
  id: identifier;
  value : int;
  span: code_span;
}

(** A type definition ([type name = body])*)
and type_def = {
  name: identifier;
  body: data_type;
  params: param list; (** list of parameters *)
  span: code_span;
}

(** A session type definition ([session name = body])*)
and session_def = {
  name: identifier;
  body: session_type ast_node;
  params: endpoint_def ast_node list; (** list of session parameters *)
  data_params : param list; (** list of data type parameters *)
}

(** Unit type. Basically an empty tuple. *)
let unit_dtype = `Tuple []

(** Number of bits required to hold the tag for a variant type. *)
let variant_tag_size (v: [>`Variant of (data_type option)*((identifier * (data_type option)*(literal option)) ast_node list)]) : int =
  match v with
  | `Variant (_, vlist) -> List.length vlist |> Utils.int_log2

(** Data type a variant type constructor. *)
let variant_lookup_dtype (v: [> `Variant of (data_type option)*((identifier * (data_type option) * (literal option)) ast_node list)]) (cstr: identifier) : data_type option =
    match v with
    | `Variant (_, vlist) ->
      List.find_opt (fun {d = (x,_,_); _} -> x = cstr) vlist |> Option.map (fun {d = (_,dt,_); _} -> dt) |> Option.join

(** Index of a variant type constructor. *)
let variant_lookup_index (v: [> `Variant of (data_type option)*((identifier * (data_type option) * (literal option)) ast_node list)]) (cstr: identifier) : int option =
  let res : int option ref = ref None in
  match v with
  | `Variant (_,vlist) ->
      List.iteri (fun i {d = (x,_,v); _} ->
        if Option.is_none !res then begin
          if x = cstr then
            if Option.is_none v then
              res := Some i
            else res := Some (Option.get v |> literal_eval )
          else ()
        end else ()) vlist;
  !res

type 'a sig_type_general = {
  dtype: data_type;
  lifetime: 'a;
}

(** Signal type, including both data type and the lifetime signature. *)
type sig_type = sig_lifetime sig_type_general

(** Same as {!sig_type} but local to a channel. *)
type sig_type_chan_local = sig_lifetime_chan_local sig_type_general

(** Convert a channel-local delay pattern to a global (process context) delay pattern. *)
let delay_pat_globalise (endpoint : identifier) (t : delay_pat_chan_local) : delay_pat =
  match t with
  | `Message_with_offset (msg, offset, plus) -> `Message_with_offset ({endpoint = endpoint; msg = msg}, offset, plus)
  | `Cycles n -> `Cycles n
  | `Eternal -> `Eternal

(** Convert a channel-local lifetime signature to a global (process context) lifetime signature. *)
let lifetime_globalise (endpoint : identifier) (lt : sig_lifetime_chan_local) : sig_lifetime =
  { e = delay_pat_globalise endpoint lt.e }

(** Convert a channel-local signal type to a global (process context) signal type. *)
let sig_type_globalise (endpoint : identifier) (s : sig_type_chan_local) : sig_type =
  {
    dtype = s.dtype;
    lifetime = lifetime_globalise endpoint s.lifetime
  }

(** A register definition. {!reg_def.init} specifies the initial value of the register. *)
type reg_def = {
  name: string;
  d_type: data_type;
  init: string option;
}

type reg_def_list = reg_def list

type message_direction = Inp | Out

(** Synchronisation mode of a message type. *)
type message_sync_mode =
  | Dynamic (** dynamic synchronisation, e.g., through [valid]/[ack] handshakes *)
  | Static of int * int (** (init offset, static interval) *)
  | Dependent of string * int (** relative to another message (msg, delay) **)

type handshake_modes =
  | ValidAck  (** valid/ack handshake *)
  | ValidReady (** valid/ready handshake *)

(** Whether a message operation waits for its peer. A property of the
    operation, not of the message type. *)
type handshake_kind =
  | Blocking (** two-way handshake ([send]/[recv]) *)
  | Instant (** one-way handshake ([isend]/[irecv]) *)

let string_of_handshake_kind = function
  | Blocking -> "blocking"
  | Instant -> "instantaneous"



(** A message type definition, as part of a channel definition. *)
type message_def = {
  name: identifier;
  dir: message_direction;
  send_sync: message_sync_mode; (** how to synchronise when data is available *)
  recv_sync: message_sync_mode; (** how to synchronise when data is acknowledged *)
  handshake_mode: handshake_modes option;
    (** explicit handshake override; [None] means it is derived from use *)
  sig_types: sig_type_chan_local list; (** the signal types of the values carried in the message *)
  span: code_span; (** code span of the message definition *)
}

(** A channel class definition, containing a list of message type definitions. *)
type channel_class_def = {
  name: identifier;
  messages: message_def list;
  params: param list;  (** List of generic parameters *)
  span: code_span; (** code span of the channel class definition *)
  local_sty: session_type ast_node option; (** local session type, if any *)
}

(** The visibility of a channel. *)
type channel_visibility =
| BothForeign (** not visible locally, must be passed to other processes *)
| LeftForeign (** the left endpoint is not visible locally but the right one is *)
| RightForeign (** the right endpoint is not visible locally but the left one is *)

(** A channel (instantiation of a channel class) definition. *)
type channel_def = {
  channel_class: identifier;
  channel_params: param_value list;
  endpoint_left: identifier;
  endpoint_right: identifier;
  visibility: channel_visibility;
  n_instances : array_dimensions option; (** number of instances for arrayed channels To Do: add support for parametrization *) 
}

type interface_pool_def = {
  pool_id : identifier;
  pool_channels : channel_def ast_node list;
  interface_members : interface_mem_def ast_node list;
}

and interface_mem_def ={
  inf_mem_id : identifier;
  interface_class_id : interface_instantiation option;
  interface_def : session_type option
}

and interface_instantiation = {
  id : identifier;
  params : identifier list;
}

(* expressions *)


type binop = Add | Sub | Xor | And | Or | Lt | Gt | Lte | Gte |
             Shl | Shr | Eq | Neq | Mul | In | LAnd | LOr
type unop  = Neg | Not | AndAll | OrAll

(* TODO: these are SV-specific; move elsewhere *)
let string_of_binop (binop: binop) : string =
  match binop with
  | Add -> "+"
  | Sub -> "-"
  | Xor -> "^"
  | And -> "&"
  | Or -> "|"
  | LAnd -> "&&"
  | LOr -> "||"
  | Lt -> "<"
  | Gt -> ">"
  | Lte -> "<="
  | Gte -> ">="
  | Shl -> "<<"
  | Shr -> ">>"
  | Eq -> "=="
  | Neq -> "!="
  | Mul -> "*"
  | In -> "inside"

let string_of_unop (unop: unop) : string =
  match unop with
  | Neg -> "-"
  | Not -> "~"
  | AndAll -> "&"
  | OrAll -> "|"

type 'a singleton_or_list = [
  | `Single of 'a
  | `List of 'a list
]

(** Information specified in a message send operation. *)
type send_pack = {
  send_msg_spec: message_specifier;
  send_msg_span: code_span; (** code span of the message specifier *)
  send_data: expr_node;
  send_handshake: handshake_kind; (** [Blocking] for [send], [Instant] for [isend] *)
}

(** Information specified in a message receive operation. *)
and recv_pack = {
  recv_msg_spec: message_specifier;
  recv_msg_span: code_span; (** code span of the message specifier *)
  recv_handshake: handshake_kind; (** [Blocking] for [recv], [Instant] for [irecv] *)
}
and constructor_spec = {
  variant_ty_name: identifier;
  variant: identifier;
}
(** A message type. This is a pair of the message type name and the direction. *)

(** An expression. This is the basic building block for a program. *)
and expr =
  | Literal of literal
  | Identifier of identifier
  | Call of identifier *(expr_node list)
  (* send and recv *)
  | Assign of lvalue * expr_node
  | Binop of binop * expr_node * (expr_node singleton_or_list)
  | Unop of unop * expr_node
  | Tuple of expr_node list
  | Let of identifier list * data_type option * expr_node
  | Join of expr_node * expr_node (** [a; b] *)
  | Wait of expr_node * expr_node (** [a => b] *)
  | Cycle of int
  | Sync of identifier (** synchronise on a shared value *)
  | IfExpr of expr_node * expr_node * expr_node
  | TryRecv of identifier * recv_pack * expr_node * expr_node (** try recv *)
  | TrySend of send_pack * expr_node * expr_node (** try send *)
  | Construct of constructor_spec * expr_node option (** construct a variant type value with a constructor *)
  | Record of identifier * (identifier * expr_node) list * expr_node option (** constructing a record-type value *)
  | Index of expr_node * index (** an element of an array ([a[3]]) *)
  | Indirect of expr_node * identifier (** a member of a record ([a.b]) *)
  | Concat of expr_node list * bool
  | Cast of expr_node * data_type (** cast an expression to a specific data type *)
  | Ready of message_specifier (** [ready(a, b)] *)
  | Probe of message_specifier (** [probe(a, b)] *)
  | Match of expr_node * ((expr_node * expr_node option) list)
  | XOffer of ((offer_arm_type * expr_node) list) * ((identifier * xoffer_order) option)
    (** exclusive offer with an optional selector wire and the order it imposes *)
  | Offer of ((offer_arm_type * expr_node) list)
  | OfferMatch of ((offer_arm_type * expr_node) list) * offer_match_arm list
    (** offer continued by the arm for exactly the offer arms taken *)
  | Read of lvalue (** reading a value from a register (leading to a borrow) *)
  | Debug of debug_op
  | Send of send_pack
  | Recv of recv_pack
  | SharedAssign of identifier * expr_node (** make ready a shared value *)
  | List of expr_node list (** array/list of expressions *)
  | Recursion of identifier * expr_node (** define a recursive block *)
  | Recursor of identifier  (** invoke a recursive block *)
  | Recurse
and expr_node = expr ast_node

(** How an xoffer's selector orders its arms. *)
and xoffer_order =
  | OrderRotate (** try arm [selector + i] at step [i], wrapping around *)
  | OrderTree (** try arm [selector XOR i] at step [i], as a binary-tree round-robin arbiter *)

(** Messages of the offer arms taken, or [None] for any other combination. *)
and offer_match_arm = message_specifier list option * expr_node

and offer_arm_atom_type =
  | OfferSend of send_pack
  | OfferRecv of identifier * recv_pack
  | OfferWildcard
  
and offer_arm_type =
  | OfferAtom of offer_arm_atom_type
  | OfferConjunction of offer_arm_atom_type list

(** A "location" that can be assigned to. *)
and lvalue =
  | Reg of identifier (** a register *)
  | Indexed of lvalue * index (** lvalue[index] *)
  | Indirected of lvalue * identifier (** lvalue.field *)

(** Indexing, either a single point or a range. *)
and index =
  | Single of expr_node
  | Range of expr_node * expr_node (** a range, the second component is the size which must be literal *)

and debug_op =
  | DebugPrint of string * expr_node list
  | DebugFinish

let delay_immediate = `Cycles 0
let delay_single_cycle = `Cycles 1

type sig_def = {
  name: identifier;
  stype: sig_type;
}

type cycle_proc = {
  trans_func: expr_node;
  sigs: sig_def list;
}

(** A spawn of a process. *)
type spawn_def = {
  proc: identifier;
  (* channels to pass as args *)
  (* TODO: this naming collides with compile-time parameters *)
  mutable params: args_spawn list; (** names of the endpoints passed to the spawned process *)
  interface_params: (ifc_instantiation list) option; (** interface name and endpoint name pairs passed to the spawned process *)
  compile_params: param_value list; (** concrete param value list *)
}
and ifc_instantiation = {
  pid : identifier;
  pifc_id : identifier;
}

and args_spawn = 
  | SingleEp of identifier
  | IndexedEp of identifier * array_index_concrete

(* TODO: specify the type? *)
type shared_var_def = {
  ident: identifier;
  assigning_thread: int;
  shared_lifetime: sig_lifetime;
}

type interface_spawn = {
  intfc_id : identifier;
  intfc_args : identifier list;
}

(** Process body. *)
type proc_def_body = {
  (* new channels available to this process *)
  mutable channels: channel_def ast_node list;
  pool_insts: (pool_inst ast_node) list;  (* pool instantiations *)
  (* processes spawned by this process *)
  spawns: spawn_def ast_node list;
  regs: reg_def ast_node list;
  shared_vars: shared_var_def ast_node list;  (* New field *)
  (* prog: expr; *)
  threads: (expr_node * message_specifier option) list; (** the second component is the optional reset signal *)
}

and pool_inst = {
  p_id : identifier;  (* pool instance id *)
  p_ty : identifier;  (* pool type name *)
}

(** Extern process definition *)
type proc_def_body_extern = {
  named_ports : (string * string) list;
  msg_ports : (message_specifier * string option * string option * string option) list;
  (** data, valid, and ack ports *)
}

type proc_def_body_maybe_extern =
  | Native of proc_def_body
  | Extern of string * proc_def_body_extern (** module name and port bindings *)

(** Process definition. *)
type proc_def = {
  name: string;
  (* arguments are endpoints passed from outside *)
  interface : (identifier ast_node) list; (** optional interface name *)
  mutable args: endpoint_def ast_node list; (** endpoints passed from outside *)
  body: proc_def_body_maybe_extern; (** process body *)
  params: param list; (** compile-time parameters *)
  span: code_span; (** code span of the process definition *)
}

(** An import directive for importing code from other files. *)
type import_directive = {
  file_name : string;
  is_extern : bool; (** is this import external?
      Currently an external import means importing SystemVerilog code *)
  span: code_span;
}
type typed_arg = {
  arg_name: identifier;
  arg_type: data_type option; (** type of the argument, if any *)
  span: code_span;
}

type func_def =  {
  name: identifier;
  args: typed_arg list;
  body: expr_node;
  span: code_span;
}
(** A channel class definition, which is a set of message types. *)

(** A name in a session type with its span, recorded by the parser for tooling. *)
type session_ref =
  | SessionMsgRef of message_specifier * code_span (** a message action [ep.m] or [#ep.m] *)
  | SessionVarRef of identifier * code_span (** a use of a [rec] or [let] variable *)
  | SessionBinderRef of identifier * code_span * code_span
    (** a [rec] or [let] variable binding: the name's span and the span of its scope *)

(** A compilation unit, corresponding to a source file. *)
type compilation_unit = {
  cunit_file_name : string option; (** filename in which the compilation unit resides *)
  channel_classes: channel_class_def list;
  type_defs: type_def list;
  pools : interface_pool_def ast_node list;
  session_defs: session_def ast_node list;
  macro_defs: macro_def list;
  func_defs : func_def list;
  procs: proc_def list;
  imports : import_directive list;
  _extern_procs : proc_def list; (** processes that are external, usable but not built *)
  session_refs : session_ref list; (** names referenced in this unit's session types, in source order *)
}

let cunit_empty : compilation_unit =
  {cunit_file_name = None; channel_classes = []; type_defs = [];
  session_defs = []; procs = []; imports = []; _extern_procs = []; macro_defs = []; func_defs = []; pools = [];
  session_refs = []}

let cunit_add_channel_class
  (c : compilation_unit) (cc : channel_class_def) : compilation_unit =
  {c with channel_classes = cc::c.channel_classes}

let cunit_add_type_def (c : compilation_unit) (ty : type_def) : compilation_unit =
  {c with type_defs = ty::c.type_defs}

let cunit_add_session_def (c : compilation_unit) (sess : session_def ast_node) : compilation_unit =
  {c with session_defs = sess::c.session_defs}

let cunit_add_interface_pool_def (c : compilation_unit) (pool : interface_pool_def ast_node) : compilation_unit =
  {c with pools = pool::c.pools}

let cunit_add_func_def (c : compilation_unit) (f : func_def) : compilation_unit =
  {c with func_defs = f::c.func_defs}
let cunit_add_macro_def (c : compilation_unit) (macro : macro_def) :
  compilation_unit = {c with macro_defs = macro::c.macro_defs}
let cunit_add_proc
  (c : compilation_unit) (p : proc_def) : compilation_unit =
  {c with procs = p::c.procs}

let cunit_add_import (c : compilation_unit) (im : import_directive) : compilation_unit =
  {c with imports = im::c.imports}

(** Reverse a message direction. *)
let reverse (msg_dir : message_direction) : message_direction =
  match msg_dir with
  | Inp -> Out
  | Out -> Inp

let get_message_direction (msg_dir : message_direction)
            (endpoint_dir : endpoint_direction) : message_direction =
  match endpoint_dir with
  | Left -> msg_dir
  | Right -> reverse msg_dir

let string_of_channel_class (cc : channel_class_def) : string =
  Printf.sprintf "Channel class %s" cc.name
let rec string_of_expr (e : expr) : string =
  match e with
  | Literal lit -> "Literal " ^ string_of_literal lit
  | Identifier id -> "Identifier " ^ id
  | Let (ids, dtype_opt, e) ->
      let ty_str = match dtype_opt with Some dt -> ": " ^ string_of_data_type dt | None -> "" in
      "Let (" ^ String.concat ", " ids ^ ty_str ^ " = " ^ string_of_expr e.d ^ ")"
  | Assign (lv, n) -> "Assign (" ^ string_of_lvalue lv ^ ", " ^ string_of_expr n.d ^ ")"
  | Call (f, args) ->
      "Call " ^ f ^ "(" ^ String.concat ", " (List.map (fun a -> string_of_expr a.d) args) ^ ")"
  | Binop (op, e1, e2_sol) ->
      let rhs = match e2_sol with
        | `Single e2 -> string_of_expr e2.d
        | `List es -> "[" ^ String.concat "; " (List.map (fun e -> string_of_expr e.d) es) ^ "]"
      in
      "Binop (" ^ string_of_binop op ^ ", " ^ string_of_expr e1.d ^ ", " ^ rhs ^ ")"
  | Unop (op, e) -> "Unop (" ^ string_of_unop op ^ ", " ^ string_of_expr e.d ^ ")"
  | Tuple es ->
      (match es with
       | [] -> "Unit"
       | _ -> "Tuple (" ^ String.concat ", " (List.map (fun e -> string_of_expr e.d) es) ^ ")")
  | Join (e1, e2) -> "Join (" ^ string_of_expr e1.d ^ "; " ^ string_of_expr e2.d ^ ")"
  | Wait (e1, e2) -> "Wait (" ^ string_of_expr e1.d ^ " => " ^ string_of_expr e2.d ^ ")"
  | Cycle n -> "Cycle " ^ string_of_int n
  | Sync id -> "Sync " ^ id
  | IfExpr (cond, then_e, else_e) ->
      "If (" ^ string_of_expr cond.d ^ ") { " ^ string_of_expr then_e.d ^ " } else { " ^ string_of_expr else_e.d ^ " }"
  | TryRecv (id, rp, ok_e, fail_e) ->
      "TryRecv " ^ id ^ " <- " ^ string_of_msg_spec rp.recv_msg_spec ^
      " { ok: " ^ string_of_expr ok_e.d ^ ", fail: " ^ string_of_expr fail_e.d ^ " }"
  | TrySend (sp, ok_e, fail_e) ->
      "TrySend " ^ string_of_msg_spec sp.send_msg_spec ^ "(" ^ string_of_expr sp.send_data.d ^ ")" ^
      " { ok: " ^ string_of_expr ok_e.d ^ ", fail: " ^ string_of_expr fail_e.d ^ " }"
  | Send sp ->
      (match sp.send_handshake with Instant -> "ISend " | Blocking -> "Send ")
      ^ string_of_msg_spec sp.send_msg_spec ^ "(" ^ string_of_expr sp.send_data.d ^ ")"
  | Recv rp ->
      (match rp.recv_handshake with Instant -> "IRecv " | Blocking -> "Recv ")
      ^ string_of_msg_spec rp.recv_msg_spec
  | Construct (spec, e_opt) ->
      let payload = match e_opt with Some e -> "(" ^ string_of_expr e.d ^ ")" | None -> "" in
      "Construct " ^ spec.variant_ty_name ^ "::" ^ spec.variant ^ payload
  | Record (name, fields, base_opt) ->
      let fields_str = String.concat ", " (List.map (fun (f, e) -> f ^ " = " ^ string_of_expr e.d) fields) in
      let base_str = match base_opt with Some b -> " | " ^ string_of_expr b.d | None -> "" in
      "Record " ^ name ^ " { " ^ fields_str ^ base_str ^ " }"
  | Index (arr, idx) ->
      "Index (" ^ string_of_expr arr.d ^ ", " ^ string_of_index idx ^ ")"
  | Indirect (e, field) ->
      "Indirect (" ^ string_of_expr e.d ^ ", " ^ field ^ ")"
  | Concat (es, is_flat) ->
      "Concat" ^ (if is_flat then "[flat]" else "") ^
      " {" ^ String.concat ", " (List.map (fun e -> string_of_expr e.d) es) ^ "}"
  | Cast (e, dt) ->
      "Cast (" ^ string_of_expr e.d ^ " as " ^ string_of_data_type dt ^ ")"
  | Ready msg_spec -> "Ready (" ^ string_of_msg_spec msg_spec ^ ")"
  | Probe msg_spec -> "Probe (" ^ string_of_msg_spec msg_spec ^ ")"
  | Read lv -> "Read (" ^ string_of_lvalue lv ^ ")"
  | SharedAssign (id, e) -> "SharedAssign (" ^ id ^ ", " ^ string_of_expr e.d ^ ")"
  | List es ->
      "List [" ^ String.concat "; " (List.map (fun e -> string_of_expr e.d) es) ^ "]"
  | Recursion (id, body) ->
      "Recursion " ^ id ^ " { " ^ string_of_expr body.d ^ " }"
  | Recursor id -> "Recursor " ^ id
  | Recurse -> "Recurse"
  | Match (e, arms) ->
      let arm_str (pat, body_opt) =
        string_of_expr pat.d ^ (match body_opt with Some b -> " -> " ^ string_of_expr b.d | None -> "")
      in
      "Match (" ^ string_of_expr e.d ^ ") { " ^ String.concat " | " (List.map arm_str arms) ^ " }"
  | Debug dbg ->
      (match dbg with
       | DebugPrint (fmt, args) ->
           "Debug:print(\"" ^ fmt ^ "\"" ^
           (if args = [] then "" else ", " ^ String.concat ", " (List.map (fun a -> string_of_expr a.d) args)) ^ ")"
       | DebugFinish -> "Debug:finish")
  | XOffer (arms, sel_opt) ->
      let arm_str (arm_ty, body) =
        string_of_offer_arm arm_ty ^ " -> " ^ string_of_expr body.d
      in
      let sel_str = match sel_opt with
        | Some (s, OrderRotate) -> " sel=" ^ s
        | Some (s, OrderTree) -> " tree sel=" ^ s
        | None -> "" in
      "XOffer" ^ sel_str ^ " { " ^ String.concat " | " (List.map arm_str arms) ^ " }"
  | Offer arms ->
      let arm_str (arm_ty, body) =
        string_of_offer_arm arm_ty ^ " -> " ^ string_of_expr body.d
      in
      "Offer { " ^ String.concat " | " (List.map arm_str arms) ^ " }"
  | OfferMatch (arms, cases) ->
      let arm_str (arm_ty, body) =
        string_of_offer_arm arm_ty ^ " -> " ^ string_of_expr body.d
      in
      let case_str (on, body) = string_of_match_on on ^ " -> " ^ string_of_expr body.d in
      "Offer { " ^ String.concat " | " (List.map arm_str arms) ^ " } Match { "
      ^ String.concat " | " (List.map case_str cases) ^ " }"

and string_of_match_on = function
  | Some [m] -> string_of_msg_spec m
  | Some ms -> "{" ^ String.concat ", " (List.map string_of_msg_spec ms) ^ "}"
  | None -> "*"

and string_of_offer_arm_type arm : string =
  match arm with
  | OfferSend sp ->
      (match sp.send_handshake with Instant -> "ISend " | Blocking -> "Send ")
      ^ string_of_msg_spec sp.send_msg_spec ^ "(" ^ string_of_expr sp.send_data.d ^ ")"
  | OfferRecv (id, rp) ->
      (match rp.recv_handshake with Instant -> "IRecv " | Blocking -> "Recv ")
      ^ id ^ " <- " ^ string_of_msg_spec rp.recv_msg_spec
  | OfferWildcard -> "_"

and string_of_offer_arm (arm : offer_arm_type) : string =
  match arm with
  | OfferAtom atom -> string_of_offer_arm_type atom
  | OfferConjunction arms -> "&(" ^ String.concat ", " (List.map string_of_offer_arm_type arms) ^ ")"

and string_of_lvalue (lv : lvalue) : string =
  match lv with
  | Reg id -> "Reg " ^ id
  | Indexed (lv, idx) -> "Indexed (" ^ string_of_lvalue lv ^ ", " ^ string_of_index idx ^ ")"
  | Indirected (lv, id) -> "Indirected (" ^ string_of_lvalue lv ^ ", " ^ id ^ ")"

and string_of_index (idx : index) : string =
  match idx with
  | Single e -> "Single (" ^ string_of_expr e.d ^ ")"
  | Range (e1, e2) -> "Range (" ^ string_of_expr e1.d ^ ", " ^ string_of_expr e2.d ^ ")"


and string_of_data_type (dtype : data_type) : string =
  match dtype with
  | `Logic -> "Logic"
  | `Array (d,n) ->
    let n' = match n with
      | ParamEnv.Concrete n -> string_of_int n
      | ParamEnv.Param s   -> "Param(" ^ s ^ ")"
      | ParamEnv.Expr _    -> "Expr(...)"
    in
    "Array[" ^ n' ^ "] (" ^ string_of_data_type d ^ ")"
  | `Variant (_, (id_opt_list)) ->
      "Variant (" ^ String.concat ", " (List.map (fun {d = (id, dt_opt, val_opt); _} ->
        match (dt_opt, val_opt) with
        | (Some dt, None) -> id ^ ": " ^ string_of_data_type dt
        | (None, Some lit) -> id ^ ": " ^ string_of_literal lit
        | (Some dt, Some lit) -> id ^ ": " ^ string_of_data_type dt ^ " = " ^ string_of_literal lit
        | (None, None) -> id) id_opt_list) ^ ")"
  | `Record fields ->
      "Record (" ^ String.concat ", " (List.map (fun {d = (field_name, field_type); _} ->
        field_name ^ ": " ^ string_of_data_type field_type) fields) ^ ")"
  | `Tuple dt_list ->
    (
      match dt_list with
      | [] -> "Void"
      | _ ->
        "Tuple (" ^ String.concat ", " (List.map string_of_data_type dt_list) ^ ")"
    )
  | `Opaque id -> "Opaque " ^ id
  | `Named (name, params) ->
      let params_str = String.concat ", " (List.map (function
        | IntParamValue v -> string_of_int v
        | TypeParamValue dt -> string_of_data_type dt) params) in
      "Named (" ^ name ^ ", [" ^ params_str ^ "])"
and string_of_data_type_opt (dtype_opt : data_type option) : string =
  match dtype_opt with
  | Some dtype -> string_of_data_type dtype
  | None -> "None"

and string_of_literal (lit : literal) : string =
  match lit with
  | Binary (n, bits) -> "Binary (" ^ string_of_int n ^ ", [" ^ String.concat ";" (List.map string_of_digit bits) ^ "])"
  | Decimal (n, digits) -> "Decimal (" ^ string_of_int n ^ ", [" ^ String.concat ";" (List.map string_of_digit digits) ^ "])"
  | Hexadecimal (n, hexits) -> "Hexadecimal (" ^ string_of_int n ^ ", [" ^ String.concat ";" (List.map string_of_digit hexits) ^ "])"
  | WithLength (n, v) -> "WithLength (" ^ string_of_int n ^ ", " ^ string_of_int v ^ ")"
  | NoLength v -> "NoLength " ^ string_of_int v

let sub_ep_index (ep: message_specifier) (index: int) (id : identifier) : message_specifier =
  let is_array = String.contains ep.endpoint '[' && String.contains ep.endpoint ']'in
  if is_array then
    (
    let base_name = String.sub ep.endpoint 0 (String.index ep.endpoint '[') in
    let rest = String.sub ep.endpoint (String.index ep.endpoint '[') (String.length ep.endpoint - String.index ep.endpoint '[') in
    let replaced_string = String.map (fun c ->
      if c = id.[0] then
        Char.chr (Char.code '0' + index)
      else
        c
    ) rest in
    { endpoint = base_name ^ replaced_string; msg = ep.msg }
    )
  else 
    ep

let rec substitute_expr_identifier (id: identifier) (value: expr_node) (idx : int) (expr: expr_node)  : expr_node =
  let subst = substitute_expr_identifier id value idx in
  let new_expr = match expr.d with
  | Identifier name when name = id ->
      value.d
  | Let (ids, dtype, e) ->
      if List.mem id ids then expr.d
      else Let (ids, dtype, substitute_expr_identifier id value idx e)
  | Record (name, fields, base) ->
      Record (
        name,
        List.map (fun (field_name, field_expr) ->
          (field_name, subst field_expr)
        ) fields,
        Option.map subst base
      )
  | Binop (op, e1, e2_opt) ->
      let new_e2_opt = match e2_opt with
        | `Single e2 -> `Single (substitute_expr_identifier id value idx e2)
        | `List exprs -> `List (List.map (fun e -> substitute_expr_identifier id value idx e) exprs)
        in
      Binop (op, substitute_expr_identifier id value idx e1, new_e2_opt)
  | Unop (op, e) ->
      Unop (op, subst e)
  | Tuple exprs ->
      Tuple (List.map (subst) exprs)
  | Join (e1, e2) ->
      Join (subst e1, subst e2)
  | Wait (e1, e2) ->
      Wait (subst e1, subst e2)
  | Index (arr, idx) ->
      let new_arr = subst arr in
      let new_idx = match idx with
        | Single e -> Single (subst e)
        | Range (e1, e2) -> Range (subst e1, subst e2)
      in
      Index (new_arr, new_idx)
  | Cast (e, dtype) ->
      Cast (subst e, dtype)
  | Concat (exprs, is_flat) ->
      Concat (List.map subst exprs, is_flat)
  | Assign (lv, e) ->
      let new_lv = substitute_lvalue id value idx lv in
      Assign (new_lv, subst e)
  | Send ({send_msg_spec; send_data; _} as sp) ->
      Send {
        sp with
        send_msg_spec = sub_ep_index send_msg_spec idx id;
        send_data = subst send_data;
      }
  | Debug (DebugPrint (msg, exprs)) ->
      Debug (DebugPrint (msg, List.map subst exprs))
  | Debug other_debug -> Debug other_debug
  | IfExpr (cond, then_expr, else_expr) ->
      IfExpr (
        subst cond,
        subst then_expr,
        subst else_expr
      )
  | Indirect (e, field) ->
      Indirect (subst e, field)
  | Call (name, args) ->
      Call (name, List.map subst args)
  | Match (e, arms) ->
    Match (
      subst e,
      List.map (fun (e_pat, e_body) -> (e_pat, Option.map subst e_body)) arms
    )
  | List ls -> List (List.map subst ls)
  | TryRecv (ident, recv_pack, e1, e2) ->
    TryRecv (
      ident,
      {recv_pack with recv_msg_spec = sub_ep_index recv_pack.recv_msg_spec idx id},
      subst e1,
      subst e2
    )
  | TrySend (send_pack, e1, e2) ->
    TrySend (
      {send_pack with send_msg_spec = sub_ep_index send_pack.send_msg_spec idx id; send_data = subst send_pack.send_data},
      subst e1,
      subst e2
    )
  | Construct (spec, e) ->
    Construct (
      spec,
      Option.map subst e
    )
  | SharedAssign (ident, e) ->
    SharedAssign (
      ident,
      subst e
    )
  | XOffer (arms, selector) ->
    XOffer (
      List.map (fun (arm_type, e_body) ->
        (arm_type, subst e_body)
      ) arms,
      selector
    )
  | Offer arms ->
    Offer (
      List.map (fun (arm_type, e_body) ->
        (arm_type, subst e_body)
      ) arms
    )
  | OfferMatch (arms, cases) ->
    OfferMatch (
      List.map (fun (arm_type, e_body) -> (arm_type, subst e_body)) arms,
      List.map (fun (on, e_body) -> (on, subst e_body)) cases
    )
  | Read lv ->
    Read (substitute_lvalue id value idx lv)
  | Recursion (rec_id, body) ->
    Recursion (rec_id, subst body)
  | Recurse | Literal _ | Cycle _ | Recursor _ 
  | Identifier _ | Ready _ | Probe _-> expr.d
  | Recv recv_pack ->
      let new_recv_pack = {recv_pack with recv_msg_spec = sub_ep_index recv_pack.recv_msg_spec idx id} in
      Recv new_recv_pack
  | Sync _ -> expr.d


  in
  { expr with d = new_expr }

and substitute_lvalue (id: identifier) (value: expr_node) (ind : int) (lv: lvalue) : lvalue =
    match (lv:lvalue) with
    | Reg name ->
        if name = id then
          match value.d with
          | Identifier new_id -> Reg new_id
          | _ -> failwith "Expected identifier"
        else
          lv
    | Indexed (lv', idx) ->
        let new_lv = substitute_lvalue id value ind lv' in
        let new_idx = match idx with
          | Single e -> Single (substitute_expr_identifier id value ind e)
          | Range (e1, e2) -> Range (substitute_expr_identifier id value ind e1, substitute_expr_identifier id value ind e2)
        in
        Indexed (new_lv, new_idx)
    | Indirected (lv', field) ->
        let new_lv = substitute_lvalue id value ind lv' in
        Indirected (new_lv, field)

let generate_expr (id, start, end_v, offset, body) =
  let rec generate_exprs (curr:int) acc =
    if curr > end_v then
      match List.rev acc with
      | [] -> Tuple []
      | [single] -> single.d
      | hd::tl ->
          List.fold_left
            (fun acc expr -> Join (expr, dummy_ast_node_of_data acc))
            hd.d
            tl
    else
      let bit_length = Utils.int_log2 (end_v + 1) in
      let substituted = substitute_expr_identifier id (dummy_ast_node_of_data(Literal(WithLength(bit_length, curr)))) curr body in
      generate_exprs (curr + offset) (substituted :: acc);

  in
  generate_exprs start []

  let generate_expr_seq (id, start, end_v, offset, body) =
    let rec generate_exprs_seq (curr:int) acc =
      if curr > end_v then
        match acc with
        | [] -> Tuple []
        | [single] -> single.d
        | hd::tl ->
            List.fold_left
              (fun acc expr -> Wait(expr, dummy_ast_node_of_data acc))
              hd.d
              tl
      else
        let bit_length = Utils.int_log2 (end_v + 1) in
        let substituted = substitute_expr_identifier id (dummy_ast_node_of_data(Literal(WithLength(bit_length, curr)))) curr body in
        generate_exprs_seq (curr + offset) (substituted :: acc);
    in
    generate_exprs_seq start []

(** An expression that does nothing and evaluates to a singleton unit value. *)
let unit_expr = Tuple []

let dummy_unit_node = dummy_ast_node_of_data unit_expr

(** A span that includes only the ending position of the given span. *)
let span_to_end span = {span with st = span.ed}

(** A span that includes only the starting position of the given span. *)
let span_to_start span = {span with ed = span.st}


let get_lvalue_reg_id (lv : lvalue) =
let rec get_lv lval =
  match lval with
  | Reg id -> id
  | Indexed (lval, _) -> get_lv lval
  | Indirected (lv,_) -> get_lv lv
in get_lv lv

(* let add_ep_to_atomic_action ep = function
  | AtomBMsg id -> AtomBMsg (Printf.sprintf "%s.%s" ep id)
  | AtomNBMsg id -> AtomNBMsg (Printf.sprintf "%s.%s" ep id)
   *)


(* let rec add_msg_ep_to_protocol ep = function
  | StyAtom (AtomicAct atm) ->
      StyAtom (AtomicAct (add_ep_to_atomic_action ep atm))
  | StySeq (p1, p2) -> *)

let rec string_of_protocol_for_graph p =
let rec aux p =
  match p with
  | StySeq (p1, p2) ->
      aux p1 ^ ";" ^ aux p2 
  | StySkip ->
      "∅"
  | StyEnd id ->
      "$" ^ id
  | StyChoice (p1, p2) ->
      "( " ^ aux p1 ^ "\n+\n" ^ aux p2 ^ " )"
  | StyOffer ps ->
      "( " ^ String.concat "\n&\n " (List.map aux2 ps) ^ " )"
  | StyXOffer ps ->
      "( " ^ String.concat " \n^\n " (List.map aux2 ps) ^ " )"
  | StyFairChoice (p1, p2) ->
      "( " ^ aux p1 ^ "\n+ᶠ\n" ^ aux p2 ^ " )"
  | StyFairXOffer ps ->
      "ᶠ( " ^ String.concat " \n^\n " (List.map aux2 ps) ^ " )"
  | StyOfferMatch (ps, cases) ->
      "( " ^ String.concat "\n&\n " (List.map aux2 ps) ^ " ).{ "
      ^ String.concat ",\n " (List.map (fun c -> string_of_match_on c.match_on ^ " : " ^ aux c.match_body) cases)
      ^ " }"
  | StyAtom act -> string_of_aa_with_gap act
  | StyFuture p_inner ->
      "F( " ^ aux p_inner ^ " )"
  | StyParallel (p1, p2) ->
      "( " ^ aux p1 ^ "\n||\n " ^ aux p2 ^ " )"
  | StyRec (id, p_body) ->
      "μ " ^ id ^ ".( " ^ aux p_body ^ " )"
  | StyVar id ->
      id
  | StyLet (id, p_def, p_body) ->
      "let " ^ id ^ " = " ^ aux p_def ^ " in " ^ aux p_body
  | StyForall (op,id,qty,body,_ex) ->
    let ex = string_of_quant_mem _ex in
    let op_str = match op with
      | QuantSum -> "∑" | QuantProduct -> "∏"
      | QuantOffer -> "∧" | QuantXOffer -> "⊕"
    in
      "∀_"^op_str^" ("^id^ " ∈ "^(string_of_quantifier_type qty)^ex^") { " ^ string_of_protocol_for_graph body ^ " }"
and string_of_quantifier_type ty = 
  match ty with
  | QuantRange (st,ed) ->
      "["^(string_of_int st)^","^(string_of_int ed)^"]"
and string_of_quant_mem mem = 
  match mem with
  | Some mem ->
    (
    match mem with
    | QuantSingleInt v ->
      "¬"^(string_of_int v)
    | QuantIntList lst ->
      "¬"^"{"^(String.concat "," (List.map string_of_int lst))^"}"
    )
  | None -> ""
and string_of_atomic_action atomic_action =
  match atomic_action with
  | AtomBMsg id -> string_of_msg_spec id
  | AtomNBMsg id -> "#" ^ string_of_msg_spec id
and string_of_aa_with_gap = function
  | AtomicAct act -> string_of_atomic_action act
  | AtomDelay n -> Printf.sprintf "#<%d>" n
  | AtomTerminal sty -> "( end of " ^ string_of_protocol_for_graph sty ^ " )"
  | AtomConjunction act_list -> "( " ^ String.concat " ∧ " (List.map string_of_atomic_action act_list) ^ " )" 
and aux2 p =
  match p with
  | {trigger; continuation} ->
    match continuation with
    | None -> string_of_aa_with_gap trigger
    | Some p_continuation -> string_of_aa_with_gap trigger ^ " : " ^ aux p_continuation
in aux p



let rec string_of_protocol p =
let rec aux p =
  match p with
  | StySeq (p1, p2) ->
      aux p1 ^ ";" ^ aux p2 
  | StySkip ->
      "∅"
  | StyEnd id ->
      "$" ^ id
  | StyChoice (p1, p2) ->
      "(" ^ aux p1 ^ "+" ^ aux p2 ^ ")"
  | StyOffer ps ->
      "(" ^ String.concat "∧" (List.map aux2 ps) ^ ")"
  | StyXOffer ps ->
        "(" ^ String.concat " ⊕ "   (List.map aux2 ps) ^ ")"
  | StyFairChoice (p1, p2) ->
      "(" ^ aux p1 ^ "+ᶠ" ^ aux p2 ^ ")"
  | StyFairXOffer ps ->
      "(" ^ String.concat " ⊕ᶠ " (List.map aux2 ps) ^ ")"
  | StyOfferMatch (ps, cases) ->
      "(" ^ String.concat "∧" (List.map aux2 ps) ^ ").{"
      ^ String.concat ", " (List.map (fun c -> string_of_match_on c.match_on ^ " : " ^ aux c.match_body) cases)
      ^ "}"
  | StyAtom act -> string_of_aa_with_gap act
  | StyFuture p_inner ->
      "F(" ^ aux p_inner ^ ")"
  | StyParallel (p1, p2) ->
      "(" ^ aux p1 ^ " ||  " ^ aux p2 ^ ")"
  | StyRec (id, p_body) ->
      "μ " ^ id ^ ".( " ^ aux p_body ^ ")"
  | StyVar id ->
      id
  | StyLet (id, p_def, p_body) ->
      "let " ^ id ^ " = " ^ aux p_def ^ " in " ^ aux p_body
  | StyForall (op,id,qty,body,_ex) ->
    let ex = string_of_quant_mem _ex in
    let op_str = match op with
      | QuantSum -> "∑" | QuantProduct -> "∏"
      | QuantOffer -> "∧" | QuantXOffer -> "⊕"
    in
      "∀_"^op_str^" ("^id^ " ∈ "^(string_of_quantifier_type qty)^ex^") { " ^ string_of_protocol body ^ " }"

and string_of_quantifier_type ty = 
  match ty with
  | QuantRange (st,ed) ->
      "["^(string_of_int st)^","^(string_of_int ed)^"]"

and string_of_quant_mem mem = 
  match mem with
  | Some mem ->
    (
    match mem with
    | QuantSingleInt v ->
    " ̸ "^(string_of_int v)
    | QuantIntList lst ->
      " ̸ "^"{"^(String.concat "," (List.map string_of_int lst))^"}"
    ) 
  | None -> ""
  
  





and string_of_atomic_action atomic_action =
  match atomic_action with
  | AtomBMsg id -> string_of_msg_spec id
  | AtomNBMsg id -> "#" ^ string_of_msg_spec id
and string_of_aa_with_gap = function
  | AtomicAct act -> string_of_atomic_action act
  | AtomDelay n when n > 0 -> Printf.sprintf "#<%d>" n
  | AtomTerminal sty -> "( end of " ^ string_of_protocol sty ^ " )"
  | AtomConjunction acts -> "( " ^ String.concat " ∧ " (List.map string_of_atomic_action acts) ^ " )"
  | _ -> "*"
and aux2 p =
  match p with
  | {trigger; continuation} ->
    match continuation with
    | None -> string_of_aa_with_gap trigger
    | Some p_continuation -> string_of_aa_with_gap trigger ^ " : " ^ aux p_continuation
in aux p

let  string_of_atomic_action act =
  match act with
  | AtomBMsg id -> string_of_msg_spec id
  | AtomNBMsg id -> "#" ^ string_of_msg_spec id
  
let string_of_atomic_action_with_gap = function
  | AtomicAct act -> string_of_atomic_action act
  | AtomDelay n when n > 0 -> Printf.sprintf "#<%d>" n
  | AtomTerminal sty -> "( end of " ^ string_of_protocol sty ^ " )"
  | AtomConjunction acts -> "( " ^ String.concat " ∧ " (List.map string_of_atomic_action acts) ^ " )"
  | _ -> "*"




let preprocess_ep_spawn_args (args : args_spawn list) : identifier list =
  let rec generate_ep_indices base_string_list idx =
    match idx with
    | IndexSingle i ->
      List.map(
        fun base_str -> base_str ^ (Printf.sprintf "[%d]" i)
      )base_string_list
    | IndexRange (start, sz) ->
        let end_v = start + sz - 1 in
        let rec generate_range curr =
          if curr > end_v then
            []
          else  
            let new_base_strings = List.map(
              fun base_str -> base_str ^ (Printf.sprintf "[%d]" curr)
            ) base_string_list in
            new_base_strings @ (generate_range (curr + 1))
        in
        generate_range start
    | IndexMultiDimSingle (i, rest) ->
        let new_base_strings = List.map(
          fun base_str -> base_str ^ (Printf.sprintf "[%d]" i)
        ) base_string_list in
        generate_ep_indices new_base_strings rest
    | IndexMultiDimRange (start, size, rest) ->
        List.concat_map (fun curr ->
          let new_base_strings = List.map(
            fun base_str -> base_str ^ (Printf.sprintf "[%d]" curr)
          ) base_string_list in
          generate_ep_indices new_base_strings rest
        ) (List.init size (fun i -> start + i))
  in

  List.concat_map
    (function
      | SingleEp name -> [name]
      | IndexedEp (name, idx) ->
        generate_ep_indices [name] idx
    ) 
    args

let rec calculate_array_index_concrete_size (dimm : array_index_concrete) : int =
  match dimm with
  | IndexSingle _ -> 1
  | IndexRange (_, sz) -> sz
  | IndexMultiDimSingle (_, rest) ->
      calculate_array_index_concrete_size rest
  | IndexMultiDimRange (_, size, rest) ->
      size * (calculate_array_index_concrete_size rest)

(* Offer matches: a case applies when exactly its arms were taken. Arms are
   identified by their message groups, which must be disjoint. *)
let same_msg_set (a : message_specifier list) (b : message_specifier list) =
  List.sort_uniq compare a = List.sort_uniq compare b

(** Every non-empty combination of arms, as the messages of the arms taken. *)
let offer_arm_combinations (groups : message_specifier list list) =
  let rec subsets = function
    | [] -> [ [] ]
    | g :: rest -> List.concat_map (fun s -> [ s; g @ s ]) (subsets rest)
  in
  List.filter (fun s -> s <> []) (subsets groups)

(** The case for exactly [taken], or the default case. *)
let offer_match_lookup (cases : (message_specifier list option * 'a) list) taken =
  match List.find_opt (fun (on, _) ->
      match on with Some ms -> same_msg_set ms taken | None -> false) cases with
  | Some (_, x) -> Some x
  | None -> List.find_map (fun (on, x) -> if on = None then Some x else None) cases

(** An error message if the cases are not one per combination of arms. *)
let check_offer_match_cases (groups : message_specifier list list)
    (cases : (message_specifier list option * 'a) list) =
  let combinations = offer_arm_combinations groups in
  let keys = List.filter_map fst cases in
  let defaults = List.length (List.filter (fun (on, _) -> on = None) cases) in
  let missing = List.filter (fun c -> offer_match_lookup cases c = None) combinations in
  let names ms = "{" ^ String.concat ", " (List.map string_of_msg_spec ms) ^ "}" in
  match List.find_opt (fun k -> not (List.exists (same_msg_set k) combinations)) keys with
  | Some k -> Some ("Offer match case " ^ names k ^ " is not a combination of the offer's arms")
  | None ->
    if List.length (List.sort_uniq compare (List.map (List.sort_uniq compare) keys)) <> List.length keys
    then Some "Offer match has two cases for the same arms"
    else if defaults > 1 then Some "Offer match has more than one default case"
    else match missing with
      | m :: _ -> Some ("Offer match has no case for arms " ^ names m)
      | [] -> None

(** An error message unless every arm of an offer match is a message whose
    continuation starts with a delay. *)
let check_offer_match_arms (offerings : offering_session_type list) =
  let rec starts_with_delay = function
    | StySkip | StyAtom (AtomDelay _) -> true
    | StySeq (a, _) -> starts_with_delay a
    | _ -> false
  in
  List.find_map (fun (off : offering_session_type) ->
    match off.trigger, off.continuation with
    | AtomTerminal _, _ -> Some "Offer match arms must be messages"
    | (AtomicAct _ | AtomConjunction _), Some cont when not (starts_with_delay cont) ->
        Some "An offer match arm must wait a cycle before continuing; put same-cycle actions in the cases"
    | _ -> None) offerings
