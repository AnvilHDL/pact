%token EOF
%token LEFT_BRACE           (* { *)
%token RIGHT_BRACE          (* } *)
%token LEFT_BRACKET         (* [ *)
%token RIGHT_BRACKET        (* ] *)
%token LEFT_PAREN           (* ( *)
%token RIGHT_PAREN          (* ) *)
%token COMMA                (* , *)
%token SEMICOLON            (* ; *)
%token COLON                (* : *)
%token DOUBLE_COLON         (* :: *)
%token KEYWORD_FUNCTION    (* func *)
%token KEYWORD_PROTOCOL    (* protocol *)
%token KEYWORD_CALL                (* call *)
%token SHARP                (* # *)
%token EQUAL                (* = *)
%token COLON_EQ             (* := *)
%token LEFT_ABRACK          (* < *)
%token RIGHT_ABRACK         (* > *)
%token LEFT_ABRACK_EQ       (* <= *)
%token RIGHT_ABRACK_EQ      (* >= *)
%token DOUBLE_LEFT_ABRACK   (* << *)
%token SHL                  (* shl *)
%token SHR                  (* shr *)
%token KEYWORD_CONST        (* const *)
%token KEYWORD_XOFFER       (* xoffer *)
%token KEYWORD_READY        (* ready *)
%token KEYWORD_VOID         (* void *)
%token KEYWORD_PROBE        (* probe *)
%token DOUBLE_EQ            (* == *)
%token EQ_GT                (* => *)
%token DOUBLE_GT            (* >> *)
%token EXCL_EQ              (* != *)
%token ASTERISK             (* * *)
%token PLUS                 (* + *)
%token MINUS                (* - *)
%token DOUBLE_MINUS         (* -- *)
%token XOR                  (* ^ *)
%token AND                  (* & *)
%token DOUBLE_AND           (* && *)
%token OR                   (* | *)
%token DOUBLE_OR            (* || *)
%token AT                   (* @ *)
%token TILDE                (* ~ *)
%token PERIOD               (* . *)
%token IN_SYMBOL            (* ∈ *)
%token SUM_SYMBOL           (* ∑ *)
%token PROD_SYMBOL          (* Π *)
%token XOR_SYMBOL           (* ⨁ *)
%token AND_SYMBOL           (* ⋀ *)
%token REC_SYMBOL           (* μ *)
%token KEYWORD_LOOP         (* loop *)
%token KEYWORD_PROC         (* proc *)
%token KEYWORD_INTERFACE      (* Interface *)
%token DOLLAR               (* $ *)       
%token KEYWORD_CHAN         (* chan *)
%token KEYWORD_REC         (* rec *)
%token KEYWORD_LEFT         (* left *)
%token KEYWORD_RIGHT        (* right *)
%token KEYWORD_PUT          (* put *)
%token KEYWORD_FORALL       (* forall *)
%token FORALL_SYMBOL     (* ∀ *)
%token NOT_SYMBOL     (* ̸ *)
%token KEYWORD_EXCEPT       (* not  *)
%token KEYWORD_LOGIC        (* logic *)
%token KEYWORD_POOL        (* pool *)
%token KEYWORD_GENERATE     (* generate *)
%token KEYWORD_GENERATE_SEQ     (* generate *)
%token KEYWORD_FLAT       (* flat *)
%token KEYWORD_IF           (* if *)
%token KEYWORD_ELSE         (* else *)
%token KEYWORD_LET          (* let *)
%token KEYWORD_SEND         (* send *)
%token KEYWORD_RECV         (* recv *)
%token KEYWORD_IN          (* in *)
%token KEYWORD_ETERNAL      (* eternal *)
%token KEYWORD_TYPE         (* type *)
%token KEYWORD_SET          (* set *)
%token KEYWORD_MATCH        (* match *)
%token KEYWORD_SYNC         (* sync *)
%token KEYWORD_DYN          (* dyn *)
%token KEYWORD_CYCLE        (* cycle *)
%token KEYWORD_REG          (* reg *)
%token KEYWORD_SPAWN        (* spawn *)
%token KEYWORD_DPRINT       (* dprint *)
%token KEYWORD_DFINISH      (* dfinish *)
%token KEYWORD_IMPORT       (* import *)
%token KEYWORD_EXTERN       (* extern *)
%token KEYWORD_INT          (* int *)
%token KEYWORD_RECURSIVE    (* recursive *)
%token KEYWORD_RECURSE      (* recurse *)
%token KEYWORD_STRUCT       (* struct *)
%token KEYWORD_ENUM         (* enum *)
%token KEYWORD_WITH         (* with *)
%token KEYWORD_F         (* F *)
%token KEYWORD_OFFER        (* offer *)
%token KEYWORD_TRY          (* try *)
%token <int>INT             (* int literal *)
%token <string>IDENT        (* identifier *)
%token <string>BIT_LITERAL  (* bit literal *)
%token <string>DEC_LITERAL  (* decimal literal *)
%token <string>HEX_LITERAL  (* hexadecimal literal *)
%token <string>STR_LITERAL
%token KEYWORD_SHARED       (* shared *)
%token KEYWORD_ASSIGNED     (* assigned *)
%token KEYWORD_BY           (* by *)
%nonassoc PREC_NAMED_TYPE
%right LEFT_ABRACK RIGHT_ABRACK LEFT_ABRACK_EQ RIGHT_ABRACK_EQ
%right DOUBLE_GT SEMICOLON
%right KEYWORD_LET KEYWORD_SET KEYWORD_PUT
%left DOUBLE_AND DOUBLE_OR
%left EXCL_EQ DOUBLE_EQ
%left XOR AND OR PLUS MINUS
%left SHL SHR
%left PERIOD
%left ASTERISK
%left LEFT_BRACKET
%nonassoc TILDE UMINUS UAND UOR KEYWORD_IN
%nonassoc KEYWORD_F
%start <Lang.compilation_unit> cunit
%%

%public %inline node(X):
  x=X { Lang.ast_node_of_data $startpos $endpos x }

cunit:
| EOF
  { Lang.cunit_empty }
| p = proc_def; c = cunit
  { Lang.cunit_add_proc c p }
| macro  = macro_def;c = cunit
  { Lang.cunit_add_macro_def c macro }
| func_def = function_def; c = cunit
  { Lang.cunit_add_func_def c func_def }
| ty = type_def; c = cunit
  { Lang.cunit_add_type_def c ty }
| sess = node(session_def); c = cunit
  { Lang.cunit_add_session_def c sess }
| pools = node(interface_pool_def); c = cunit
  { Lang.cunit_add_interface_pool_def c pools }
| cc = channel_class_def; c = cunit
  { Lang.cunit_add_channel_class c cc }
| im = import_directive; c = cunit
  { Lang.cunit_add_import c im }
;

import_directive:
| KEYWORD_IMPORT; file_name = STR_LITERAL
  {
    let open Lang in {file_name; is_extern = false}
  }
| KEYWORD_EXTERN; KEYWORD_IMPORT; file_name = STR_LITERAL
  {
    let open Lang in {file_name; is_extern = true}
  }
;


proc_def:
| KEYWORD_PROC; ident = IDENT;
  LEFT_PAREN; RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = [];
      args = [];
      params = [];
      body = let open Lang in Native body
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT;
  LEFT_PAREN; args = proc_def_arg_list_nonempty; RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = [];
      args = args;
      params = [];
      body = let open Lang in Native body
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT; LEFT_ABRACK; params = separated_list(COMMA, param_def); RIGHT_ABRACK;
  LEFT_PAREN; RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = [];
      args = [];
      params = params;
      body = let open Lang in Native body
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT; LEFT_ABRACK; params = separated_list(COMMA, param_def); RIGHT_ABRACK;
  LEFT_PAREN; args = proc_def_arg_list_nonempty; RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = [];
      args = args;
      params = params;
      body = let open Lang in Native body
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT;
  LEFT_PAREN; args = proc_def_arg_list_nonempty; RIGHT_PAREN;
  KEYWORD_EXTERN; LEFT_PAREN; mod_name = STR_LITERAL; RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body_extern; RIGHT_BRACE
  {
    {
      name = ident;
      interface = [];
      args = args;
      params = [];
      body = let open Lang in Extern (mod_name, body)
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT; LEFT_ABRACK; params = separated_list(COMMA, param_def); RIGHT_ABRACK;
  LEFT_PAREN; intf = separated_list(COMMA, node(IDENT)); RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = intf;
      args = [];
      params = params;
      body = let open Lang in Native body
    } : Lang.proc_def
  }
| KEYWORD_PROC; ident = IDENT;
  LEFT_PAREN; intf = separated_list(COMMA, node(IDENT)); RIGHT_PAREN;
  LEFT_BRACE; body = proc_def_body; RIGHT_BRACE
  {
    {
      name = ident;
      interface = intf;
      args = [];
      params = [];
      body = let open Lang in Native body
    } : Lang.proc_def
  }

proc_def_body:
|
  {
    let open Lang in {
      channels = [];
      pool_insts = [];
      spawns = [];
      regs = [];
      threads = [];
      shared_vars = [];
    }
  }
| KEYWORD_LOOP; reset_by = message_specifier?; LEFT_BRACE; thread_prog = node(expr); RIGHT_BRACE; body=proc_def_body //For thread definitions
  {
    let open Lang in
    let thread_prog = {thread_prog with d = Wait (thread_prog, dummy_ast_node_of_data Recurse)} in
    {body with threads = (thread_prog, reset_by)::(body.threads) }
  }
| KEYWORD_RECURSIVE; LEFT_BRACE; thread_prog = node(expr); RIGHT_BRACE; body = proc_def_body
  {
    let open Lang in
    { body with threads = (thread_prog, None)::(body.threads) }
  }
| KEYWORD_CHAN; chan_def = node(channel_def); SEMICOLON; body = proc_def_body // For Channel Invocation and interface aquisition
  {
    let open Lang in {body with channels = chan_def::(body.channels)}
  }
| KEYWORD_POOL; p = node(pool_spawn); SEMICOLON; body = proc_def_body
  {
    let open Lang in {body with pool_insts = p::(body.pool_insts)}
  }
| KEYWORD_REG; reg_def = node(reg_def); SEMICOLON; body = proc_def_body // For reg definition
  {
    let open Lang in {body with regs = reg_def::(body.regs)}
  }
| KEYWORD_SPAWN; spawn_def = node(spawn); SEMICOLON; body = proc_def_body // For instantiating processes
  {
    let open Lang in {body with spawns = spawn_def::(body.spawns)}
  }
| shared_var = node(shared_var_def); SEMICOLON; body = proc_def_body
  {
    let open Lang in {body with shared_vars = shared_var :: body.shared_vars}
  }
;


pool_spawn:
| pid = IDENT; COLON; pty = IDENT
  {
    {
      p_id = pid;
      p_ty = pty
    } : Lang.pool_inst
  }
// interface_spawn:
//   id = IDENT; LEFT_ABRACK; params = separated_list(COMMA, IDENT); RIGHT_ABRACK
//   { {intfc_id = id; intfc_args =  params} }

proc_def_body_extern:
| { let open Lang in {named_ports = []; msg_ports = []} }
| name = IDENT; LEFT_PAREN; s = STR_LITERAL; RIGHT_PAREN; SEMICOLON; body = proc_def_body_extern
  {
    let open Lang in {body with named_ports = (name, s)::body.named_ports}
  }
| msg = message_specifier; LEFT_PAREN; s0 = STR_LITERAL?; COLON;
  s1 = STR_LITERAL?; COLON; s2 = STR_LITERAL?; RIGHT_PAREN; SEMICOLON; body = proc_def_body_extern
  {
    let open Lang in {body with msg_ports = (msg, s0, s1, s2)::body.msg_ports}
  }
;

param_def:
| name = IDENT; COLON; KEYWORD_INT
  {
    let open Lang in {param_name = name; param_ty = IntParam}
  }
| name = IDENT; COLON; KEYWORD_TYPE
  {
    let open Lang in {param_name = name; param_ty = TypeParam}
  }
;

param_list:
  LEFT_ABRACK; params = separated_list(COMMA, param_def); RIGHT_ABRACK;
  { params }
;

// For defining struct for messages and message types
type_def:
| KEYWORD_TYPE; name = IDENT; params = param_list?;
  EQUAL; dtype = data_type; SEMICOLON
  {
    { name = name; body = dtype; params = Option.value ~default:[] params } : Lang.type_def
  }
| KEYWORD_ENUM; name = IDENT; params = param_list?;
  LEFT_BRACE; variants = separated_nonempty_list(COMMA, variant_def); RIGHT_BRACE
  {
    { name = name; body = `Variant (None,variants); params = Option.value ~default:[] params } : Lang.type_def
  }
| KEYWORD_ENUM; name = IDENT; dtype = data_type; params = param_list?;
  LEFT_BRACE; variants = separated_nonempty_list(COMMA, variant_def); RIGHT_BRACE
  {
    { name = name; body = `Variant (Some dtype, variants); params = Option.value ~default:[] params } : Lang.type_def
  }
| KEYWORD_STRUCT; name = IDENT; params = param_list?;
  LEFT_BRACE; fields = separated_nonempty_list(COMMA, field_def); RIGHT_BRACE
  {
    { name = name; body = `Record (List.rev fields); params = Option.value ~default:[] params } : Lang.type_def
  }
;


interface_pool_def:
| KEYWORD_POOL; id = IDENT; LEFT_BRACE; channel_defs = separated_list(COMMA, node(channel_def)); SEMICOLON; interface_mem = separated_list(COMMA, node(interface_members_def)); RIGHT_BRACE
  {
    {
    pool_id = id;
      pool_channels = channel_defs;
      interface_members = interface_mem
    } : Lang.interface_pool_def
  }
;

interface_members_def:
| id1 = IDENT; COLON; intf = local_session_type
  {
    {
      inf_mem_id = id1;
      interface_class_id = None;
      interface_def = Some intf
    } : Lang.interface_mem_def
  }
| id1 = IDENT; COLON; intf = IDENT; LEFT_PAREN; params = separated_list(COMMA,IDENT); RIGHT_PAREN
  {
    {
      inf_mem_id = id1;
      interface_class_id = Some {id = intf; params = params};
      interface_def = None
    } : Lang.interface_mem_def
  } 
;

session_def:
| KEYWORD_INTERFACE; name = IDENT; LEFT_PAREN; params = proc_def_arg_list; RIGHT_PAREN; EQUAL ; body = node(local_session_type);
  {
    { name = name; body = body; params = params; data_params = [] } : Lang.session_def
  }
| KEYWORD_INTERFACE; data_params = param_list; name = IDENT; LEFT_PAREN; params = proc_def_arg_list; RIGHT_PAREN; EQUAL ; body = node(local_session_type);
  {
    { name = name; body = body; params = params; data_params = data_params } : Lang.session_def
  }
;
  
local_session_type:
| LEFT_PAREN; RIGHT_PAREN
  { Lang.StyTrue }
| SHARP; n = INT
  { Lang.StyAtom (Lang.AtomDelay n) }
| KEYWORD_LET; id = IDENT; EQUAL; ex = local_session_type; KEYWORD_IN; body = local_session_type
  { Lang.StyLet (id, ex, body) }
| rec_sym; id = IDENT; PERIOD; body = local_session_type
  { Lang.StyRec (id, body) }
| id = IDENT
  { Lang.StyVar id }
| act = atomic_action
  { Lang.StyAtom (Lang.AtomicAct act) }
| act1 = local_session_type ;SEMICOLON; act2 = local_session_type
  { Lang.StySeq (act1, act2) }
| act1 = local_session_type ;PLUS; act2 = local_session_type
  { Lang.StyChoice (act1, act2) }
| and_sym; LEFT_PAREN offering_list = separated_list(COMMA, offering_arm); RIGHT_PAREN
  { Lang.StyOffer offering_list }
| xor_sym; LEFT_PAREN offering_list = separated_list(COMMA, offering_arm); RIGHT_PAREN
  { Lang.StyXOffer offering_list }
| act1 = local_session_type; DOUBLE_OR; act2 = local_session_type
  { Lang.StyParallel (act1, act2) }
| LEFT_PAREN; sty = local_session_type; RIGHT_PAREN
  { sty }
| KEYWORD_F; sty = local_session_type %prec KEYWORD_F
  { Lang.StyFuture sty }
| sum_symbol;LEFT_PAREN; choice_list = separated_list(COMMA, local_session_type); RIGHT_PAREN
  { let rec unfold_sum lst =
    match lst with
    | [] -> Lang.StyTrue
    | x::xs -> Lang.StyChoice (x, unfold_sum xs)
  in
  unfold_sum choice_list }
| prod_sym; LEFT_PAREN; par_list = separated_list(COMMA, local_session_type); RIGHT_PAREN
  { let rec unfold_prod lst =
    match lst with
    | [] -> Lang.StyTrue
    | x::xs -> Lang.StyParallel (x, unfold_prod xs)
  in
  unfold_prod par_list }
| forall; LEFT_PAREN; id = IDENT; in_sym; quant_type = quantifier_type;exc=excluded_member?; RIGHT_PAREN; op = op_quantifier; LEFT_BRACE; body = local_session_type; RIGHT_BRACE
  { Lang.StyForall (op, id, quant_type, body, exc)}
| forall; LEFT_PAREN; id = IDENT; in_sym; quant_type = quantifier_type; exc=excluded_member?; RIGHT_PAREN; and_sym ; LEFT_BRACE; body = separated_list(COMMA, offering_arm); RIGHT_BRACE
  { Lang.StyForall (Lang.QuantOffer, id, quant_type, Lang.StyOffer body, exc) }
| forall; LEFT_PAREN; id = IDENT; in_sym; quant_type = quantifier_type; exc=excluded_member?; RIGHT_PAREN; xor_sym; LEFT_BRACE; body = separated_list(COMMA, offering_arm); RIGHT_BRACE
  { Lang.StyForall (Lang.QuantXOffer, id, quant_type, Lang.StyXOffer body, exc) }

op_quantifier:
| sum_symbol
  { Lang.QuantSum }
| prod_sym
  { Lang.QuantProduct }

forall:
| KEYWORD_FORALL
  { () }
| FORALL_SYMBOL
  { () }

in_sym:
| IN_SYMBOL
  { () }
| COLON
  { () }

xor_sym:
| XOR
  { () }
| XOR_SYMBOL
  { () }

rec_sym:
| KEYWORD_REC
  { () }
| REC_SYMBOL
  { () }

and_sym:
| AND
  { () }
| AND_SYMBOL
  { () }

sum_symbol:
| PLUS
  { () }
| SUM_SYMBOL
  { () }

prod_sym:
| DOUBLE_OR
  { () }
| PROD_SYMBOL
  { () }


excluded_member:
| KEYWORD_EXCEPT; exc = excluded_member_ty
  { exc }
| NOT_SYMBOL; exc = excluded_member_ty
  { exc }

// To Do : Add quantification over channel type (for input endpoints)
quantifier_type:
| LEFT_BRACKET; start = INT ;PERIOD;PERIOD; ed=INT;RIGHT_BRACKET
  { Lang.QuantRange (start,ed) }

excluded_member_ty:
| single = INT
  { Lang.QuantSingleInt single }
| LEFT_PAREN;rng = separated_list(COMMA,INT); RIGHT_PAREN  
  { Lang.QuantIntList rng }

offering_arm: 
| trig  = atomic_action; COLON; cont = local_session_type
  { { Lang.trigger = Lang.AtomicAct trig; Lang.continuation = Some cont } : Lang.offering_session_type }
| trig = atomic_action;
  { { Lang.trigger = Lang.AtomicAct trig; Lang.continuation = None } : Lang.offering_session_type }
| ASTERISK; COLON; cont = local_session_type
  { { Lang.trigger = Lang.AtomDelay 0; Lang.continuation = Some cont } : Lang.offering_session_type }
| ASTERISK
  { { Lang.trigger = Lang.AtomDelay 0; Lang.continuation = None } : Lang.offering_session_type }
| DOLLAR; x= local_session_type; COLON; cont = local_session_type
  { { Lang.trigger = Lang.AtomTerminal x; Lang.continuation = Some cont } : Lang.offering_session_type }
| DOLLAR; x= local_session_type
  { { Lang.trigger = Lang.AtomTerminal x; Lang.continuation = None } : Lang.offering_session_type }
| LEFT_BRACE; trig_list = separated_nonempty_list(COMMA, atomic_action); RIGHT_BRACE; COLON; cont = local_session_type
  { { Lang.trigger = Lang.AtomConjunction trig_list; Lang.continuation = Some cont } : Lang.offering_session_type }
| LEFT_BRACE; trig_list = separated_nonempty_list(COMMA, atomic_action); RIGHT_BRACE
  { { Lang.trigger = Lang.AtomConjunction trig_list; Lang.continuation = None } : Lang.offering_session_type }
atomic_action:
| id = message_specifier
  { Lang.AtomBMsg id }
| SHARP;id = message_specifier
  { Lang.AtomNBMsg id }



variant_def:
| name = IDENT; dtype_opt = variant_type_spec?
  { (name, dtype_opt, None) }

| name = IDENT; EQUAL; lit = literal_val
  { (name, None, Some lit) } 
;

variant_type_spec:
| LEFT_PAREN; dtype = data_type; RIGHT_PAREN
  { dtype }
| LEFT_PAREN; dtype = data_type; COMMA; more_dtypes = separated_nonempty_list(COMMA, data_type); RIGHT_PAREN
  { `Tuple (dtype::more_dtypes) }
;

literal_val:
| literal_str = BIT_LITERAL
  { ParserHelper.bit_literal_of_string literal_str }
| literal_str = DEC_LITERAL
  { ParserHelper.dec_literal_of_string literal_str }
| literal_str = HEX_LITERAL
  { ParserHelper.hex_literal_of_string literal_str }
| literal_val = INT
  { Lang.NoLength literal_val}

field_def:
| name = IDENT; COLON; dtype = data_type
  { (name, dtype) }
;

// For channel declaration for each pair of process
channel_class_def:
| KEYWORD_CHAN; ident = IDENT; LEFT_BRACE; messages = separated_list(COMMA, message_def); prog_cont=progress_contract?;RIGHT_BRACE
  {
    {
      name = ident;
      messages = messages;
      params = [];
  span = {st = $startpos; ed = $endpos};
  local_sty = match prog_cont with Some(p) -> Some p | None -> None
    } : Lang.channel_class_def
  }
| KEYWORD_CHAN; ident = IDENT; LEFT_ABRACK; params = separated_list(COMMA, param_def); RIGHT_ABRACK;
  LEFT_BRACE; messages = separated_list(COMMA, message_def);prog_cont=progress_contract?; RIGHT_BRACE
  {
    {
      name = ident;
      messages = messages;
      params = params;
  span = {st = $startpos; ed = $endpos};
  local_sty = match prog_cont with Some(p) -> Some p | None -> None
    } : Lang.channel_class_def
  }
;
progress_contract:
| KEYWORD_PROTOCOL; DOUBLE_COLON; prog_type = node(local_session_type);
  { prog_type }


//For passing the list of channels that are nessacary to communicate with the instantiation of the process
proc_def_arg_list:
|  l = separated_list(COMMA, node(proc_def_arg))
  { l }
;

proc_def_arg_list_nonempty:
  l = separated_nonempty_list(COMMA, node(proc_def_arg))
  { l }
;
// To Do: Can be renamed to inherited channel or something
proc_def_arg:
| ident = IDENT; COLON; chan_dir = channel_direction; chan_class = channel_class_concrete
  {
    {
      name = ident;
      channel_class = fst chan_class;
      channel_params = snd chan_class;
      dir = chan_dir;
      foreign = false;
      opp = None;
      num_instances = None;
    } : Lang.endpoint_def
  }
| ident = IDENT; n = array_dimm; COLON; chan_dir = channel_direction; chan_class = channel_class_concrete
  {
    {
      name = ident;
      channel_class = fst chan_class;
      channel_params = snd chan_class;
      dir = chan_dir;
      foreign = false;
      opp = None;
      num_instances = Some n;
    } : Lang.endpoint_def
  }

array_dimm:
| LEFT_BRACKET; n = int_maybe_param; RIGHT_BRACKET
  { Lang.OneDim n }
| LEFT_BRACKET; n = int_maybe_param; RIGHT_BRACKET; rst = array_dimm;
  {Lang.MultiDim (n, rst) }



// Specifies the dirn of comm (inp or out)
channel_direction:
| KEYWORD_LEFT
  { Lang.Left }
| KEYWORD_RIGHT
  { Lang.Right }
;
// channels are instantantiated with endpoint aquisition by native channel inside the proc
channel_def:
| left_endpoint = IDENT; DOUBLE_MINUS;
  right_endpoint = IDENT; COLON;
  chan_class = channel_class_concrete
  {
    {
      channel_class = fst chan_class;
      channel_params = snd chan_class;
      endpoint_left = left_endpoint;
      endpoint_right = right_endpoint;
      visibility = Lang.LeftForeign;
      n_instances = None;
    } : Lang.channel_def
  }
| left_endpoint = IDENT; DOUBLE_MINUS;
  right_endpoint = IDENT; COLON;
  chan_class = channel_class_concrete; n = array_dimm
  {
    {
      channel_class = fst chan_class;
      channel_params = snd chan_class;
      endpoint_left = left_endpoint;
      endpoint_right = right_endpoint;
      visibility = Lang.LeftForeign;
      n_instances = Some n;
    } : Lang.channel_def
  }
;

channel_class_concrete:
| chan_class_name = IDENT
  { (chan_class_name, []) }
| chan_class_name = IDENT; LEFT_ABRACK; params = separated_list(COMMA, param_value); RIGHT_ABRACK
  { (chan_class_name, params) }
;

// Instantiating the proc for comm
spawn:
| proc = IDENT; LEFT_PAREN; params = separated_list(COMMA,args_spawn); RIGHT_PAREN
  {
    {
      proc = proc;
      params = params;
      compile_params = [];
      interface_params = None
    } : Lang.spawn_def
  }
| proc = IDENT; LEFT_BRACKET; params = separated_list(COMMA, ifc_inst); RIGHT_BRACKET
  {
    {
      proc = proc;
      params  = [];
      compile_params = [];
      interface_params = Some params
    } : Lang.spawn_def
  }

| proc = IDENT; LEFT_ABRACK; compile_params = separated_list(COMMA, param_value); RIGHT_ABRACK;
  LEFT_PAREN; params = separated_list(COMMA, args_spawn); RIGHT_PAREN
  {
    {
      proc = proc;
      params = params;
      interface_params = None;
      compile_params = compile_params;
    } : Lang.spawn_def
  }
| proc = IDENT; LEFT_ABRACK; compile_params = separated_list(COMMA, param_value); RIGHT_ABRACK;
  LEFT_BRACKET; params = separated_list(COMMA, ifc_inst); RIGHT_BRACKET
  {
    {
      proc = proc;
      params  = [];
      compile_params = compile_params;
      interface_params = Some params
    } : Lang.spawn_def
  }
;

ifc_inst:
| pid = IDENT; PERIOD; id = IDENT
  {
    {
      pid = pid;
      pifc_id = id;
    } : Lang.ifc_instantiation
  }
args_spawn:
| ident = IDENT
  { Lang.SingleEp ident }
| ident = IDENT; idx = array_index_concrete
  { Lang.IndexedEp (ident, idx) }

array_index_concrete:
| LEFT_BRACKET; n = INT; RIGHT_BRACKET
  { Lang.IndexSingle n }
| LEFT_BRACKET; start = INT; PLUS; COLON; size = INT; RIGHT_BRACKET
  { Lang.IndexRange (start, size) }
| LEFT_BRACKET; start = INT; PLUS; COLON; size = INT;RIGHT_BRACKET; rest = array_index_concrete
  { Lang.IndexMultiDimRange (start, size, rest) }
| LEFT_BRACKET; n = INT; RIGHT_BRACKET;rest = array_index_concrete
  { Lang.IndexMultiDimSingle (n, rest) }

param_value:
| n = INT
  { Lang.IntParamValue n }
| t = data_type
  { Lang.TypeParamValue t }
;

//register declaration, To Do: Add support for declaration as well as init
reg_def:
  ident = IDENT; COLON; dtype = data_type
  {
    {
      name = ident;
      d_type = dtype;
      init = None;
    } : Lang.reg_def
  }
;
//term definitions for expressions
term:
| literal_str = BIT_LITERAL
  { Lang.Literal (ParserHelper.bit_literal_of_string literal_str) }
| literal_str = DEC_LITERAL
  { Lang.Literal (ParserHelper.dec_literal_of_string literal_str) }
| literal_str = HEX_LITERAL
  { Lang.Literal (ParserHelper.hex_literal_of_string literal_str) }
| literal_val = INT
  { Lang.Literal (Lang.NoLength literal_val)}
| ident = IDENT
  { Lang.Identifier ident }
| KEYWORD_RECURSE
  { Lang.Recurse }
;
//expressions
expr:
| KEYWORD_SET; lval = lvalue; COLON_EQ; v = node(expr) %prec KEYWORD_SET
  { Lang.Assign (lval, v) }
| e = term
  { e }
| e = un_expr
  { e }
| e = bin_expr
  { e }
| LEFT_PAREN; first_expr = node(expr); COMMA; tuple = separated_list(COMMA, node(expr)); RIGHT_PAREN
  { Lang.Tuple (first_expr::tuple) }
| LEFT_PAREN; RIGHT_PAREN
  { Lang.Tuple ([]) }
| LEFT_PAREN; e = expr; RIGHT_PAREN
  { e }
| KEYWORD_SYNC; ident = IDENT
  { Lang.Sync ident }
| KEYWORD_READY; msg_spec = message_specifier
  { Lang.Ready msg_spec }
| KEYWORD_PROBE; msg_spec = message_specifier
  { Lang.Probe msg_spec }
| KEYWORD_PUT; ident = IDENT; COLON_EQ; v = node(expr) %prec KEYWORD_PUT
  { Lang.SharedAssign (ident, v) }
| KEYWORD_LET; binding = IDENT; EQUAL; v = node(expr) %prec KEYWORD_LET
  { Lang.Let ([binding], None, v) }
| KEYWORD_LET; binding = IDENT; COLON; dtype = data_type; EQUAL; v = node(expr) %prec KEYWORD_LET
  { Lang.Let ([binding], Some(dtype), v) }
| v = node(expr); SEMICOLON; body = node(expr)
  { Lang.Join (v, body) }
| KEYWORD_SEND; send_pack = send_pack
  { Lang.Send send_pack }
| KEYWORD_RECV; recv_pack = recv_pack
  { Lang.Recv recv_pack }
| v = node(expr); DOUBLE_GT; body = node(expr)
  { Lang.Wait (v, body) }
| KEYWORD_GENERATE; LEFT_PAREN; i=IDENT; COLON; start = INT; COMMA; end_v = INT; COMMA;
  offset = INT; RIGHT_PAREN; LEFT_BRACE; body = node(expr); RIGHT_BRACE
  { Lang.generate_expr (i,start, end_v, offset, body) }
| KEYWORD_GENERATE_SEQ; LEFT_PAREN; i=IDENT; COLON; start = INT; COMMA; end_v = INT; COMMA;
  offset = INT; RIGHT_PAREN; LEFT_BRACE; body = node(expr); RIGHT_BRACE
  { Lang.generate_expr_seq (i,start, end_v, offset, body) }
| rec_sym; ident = IDENT; LEFT_BRACE; body = node(expr); RIGHT_BRACE
  { Lang.Recursion (ident, body) }
| KEYWORD_RECURSE; stid= IDENT
  { Lang.Recursor stid }
| e = if_branch
  { e }
| KEYWORD_CALL ; func = IDENT; LEFT_PAREN; args = separated_list(COMMA, node(expr)); RIGHT_PAREN
  { Lang.Call (func, args) }
| KEYWORD_CYCLE; n = INT
  { Lang.Cycle n }
| e = node(expr); LEFT_BRACKET; ind = index; RIGHT_BRACKET
  { Lang.Index (e, ind) }
| e = node(expr); PERIOD; fieldname = IDENT
  { Lang.Indirect (e, fieldname) }
| SHARP; LEFT_BRACE; components = separated_list(COMMA, node(expr)); RIGHT_BRACE
  { Lang.Concat (components, false) }
| SHARP; KEYWORD_FLAT; LEFT_BRACE; components = separated_list(COMMA, node(expr)); RIGHT_BRACE
  { Lang.Concat (components, true) }
| LEFT_ABRACK; LEFT_PAREN; expr = node(expr); RIGHT_PAREN; DOUBLE_COLON; dtype = data_type; RIGHT_ABRACK
  { Lang.Cast (expr, dtype) }
| LEFT_BRACE; e = expr; RIGHT_BRACE
  { e }
| KEYWORD_MATCH; e = node(expr); LEFT_BRACE; match_arm_list = separated_list(COMMA, match_arm); RIGHT_BRACE
  { Lang.Match (e, match_arm_list) }
| ASTERISK; reg_id = lvalue
  { Lang.Read reg_id }
| constructor_spec = constructor_spec; e = ioption(node(expr_in_parenthese))
  { Lang.Construct (constructor_spec, e) }
| record_name = IDENT; DOUBLE_COLON; LEFT_BRACE;
  base = node(expr); KEYWORD_WITH;
  record_fields = separated_nonempty_list(SEMICOLON, record_field_constr);
  RIGHT_BRACE
  { Lang.Record (record_name, record_fields, Some base) }
| record_name = IDENT; DOUBLE_COLON; LEFT_BRACE;
  record_fields = separated_nonempty_list(SEMICOLON, record_field_constr);
  RIGHT_BRACE
  { Lang.Record (record_name, record_fields, None) }
  (* debug operations *)
| KEYWORD_DPRINT; s = STR_LITERAL; LEFT_PAREN; v = separated_list(COMMA, node(expr)); RIGHT_PAREN
  { Lang.Debug (Lang.DebugPrint (s, v)) }
| KEYWORD_DFINISH
  { Lang.Debug Lang.DebugFinish }
| LEFT_BRACKET; li = separated_list(COMMA, node(expr)); RIGHT_BRACKET
  { Lang.List li }
| KEYWORD_XOFFER;  LEFT_BRACE; offer_arms = separated_list(COMMA, offer_arm); RIGHT_BRACE
  { Lang.XOffer (offer_arms, None) }
| KEYWORD_XOFFER; selector = IDENT; LEFT_BRACE; offer_arms = separated_list(COMMA, offer_arm); RIGHT_BRACE
  { Lang.XOffer (offer_arms, Some selector) }
| KEYWORD_OFFER;  LEFT_BRACE; offer_arms = separated_list(COMMA, offer_arm); RIGHT_BRACE
  { Lang.Offer offer_arms }
expr_in_parenthese:
  LEFT_PAREN; e = expr; RIGHT_PAREN
  { e }
;

if_branch:
| KEYWORD_IF; cond = node(expr); LEFT_BRACE; then_v = node(expr); RIGHT_BRACE;
  else_v = node(else_branch)?
  { Lang.IfExpr (cond, then_v, Option.value ~default:Lang.dummy_unit_node else_v) }
// | KEYWORD_TRY; ident = IDENT; EQUAL; KEYWORD_RECV; recv_pack = recv_pack
//   { Lang.TryRecv (ident, recv_pack, Lang.dummy_unit_node, Lang.dummy_unit_node) }
| KEYWORD_TRY; ident = IDENT; EQUAL; KEYWORD_RECV; recv_pack = recv_pack;
  LEFT_BRACE; then_v = node(expr); RIGHT_BRACE; else_v = node(else_branch)?
  { Lang.TryRecv (ident, recv_pack, then_v, Option.value ~default:Lang.dummy_unit_node else_v) }
// | KEYWORD_TRY; KEYWORD_SEND; send_pack = send_pack
//   { Lang.TrySend (send_pack, Lang.dummy_unit_node, Lang.dummy_unit_node) }
| KEYWORD_TRY; KEYWORD_SEND; send_pack = send_pack;
  LEFT_BRACE; then_v = node(expr); RIGHT_BRACE; else_v = node(else_branch)?
  { Lang.TrySend (send_pack, then_v, Option.value ~default:(Lang.dummy_ast_node_of_data @@ Lang.Tuple []) else_v) }
;

else_branch:
| KEYWORD_ELSE; LEFT_BRACE; else_v = expr; RIGHT_BRACE
  {
    else_v
  }
| KEYWORD_ELSE; e = if_branch
  {
    e
  }
;

constructor_spec:
  ty = IDENT; DOUBLE_COLON; variant = IDENT
  { let open Lang in {variant_ty_name = ty; variant} }
;
%inline record_field_constr:
  field_name = IDENT; EQUAL; field_value = node(expr)
  { (field_name, field_value) }
;
// The string that sends message
send_pack:
  msg_specifier = message_specifier;
  LEFT_PAREN; data = node(expr); RIGHT_PAREN
  {
    {
      Lang.send_msg_spec = msg_specifier;
      Lang.send_data = data;
    }
  }
;
// The command that recvs message
recv_pack:
  msg_specifier = message_specifier
  {
    {
      Lang.recv_msg_spec = msg_specifier
    }
  }
;

bin_expr:
| v1 = node(expr); DOUBLE_EQ; v2 = node(expr)
  { Lang.Binop (Lang.Eq, v1, (`Single v2)) }
| v1 = node(expr); KEYWORD_IN; LEFT_BRACE; v2 = separated_list(COMMA, node(expr)); RIGHT_BRACE
  { Lang.Binop (Lang.In, v1, (`List v2)) }
| v1 = node(expr); EXCL_EQ; v2 = node(expr)
  { Lang.Binop (Lang.Neq, v1, (`Single v2)) }
| v1 = node(expr); SHL; v2 = node(expr)
  { Lang.Binop (Lang.Shl, v1, (`Single v2)) }
| v1 = node(expr); SHR; v2 = node(expr)
  { Lang.Binop (Lang.Shr, v1, (`Single v2)) }
| v1 = node(expr); LEFT_ABRACK; v2 = node(expr)
  { Lang.Binop (Lang.Lt, v1, (`Single v2)) }
| v1 = node(expr); RIGHT_ABRACK; v2 = node(expr)
  { Lang.Binop (Lang.Gt, v1, (`Single v2)) }
| v1 = node(expr); LEFT_ABRACK_EQ; v2 = node(expr)
  { Lang.Binop (Lang.Lte, v1, (`Single v2)) }
| v1 = node(expr); RIGHT_ABRACK_EQ; v2 = node(expr)
  { Lang.Binop (Lang.Gte, v1, (`Single v2)) }
| v1 = node(expr); PLUS; v2 = node(expr)
  { Lang.Binop (Lang.Add, v1, (`Single v2)) }
| v1 = node(expr); ASTERISK; v2 = node(expr)
  { Lang.Binop (Lang.Mul, v1, (`Single v2)) }
| v1 = node(expr); MINUS; v2 = node(expr)
  { Lang.Binop (Lang.Sub, v1, (`Single v2)) }
| v1 = node(expr); XOR; v2 = node(expr)
  { Lang.Binop (Lang.Xor, v1, (`Single v2)) }
| v1 = node(expr); AND; v2 = node(expr)
  { Lang.Binop (Lang.And, v1, (`Single v2)) }
| v1 = node(expr); OR; v2 = node(expr)
  { Lang.Binop (Lang.Or, v1, (`Single v2)) }
| v1 = node(expr); DOUBLE_AND; v2 = node(expr)
  { Lang.Binop (Lang.LAnd, v1, (`Single v2)) }
| v1 = node(expr); DOUBLE_OR; v2 = node(expr)
  { Lang.Binop (Lang.LOr, v1, (`Single v2)) }
;

un_expr:
| MINUS; e = node(expr)
  { Lang.Unop (Lang.Neg, e) } %prec UMINUS
| TILDE; e = node(expr)
  { Lang.Unop (Lang.Not, e) }
| AND; e = node(expr)
  { Lang.Unop (Lang.AndAll, e) } %prec UAND
| OR; e = node(expr)
  { Lang.Unop (Lang.OrAll, e) } %prec UOR
;

lvalue:
| regname = IDENT
  { Lang.Reg regname }
| lval = lvalue; PERIOD; fieldname = IDENT
  { Lang.Indirected (lval, fieldname) }
| lval = lvalue; LEFT_BRACKET; ind = index; RIGHT_BRACKET
  { Lang.Indexed (lval, ind) }
;

index:
| i = node(expr)
  { Lang.Single i }
| le = node(expr); PLUS; COLON; sz = node(expr)
  { Lang.Range (le, sz) }
;

match_arm:
| pattern = node(expr); EQ_GT body_opt = node(expr)
  { (pattern, Some body_opt) }
;

offer_arm:
| arm = offer_arm_atom; EQ_GT; body = node(expr)
  { (Lang.OfferAtom arm, body) }
| LEFT_BRACE; arms = separated_nonempty_list(SEMICOLON, offer_arm_atom); RIGHT_BRACE; EQ_GT; body = node(expr)
  { (Lang.OfferConjunction arms, body) }
| SHARP; EQ_GT; body = node(expr)
  { (Lang.OfferAtom Lang.OfferWildcard, body) }
;
offer_arm_atom:
| KEYWORD_SEND; send_pack = send_pack
  { Lang.OfferSend send_pack }
| id = IDENT; EQUAL; KEYWORD_RECV; recv_pack = recv_pack
  { Lang.OfferRecv (id, recv_pack) }
;  

//Definition of messages: To Do: Doesnt support custom lifetime types, just sync?
message_def:
| dir = message_direction; ident = IDENT; COLON; LEFT_PAREN; data = separated_list(COMMA, sig_type_chan_local); RIGHT_PAREN;
  left_sync_mode_opt = message_sync_mode_spec?;
  right_sync_mode_opt = recv_message_sync_mode_spec?
  {
    let (send_sync_mode_opt, recv_sync_mode_opt) =
      match dir with
      | Lang.Inp -> (right_sync_mode_opt, left_sync_mode_opt)
      | Lang.Out -> (left_sync_mode_opt, right_sync_mode_opt)
    in
    let send_sync_mode = Option.value ~default:Lang.Dynamic send_sync_mode_opt
    and recv_sync_mode = Option.value ~default:Lang.Dynamic recv_sync_mode_opt in
    {
      name = ident;
      dir = dir;
      send_sync = send_sync_mode;
      recv_sync = recv_sync_mode;
      handshake_mode = Lang.ValidAck;
      sig_types = data;
      span = {st = $startpos; ed = $endpos}
    } : Lang.message_def
  }
| dir = message_direction; ident = IDENT; COLON; LEFT_PAREN; data = separated_list(COMMA, sig_type_chan_local); RIGHT_PAREN;
DOUBLE_LEFT_ABRACK;
  {
    {
      name = ident;
      dir = dir;
      send_sync = Lang.Dynamic;
      recv_sync = Lang.Dynamic;
      handshake_mode = Lang.ValidReady;
      sig_types = data;
      span = {st = $startpos; ed = $endpos}
    } : Lang.message_def
  }
| dir = message_direction; ident = IDENT; COLON; LEFT_PAREN; data = separated_list(COMMA, sig_type_chan_local); RIGHT_PAREN;
DOUBLE_GT;
  {
    {
      name = ident;
      dir = dir;
      send_sync = Lang.Dynamic;
      recv_sync = Lang.Dynamic;
      handshake_mode = Lang.ValidAck;
      sig_types = data;
      span = {st = $startpos; ed = $endpos}
    } : Lang.message_def
  }
;

// progress_contract:
// | ARROW_LONG; msgs = separated_list(OR, IDENT)
//   { msgs }

//To Do: Support for multiple message types
recv_message_sync_mode_spec:
  MINUS; sync = message_sync_mode_spec
  { sync }
;

message_sync_mode_spec:
| AT; SHARP; n = INT
  {
    Lang.Static (n - 1, n)
  }
| AT; SHARP; o = INT; TILDE; n = INT
  {
    Lang.Static (o, n)
  }
| AT; SHARP; m = IDENT
  {
    Lang.Dependent (m, 0)
  }
| AT; SHARP; m = IDENT; PLUS; n = INT
  {
    Lang.Dependent (m, n)
  }
| AT; KEYWORD_DYN
  {
    Lang.Dynamic
  }
;

message_direction:
| KEYWORD_LEFT
  { Lang.Inp }
| KEYWORD_RIGHT
  { Lang.Out }
;

// sig_type:
//   dtype = data_type; AT; lifetime_opt = lifetime_spec?
//   {
//     let lifetime = Option.value ~default:Lang.sig_lifetime_this_cycle lifetime_opt in
//     {
//       dtype = dtype;
//       lifetime = lifetime;
//     } : Lang.sig_type
//   }
// ;

sig_type_chan_local:
|  dtype = data_type; AT; lifetime_opt = lifetime_spec_chan_local?
  {
    let lifetime = Option.value ~default:Lang.sig_lifetime_this_cycle_chan_local lifetime_opt in
    {
      dtype = dtype;
      lifetime = lifetime;
    } : Lang.sig_type_chan_local
  }
| KEYWORD_VOID; AT; lifetime_opt = lifetime_spec_chan_local?
  {
    let lifetime = Option.value ~default:Lang.sig_lifetime_this_cycle_chan_local lifetime_opt in
    {
      dtype = Lang.unit_dtype;
      lifetime = lifetime;
    } : Lang.sig_type_chan_local
  }
;

(* A compile-time integer arithmetic expression for use in array sizes.
   Supports integer literals, named params/macros, and +, -, *, with parentheses. *)
param_arith_expr:
| n = INT
  { ParamEnv.PE_Int n }
| id = IDENT
  { ParamEnv.PE_Id id }
| LEFT_PAREN; e = param_arith_expr; RIGHT_PAREN
  { e }
| e1 = param_arith_expr; PLUS;     e2 = param_arith_expr
  { ParamEnv.PE_Add (e1, e2) }
| e1 = param_arith_expr; MINUS;    e2 = param_arith_expr
  { ParamEnv.PE_Sub (e1, e2) }
| e1 = param_arith_expr; ASTERISK; e2 = param_arith_expr
  { ParamEnv.PE_Mul (e1, e2) }
;

int_maybe_param:
| n = INT
  { ParamEnv.Concrete n }
| ident = IDENT
  { ParamEnv.Param ident }
| e1 = param_arith_expr; PLUS;     e2 = param_arith_expr
  { ParamEnv.Expr (ParamEnv.PE_Add (e1, e2)) }
| e1 = param_arith_expr; MINUS;    e2 = param_arith_expr
  { ParamEnv.Expr (ParamEnv.PE_Sub (e1, e2)) }
| e1 = param_arith_expr; ASTERISK; e2 = param_arith_expr
  { ParamEnv.Expr (ParamEnv.PE_Mul (e1, e2)) }
;

data_type_no_array:
// | dtype = data_type; LEFT_BRACKET; n = IDENT; RIGHT_BRACKET
//   { `Parametrized (dtype, n) }
| KEYWORD_LOGIC
  { `Logic }
| typename = IDENT %prec PREC_NAMED_TYPE
  { `Named (typename, []) }
| typename = IDENT; LEFT_ABRACK; compile_params = separated_list(COMMA, param_value); RIGHT_ABRACK;
  { `Named (typename, compile_params) }
| LEFT_PAREN; comps = separated_list(COMMA, data_type); RIGHT_PAREN
  { `Tuple comps }
;

data_type_array_range:
| LEFT_BRACKET; n = int_maybe_param; RIGHT_BRACKET
  { n }
;

data_type:
| dtype = data_type_no_array; ranges = data_type_array_range*
  { List.fold_right (fun n dtype_c -> `Array (dtype_c, n)) ranges dtype }
  (* We need to reverse the array ranges so logic[3][2] is 3 arrays of length 2 *)
;

lifetime_spec:
  e_time = timestamp
  {
    {
      e = e_time;
    } : Lang.sig_lifetime
  }
;

lifetime_spec_chan_local:
  e_time = timestamp_chan_local
  {
    {
      e = e_time;
    } : Lang.sig_lifetime_chan_local
  }
;


timestamp:
| SHARP; n = INT
  { `Cycles n }
| msg_spec = message_specifier
  { `Message_with_offset (msg_spec, 0, true) }
| KEYWORD_ETERNAL
  { `Eternal }
;

timestamp_chan_local:
| SHARP; n = INT
  { `Cycles n }
| msg = IDENT
  { `Message_with_offset (msg, 0, true) }
| msg = IDENT; k = plus_minus; n = INT
  { `Message_with_offset (msg, n, k) }
| KEYWORD_ETERNAL
  { `Eternal }
;

plus_minus:
| PLUS
  { true }
| MINUS
  { false }
;

//Message string
message_specifier:
|  endpoint = IDENT; PERIOD; msg_type = IDENT
  {
    {
      endpoint = endpoint;
      msg = msg_type;
    } : Lang.message_specifier
  }
| endpoint = IDENT;indx_str=get_array_index_string;PERIOD; msg_type = IDENT
  {
    {
      endpoint = Printf.sprintf "%s%s" endpoint indx_str;
      msg = msg_type;
    } : Lang.message_specifier
  }
;


get_array_index_string:
| LEFT_BRACKET; idx_content = int_or_id; RIGHT_BRACKET
  { Printf.sprintf "[%s]" idx_content }
| LEFT_BRACKET; idx_content = int_or_id; RIGHT_BRACKET; rest = get_array_index_string
  { Printf.sprintf "[%s]%s" idx_content rest }

int_or_id: 
| n = INT
  { string_of_int n }
| id = IDENT
  { id }
shared_var_def:
  KEYWORD_SHARED; LEFT_PAREN; lifetime = lifetime_spec; RIGHT_PAREN; ident = IDENT; KEYWORD_ASSIGNED; KEYWORD_BY; thread_id = INT
  {
    {
      ident = ident;
      assigning_thread = thread_id;
      shared_lifetime = lifetime;
    } : Lang.shared_var_def
  }
;

macro_def:
  | KEYWORD_CONST; id = IDENT; EQUAL; value = INT; SEMICOLON
    {
      { id = id; value = value } : Lang.macro_def
    }
;

function_def:
  | KEYWORD_FUNCTION; name = IDENT; LEFT_PAREN; args = separated_list(COMMA, typed_arg); RIGHT_PAREN; LEFT_BRACE; body = node(expr); RIGHT_BRACE
    {
      { name = name; args = args; body = body } : Lang.func_def
    }
;

typed_arg:
  | name = IDENT; COLON; dtype = data_type
    {
      { arg_name = name; arg_type = Some dtype } : Lang.typed_arg
    }
  | name = IDENT
    {
      { arg_name = name; arg_type = None } : Lang.typed_arg
    }
