open Lang

type event_graph = EventGraph.event_graph
type proc_graph = EventGraph.proc_graph  (* Ensure proc_graph is defined in EventGraph *)
type event_graph_collection = EventGraph.event_graph_collection

module Format = CodegenFormat

type port_def = CodegenPort.t


let codegen_ports ?(resolve = CodegenPort.default_resolver) printer (graphs : event_graph_collection)
                      (endpoints : endpoint_def list) (is_mod_comb : bool)=
  let port_list = CodegenPort.gather_ports ~resolve graphs.channel_classes endpoints in
  let rec print_port_list port_list =
  match port_list with
  | [] -> ()
  | port :: [] ->
      CodegenPort.format graphs.typedefs graphs.macro_defs port |> CodegenPrinter.print_line printer
  | port :: port_list' ->
      CodegenPort.format graphs.typedefs graphs.macro_defs port |> Printf.sprintf "%s," |> CodegenPrinter.print_line printer;
      print_port_list port_list'
  in
  if is_mod_comb then
    print_port_list port_list
  else
    print_port_list ([CodegenPort.clk; CodegenPort.rst] @ port_list);
  port_list

let codegen_spawns printer (graphs : event_graph_collection) (g : proc_graph) =
  let parent_resolve = HandshakeResolve.resolver_for graphs g in

  let format_connection (dst : string) (src : string) =
    Printf.sprintf ".%s (%s)" dst src
  in
  let print_connections connections =
    let connection_count = List.length connections in
    List.iteri (fun idx connection ->
      let suffix = if idx = connection_count - 1 then "" else "," in
      Printf.sprintf "%s%s" connection suffix |> CodegenPrinter.print_line printer
    ) connections
  in

  let gen_spawn = fun (idx : int) ((module_name, spawn) : string * (spawn_def ast_node)) ->
    let spawned_proc = CodegenHelpers.lookup_proc graphs.external_event_graphs module_name |> Option.get in

    let uses_anvil_port_layout = match spawned_proc.extern_module, spawned_proc.proc_body with
    | None, _ -> true
    | (Some _ , Lang.Extern (_,body)) -> (
        if List.is_empty body.named_ports then true
        else false
      )
    | _ -> true in
    let spawn_is_comb = (List.for_all (fun (thread , _) ->
    (thread : EventGraph.event_graph).comb
  ) spawned_proc.threads) && uses_anvil_port_layout in

    let child_resolve = HandshakeResolve.resolver_for graphs spawned_proc in

    CodegenPrinter.print_comment printer (Printf.sprintf "spawn %s instance %d" module_name idx);
    Printf.sprintf "%s _spawn_%d (" module_name idx|> CodegenPrinter.print_line printer ~lvl_delta_post:1;

    let endpoint_connections = fun (arg_endpoint : endpoint_def) (param_ident : identifier) ->
      let parent_endpoint =
        match MessageCollection.lookup_endpoint g.messages param_ident with
        | Some ep -> ep
        | None -> 
            raise (Failure (Printf.sprintf "Could not find endpoint '%s'in parent process" param_ident))
      in
      let parent_endpoint_name = CodegenFormat.canonicalize_endpoint_name param_ident (List.hd g.threads |> fst) in
      let channel_class = MessageCollection.lookup_channel_class graphs.channel_classes parent_endpoint.channel_class |> Option.get in
      let msg_connections = fun (msg : message_def) ->
        let msg = ParamConcretise.concretise_message channel_class.params parent_endpoint.channel_params msg in
        let sync_connections =
          (if CodegenPort.message_has_valid_port msg then
            [format_connection
              (Format.format_msg_valid_signal_name arg_endpoint.name msg.name)
              (Format.format_msg_valid_signal_name parent_endpoint_name msg.name)]
          else [])
          @
          (* Each module names its reverse port using its own resolved mode. *)
          (let child_mode = child_resolve arg_endpoint.name msg.name in
           let parent_reverse =
             match parent_resolve parent_endpoint_name msg.name with
             | ValidAck -> Format.format_msg_ack_signal_name parent_endpoint_name msg.name
             | ValidReady -> Format.format_msg_ready_signal_name parent_endpoint_name msg.name
           in
           if CodegenPort.message_has_ack_port ~mode:child_mode msg then
            [format_connection
              (Format.format_msg_ack_signal_name arg_endpoint.name msg.name)
              parent_reverse]
          else if CodegenPort.message_has_ready_port ~mode:child_mode msg then
            [format_connection
              (Format.format_msg_ready_signal_name arg_endpoint.name msg.name)
              parent_reverse]
          else [])
        in
        let data_connections =
          List.filter_map (fun (idx, _) ->
            if CodegenPort.message_has_data_port msg idx then
              Some (format_connection
                (Format.format_msg_data_signal_name arg_endpoint.name msg.name idx)
                (Format.format_msg_data_signal_name parent_endpoint_name msg.name idx))
            else
              None
          ) (List.mapi (fun idx sig_type -> (idx, sig_type)) msg.sig_types)
        in
        sync_connections @ data_connections
      in
      List.concat_map msg_connections channel_class.messages
    in
    let param_count = List.fold_left (fun acc p -> match p with Lang.SingleEp _ -> acc + 1 | Lang.IndexedEp (_,idx) -> acc + (Lang.calculate_array_index_concrete_size idx)) 0 spawn.d.params in
    if List.length spawned_proc.messages.args <> param_count then
      raise (Failure (Printf.sprintf "Invalid number of arguments for spawn of proc %s | Expected %d | Got %d %s"  spawned_proc.name param_count (List.length spawned_proc.messages.args) (String.concat ", " (List.map (fun (ep : endpoint_def) -> ep.name) spawned_proc.messages.args) )));
    let clock_connections = if spawn_is_comb then [] else [".clk_i"; ".rst_ni"] in
    let message_connections =
      List.map2 endpoint_connections spawned_proc.messages.args (Lang.preprocess_ep_spawn_args spawn.d.params)
      |> List.concat
    in
    print_connections (clock_connections @ message_connections);
    CodegenPrinter.print_line printer ~lvl_delta_pre:(-1) ");"
  in List.iteri gen_spawn g.spawns

let codegen_endpoints ?(resolve = CodegenPort.default_resolver) printer (graphs : event_graph_collection) (g : event_graph) =
  let print_port_signal_decl = fun (port : port_def) ->
    if port.dtype <> Lang.unit_dtype then
    Printf.sprintf "%s %s;" (Format.format_dtype graphs.typedefs graphs.macro_defs port.dtype) (port.name) |>
      CodegenPrinter.print_line printer
  in
  let local_endpoint_ports =
    List.filter (fun (p : endpoint_def) -> p.dir = Left) g.messages.endpoints
    |> CodegenPort.gather_ports ~resolve graphs.channel_classes
  in
  if local_endpoint_ports <> [] then
    CodegenPrinter.print_section printer (Printf.sprintf "Thread %d local endpoint mirrors" g.thread_id);
  List.iter print_port_signal_decl local_endpoint_ports

let codegen_wire_assignment resolve printer (graphs : event_graph_collection) (g : event_graph) (w : WireCollection.wire) =
  let lookup_msg_def msg = MessageCollection.lookup_message g.messages msg graphs.channel_classes in
  let wire_name = Format.format_wirename w.thread_id w.id in
  let inline_source_comment =
    match w.source with
    | Literal _ -> ""
    | _ -> Printf.sprintf " // %s" (Format.format_wire_source_comment w)
  in
  match w.source with
  | Cases (vw, sw, d) -> (
    CodegenPrinter.print_comment printer (Printf.sprintf "%s: %s" wire_name (Format.format_wire_source_comment w));
    CodegenPrinter.print_line ~lvl_delta_post:1 printer
      @@ Printf.sprintf "always_comb begin: _%s_cases_assign" wire_name;
    CodegenPrinter.print_line ~lvl_delta_post:1 printer
      @@ Printf.sprintf "unique case (%s)" @@ Format.format_wirename vw.thread_id vw.id;
    List.iter (fun ((wp, wb) : WireCollection.wire * WireCollection.wire) ->
      CodegenPrinter.print_line ~lvl_delta_post:1 printer
        @@ Printf.sprintf "%s:" @@ Format.format_wirename wp.thread_id wp.id;
      CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
        @@ Printf.sprintf "%s = %s;" wire_name
        @@ (Format.format_wirename wb.thread_id wb.id);
    ) sw;
    CodegenPrinter.print_line ~lvl_delta_post:1 printer "default:";
    CodegenPrinter.print_line ~lvl_delta_post:(-1) printer
      @@ Printf.sprintf "%s = %s;" wire_name
      @@ (Format.format_wirename d.thread_id d.id);
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "endcase";
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
  )
  | Update (base_w, updates) -> (
    CodegenPrinter.print_comment printer (Printf.sprintf "%s: %s" wire_name (Format.format_wire_source_comment w));
    CodegenPrinter.print_line ~lvl_delta_post:1 printer
      @@ Printf.sprintf "always_comb begin: _%s_update_assign" wire_name;
    CodegenPrinter.print_line printer
      @@ Printf.sprintf "%s = %s;" wire_name
      @@ (Format.format_wirename base_w.thread_id base_w.id);
    List.iter (fun (offset, size, (update_w : EventGraph.wire)) ->
      CodegenPrinter.print_line printer
      @@ Printf.sprintf "%s[%d +: %d] = %s;" wire_name
        offset size @@ (Format.format_wirename update_w.thread_id update_w.id);
    ) updates;
    CodegenPrinter.print_line ~lvl_delta_pre:(-1) printer "end"
  )
  | _ -> (
    let expr =
      match w.source with
      | Literal lit -> Format.format_literal lit
      | Binary (binop, w1, w2) ->
        (
          match w2 with
          | `List ws2 ->
            Printf.sprintf "%s %s {%s}"
              (Format.format_wirename w1.thread_id w1.id)
              (Format.format_binop binop)
              (List.map (fun (w' : WireCollection.wire) -> Format.format_wirename w'.thread_id w'.id) ws2 |>
            String.concat ", ")
          | `Single w2n ->
              Printf.sprintf "%s %s %s"
                (Format.format_wirename w1.thread_id w1.id)
                (Format.format_binop binop)
                (Format.format_wirename w2n.thread_id w2n.id)
        )
      | Unary (unop, w') ->
        Printf.sprintf "%s%s"
          (Format.format_unop unop)
          (Format.format_wirename w'.thread_id w'.id)
      | Switch (sw, d) ->
        let conds = List.map
          (fun ((cond, v) : WireCollection.wire * WireCollection.wire) ->
            Printf.sprintf "(%s) ? %s : "
              (Format.format_wirename cond.thread_id cond.id)
              (Format.format_wirename v.thread_id v.id)
          )
          sw
        |> String.concat "" in
        Printf.sprintf "%s%s" conds (Format.format_wirename d.thread_id d.id)
      | RegRead reg_ident -> Format.format_regname_current reg_ident
      | Concat ws ->
        List.map (fun (w' : WireCollection.wire) -> Format.format_wirename w'.thread_id w'.id) ws |>
          String.concat ", " |> Printf.sprintf "{%s}"
      | MessagePort (msg, idx) ->
        let msg_endpoint = CodegenFormat.canonicalize_endpoint_name msg.endpoint g in
        Format.format_msg_data_signal_name msg_endpoint msg.msg idx
      | Slice (w', base_i, len) ->
        Printf.sprintf "%s[%s +: %d]" (Format.format_wirename w'.thread_id w'.id)
          (Format.format_wire_maybe_const base_i)
          len
      | MessageValidPort msg ->
        let m = Option.get @@ lookup_msg_def msg in
        if CodegenPort.message_has_valid_port m then
          CodegenFormat.format_msg_valid_signal_name (CodegenFormat.canonicalize_endpoint_name msg.endpoint g) msg.msg
        else "1'b1"
      | MessageAckPort msg | MessageReadyPort msg ->
        let m = Option.get @@ lookup_msg_def msg in
        let endpoint = CodegenFormat.canonicalize_endpoint_name msg.endpoint g in
        (* These reads are created before handshake resolution. *)
        (match CodegenPort.site_reverse_signal ~mode:(resolve endpoint msg.msg) m with
         | Some UsesAck -> CodegenFormat.format_msg_ack_signal_name endpoint msg.msg
         | Some UsesReady -> CodegenFormat.format_msg_ready_signal_name endpoint msg.msg
         | None -> "1'b1")
        
        
      | Cases _ | Update _ -> failwith "Something went wrong!"
    in
    CodegenPrinter.print_line printer
      @@
      if w.is_const && w.size > 0 then
        Printf.sprintf "localparam %s %s = %s;%s"
          (Format.format_dtype graphs.typedefs graphs.macro_defs (`Array (`Logic, ParamEnv.Concrete w.size)))
          wire_name
          expr
          inline_source_comment
      else
        Printf.sprintf "assign %s = %s;" wire_name expr
  )

let codegen_post_declare resolve printer (graphs : event_graph_collection) (g : event_graph) =
  let codegen_wire_decl = fun (w: WireCollection.wire) ->
    if not w.is_const && w.size > 0 then
      Printf.sprintf "%s %s; // %s"
        (Format.format_dtype graphs.typedefs graphs.macro_defs (`Array (`Logic, ParamEnv.Concrete w.size)))
        (Format.format_wirename w.thread_id w.id)
        (Format.format_wire_source_comment w) |>
        CodegenPrinter.print_line printer
  in
  let wires_in_id_order = List.rev g.wires.wire_li in
  let declared_wires = List.filter (fun (w : WireCollection.wire) -> not w.is_const && w.size > 0) wires_in_id_order in
  if declared_wires <> [] then
    CodegenPrinter.print_section printer (Printf.sprintf "Thread %d wires" g.thread_id);
  List.iter codegen_wire_decl declared_wires;
  if wires_in_id_order <> [] then
    CodegenPrinter.print_section printer (Printf.sprintf "Thread %d wire assignments" g.thread_id);
  List.iter (codegen_wire_assignment resolve printer graphs g) wires_in_id_order

let codegen_regs printer (graphs : event_graph_collection) (g : event_graph) =
  let visible_regs = Utils.StringMap.filter (fun _ (r : reg_def) -> r.d_type <> Lang.unit_dtype) g.regs in
  if not (Utils.StringMap.is_empty visible_regs) then
    CodegenPrinter.print_section printer (Printf.sprintf "Thread %d registers" g.thread_id);
  Utils.StringMap.iter
    (
      fun _ (r : reg_def) ->
        let open CodegenFormat in
        Printf.sprintf "%s %s; // register %s"
          (format_dtype graphs.typedefs graphs.macro_defs r.d_type)
          (format_regname_current r.name)
          r.name |>
        CodegenPrinter.print_line printer
    )
    visible_regs

let codegen_proc printer (config : Config.compile_config) (graphs : EventGraph.event_graph_collection) (g : proc_graph) =

  let uses_anvil_port_layout = match g.extern_module ,g.proc_body with
    | None, _ -> true
    | (Some _ , Lang.Extern (_,body)) -> (
        if List.is_empty body.named_ports then true
        else false
      )
    | _ -> true in
  let is_mod_comb = (List.for_all (fun (thread , _) ->
    (thread : EventGraph.event_graph).comb
  ) g.threads) && uses_anvil_port_layout in


  CodegenPrinter.print_section printer (Printf.sprintf "Process %s" g.name);
  Printf.sprintf "module %s (" g.name |> CodegenPrinter.print_line printer ~lvl_delta_post:1;

  CodegenPrinter.print_comment printer "ports";
  let resolve = HandshakeResolve.resolver_for graphs g in
  let _ = codegen_ports ~resolve printer graphs g.messages.args is_mod_comb in
  CodegenPrinter.print_line printer ~lvl_delta_pre:(-1) ~lvl_delta_post:1 ");";

  (
    match g.extern_module, g.proc_body with
    | (Some extern_mod_name, Lang.Extern (_, body)) ->
      let open Lang in
      CodegenPrinter.print_section printer (Printf.sprintf "External module binding: %s" extern_mod_name);
      Printf.sprintf "%s _extern_mod (" extern_mod_name
        |> CodegenPrinter.print_line printer ~lvl_delta_post:1;
      let connected_ports = ref Utils.StringSet.empty in
      let print_binding ext i len local =
        let fmt = if (i = (len-1)) then (
          Printf.sprintf ".%s (%s)"
        ) else
          Printf.sprintf ".%s (%s),"
        in connected_ports := Utils.StringSet.add local !connected_ports;
        fmt ext local
          |> CodegenPrinter.print_line printer
      in
      let len1 = List.length body.named_ports in
      let len2 = List.fold_left(
        fun acc (_, d,v,a) ->
        (
            match d,v,a with
            | Some _, Some _, Some _ -> acc + 3
            | Some _, Some _ , None -> acc + 2
            | Some _ , None , Some _ -> acc + 2
            | None , Some _ , Some _ -> acc + 2
            | Some _ , None , None -> acc + 1
            | None , Some _ , None -> acc + 1
            | None , None , Some _ -> acc + 1
            | None , None , None -> acc
        )
      ) 0 body.msg_ports in
      let len = len1 + len2 in
      List.iteri (fun i (port_name, extern_port_name) ->
        print_binding extern_port_name i len port_name 
      ) body.named_ports;
      let i_sync = ref 0 in
      List.iter (fun (msg, extern_data_opt, extern_vld_opt, extern_ack_opt) ->
        let print_msg_port_opt formatter extern_opt =
        (  
          match extern_opt with
          | None -> ()
          | Some extern_port ->
            let i_off = len1 + !i_sync in
            i_sync := !i_sync + 1;
            formatter msg.endpoint msg.msg |> print_binding extern_port i_off len
        );
        in
        let open Format in
        print_msg_port_opt (fun e m -> format_msg_data_signal_name e m 0) extern_data_opt;
        print_msg_port_opt format_msg_valid_signal_name extern_vld_opt;
        print_msg_port_opt format_msg_ack_signal_name extern_ack_opt
      ) body.msg_ports;
      CodegenPrinter.print_line printer  ~lvl_delta_pre:(-1) ");";
      let ports = CodegenPort.gather_ports ~resolve graphs.channel_classes g.messages.args in
      List.iter (fun p ->
        let open CodegenPort in
        match p.dir with
        | Inp -> ()
        | Out -> (
          if Utils.StringSet.mem p.name !connected_ports |> not then (
            (* not connected, assign default values *)
            Printf.sprintf "assign %s = 'b1;" p.name
              |> CodegenPrinter.print_line printer
          )
        )
      ) ports
    | _ ->
      let initEvents = fst @@ List.hd g.threads in

      codegen_endpoints ~resolve printer graphs initEvents;

      codegen_spawns printer graphs g;

      codegen_regs printer graphs initEvents;
      if (not is_mod_comb) then CodegenStates.codegen_proc_states printer g;
      let shared_regs = CodegenStates.codegen_shared_reg_transitions printer g in
      
      List.iter (fun ((thread : EventGraph.event_graph), reset_by) ->
          CodegenPrinter.print_section printer (Printf.sprintf "Thread %d implementation" thread.thread_id);
          codegen_post_declare resolve printer graphs thread;
          CodegenStates.codegen_states shared_regs printer config graphs g thread reset_by;
      ) g.threads
  );

  CodegenPrinter.print_line printer ~lvl_delta_pre:(-1) "endmodule"

let generate_preamble out =
  [
    "// Generated by Anvil.";
    "// Debug hints: thread_<n>_wire_<m> are expression wires; EVENTS<n>[m].event_current marks active events.";
    "/* verilator lint_off UNOPTFLAT */";
    "/* verilator lint_off WIDTHTRUNC */";
    "/* verilator lint_off WIDTHEXPAND */";
    "/* verilator lint_off WIDTHCONCAT */"
  ] |> List.iter (Printf.fprintf out "%s\n")

let generate_extern_import out file_name =
  In_channel.with_open_text file_name
    (fun in_channel ->
      let eof = ref false in
      while not !eof do
        match In_channel.input_line in_channel with
        | Some line ->
          Out_channel.output_string out line;
          Out_channel.output_char out '\n'
        | None -> eof := true
      done
    )

let generate (out : out_channel)
             (config : Config.compile_config)
             (graphs : EventGraph.event_graph_collection) : unit =
  let printer = CodegenPrinter.create out 2 in
  List.iter (codegen_proc printer config graphs) graphs.event_graphs
