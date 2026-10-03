(* Readable dump of a parsed compilation unit. *)

open Lang

let print (cunit : compilation_unit) out =
  let p fmt = Printf.fprintf out fmt in
  p "file: %s\n" (Option.value cunit.cunit_file_name ~default:"<stdin>");
  List.iter (fun (imp : import_directive) ->
    p "import %s%s\n" (if imp.is_extern then "extern " else "") imp.file_name) cunit.imports;

  p "\n# macros\n";
  List.iter (fun (m : macro_def) -> p "%s = %d\n" m.id m.value) cunit.macro_defs;

  p "\n# types\n";
  List.iter (fun (t : type_def) -> p "%s = %s\n" t.name (string_of_data_type t.body)) cunit.type_defs;

  p "\n# channel classes\n";
  List.iter (fun (cc : channel_class_def) ->
    p "chan %s\n" cc.name;
    List.iter (fun (m : message_def) ->
      let lifetime (lt : sig_lifetime_chan_local) = match lt.e with
        | `Cycles n -> Printf.sprintf "#%d" n
        | `Eternal -> "E"
        | `Message_with_offset (msg, offset, plus) ->
          Printf.sprintf "%s%+d" msg (if plus then offset else -offset)
      in
      let sigs = List.map (fun (s : sig_type_chan_local) ->
        string_of_data_type s.dtype ^ "@" ^ lifetime s.lifetime) m.sig_types in
      let handshake = match m.handshake_mode with
        | Some ValidAck -> " >>"
        | Some ValidReady -> " <<"
        | None -> ""
      in
      p "  %s %s : (%s)%s\n" (match m.dir with Inp -> "left" | Out -> "right")
        m.name (String.concat ", " sigs) handshake) cc.messages) cunit.channel_classes;

  p "\n# session types\n";
  List.iter (fun (s : session_def ast_node) ->
    p "%s = %s\n" s.d.name (string_of_protocol s.d.body.d)) cunit.session_defs;

  p "\n# pools\n";
  List.iter (fun (pool : interface_pool_def ast_node) ->
    p "pool %s: %s\n" pool.d.pool_id
      (String.concat ", " (List.map (fun (m : interface_mem_def ast_node) -> m.d.inf_mem_id)
         pool.d.interface_members))) cunit.pools;

  p "\n# processes\n";
  List.iter (fun (proc : proc_def) ->
    p "proc %s(%s)\n" proc.name
      (String.concat ", " (List.map (fun (ep : endpoint_def ast_node) ->
         ep.d.name ^ " : " ^ ep.d.channel_class) proc.args));
    match proc.body with
    | Extern (mod_name, _) -> p "  extern %s\n" mod_name
    | Native body ->
      List.iter (fun (r : reg_def ast_node) ->
        p "  reg %s : %s\n" r.d.name (string_of_data_type r.d.d_type)) body.regs;
      List.iter (fun (c : channel_def ast_node) ->
        p "  chan %s -- %s : %s\n" c.d.endpoint_left c.d.endpoint_right c.d.channel_class) body.channels;
      List.iter (fun (s : spawn_def ast_node) -> p "  spawn %s\n" s.d.proc) body.spawns;
      List.iteri (fun i ((e : expr_node), _) ->
        p "  thread %d:\n    %s\n" i (string_of_expr e.d)) body.threads) cunit.procs
