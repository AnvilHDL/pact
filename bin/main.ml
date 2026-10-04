(** Saves the fields graph building mutates; the returned function restores them. *)
let snapshot_parsed_units (cunits : (string * Anvil.Lang.compilation_unit) list) =
  let open Anvil.Lang in
  let saved = List.concat_map (fun (_, (c : compilation_unit)) ->
    List.map (fun (p : proc_def) ->
      let body = match p.body with
        | Native b -> Some (b, b.channels, List.map (fun (s : spawn_def ast_node) -> (s, s.d.params)) b.spawns)
        | Extern _ -> None
      in
      (p, p.args, body)) (c.procs @ c._extern_procs)) cunits
  in
  fun () ->
    List.iter (fun ((p : proc_def), args, body) ->
      p.args <- args;
      Option.iter (fun ((b : proc_def_body), channels, spawns) ->
        b.channels <- channels;
        List.iter (fun ((s : spawn_def ast_node), params) -> s.d.params <- params) spawns) body) saved

(** Prints the AST and check results; the AST is produced whenever parsing succeeds. *)
let compile_with_ast_output config =
  let open Anvil in
  let errors_of msg = JsonOutput.error_message_to_json_errors "error" msg in
  let internal_error what exn =
    errors_of [Except.Text (Printf.sprintf "Internal compiler error while %s: %s" what (Printexc.to_string exn))]
  in
  let recovered = ref [] in
  let result =
    match CompileDriver.parse ~recover:(fun msg -> recovered := !recovered @ [msg]) config with
    | exception CompileHelpers.CompileError msg -> JsonOutput.failure_output (errors_of msg)
    | cunits ->
      let check_errors =
        (* units that are not well-formed are not checked further *)
        if !recovered <> [] then List.concat_map errors_of !recovered else begin
          SessionTrace.enabled := true;
          let restore = snapshot_parsed_units cunits in
          let null_out = open_out Filename.null in
          Fun.protect ~finally:(fun () -> close_out_noerr null_out; restore ()) (fun () ->
            try CompileDriver.compile_units null_out { config with just_check = true } cunits; []
            with
            | CompileHelpers.CompileError msg -> errors_of msg
            | exn -> internal_error "checking" exn)
        end
      in
      let (ast, serialisation_errors) =
        try
          (Some (AstJson.of_compilation_units ~session_at:AstJson.traced_session_at (List.rev_map snd cunits)), [])
        with exn -> (None, internal_error "serialising the AST" exn)
      in
      JsonOutput.ast_output ast (serialisation_errors @ check_errors)
  in
  print_endline (JsonOutput.json_output_to_string result)

let compile_with_json_output config =
  let open Anvil.Config in
  if config.input_filenames = [] then begin
  let json_errors = [Anvil.JsonOutput.{
    error_type = "error";
    path = None;
    description = [ { kind = "text"; text = Some "Error: a file name must be supplied!"; trace = None } ]
  }] in
    let json_result = Anvil.JsonOutput.failure_output json_errors in
    print_endline (Anvil.JsonOutput.json_output_to_string json_result);
    exit 1
  end else if config.ast_output then
    compile_with_ast_output config
  else begin
    let temp_file = Filename.temp_file "anvil_output" ".sv" in
    try
      let temp_out = open_out temp_file in
      (try
        Anvil.CompileDriver.compile temp_out config;
        close_out temp_out;
        let output_content = In_channel.with_open_text temp_file In_channel.input_all in
        let json_result = Anvil.JsonOutput.success_output output_content in
        print_endline (Anvil.JsonOutput.json_output_to_string json_result)
      with
        | exn ->
          close_out_noerr temp_out;
          raise exn
      );
      Sys.remove temp_file
    with
    | Anvil.CompileHelpers.CompileError msg ->
      (try Sys.remove temp_file with _ -> ());
      let json_errors = Anvil.JsonOutput.error_message_to_json_errors "error" msg in
      let json_result = Anvil.JsonOutput.failure_output json_errors in
      print_endline (Anvil.JsonOutput.json_output_to_string json_result)
  end

let compile_with_normal_output config =
  let open Anvil.Config in
  if config.input_filenames = [] && not config.stdin then begin
    Anvil.CliOutput.error "A file name must be supplied";
    exit 1
  end else begin
    let out_channel = match config.output_filename with
      | Some filename -> open_out (Printf.sprintf "%s.anvil.sv" filename)
      | None -> stdout
    in
    try
      Anvil.CompileDriver.compile out_channel config;
      if Option.is_some config.output_filename then
        close_out out_channel
    with
    |  Anvil.CompileHelpers.CompileError msg ->
      if Option.is_some config.output_filename then
        close_out_noerr out_channel;
      let open Anvil.Lang in
      Anvil.CliOutput.error "Compilation failed";
      let open Anvil.Except in
      List.iter (
        function
        | Text msg_text -> Printf.eprintf "%s\n" msg_text
        | Codespan (_, span) -> (
          let file_name = span.st.pos_fname in
          if file_name <> "" then (
            Printf.eprintf "%s:%d:%d:\n" file_name span.st.pos_lnum (span.st.pos_cnum - span.st.pos_bol + 1);
            Anvil.SpanPrinter.print_code_span ~indent:2 ~trunc:(-5) stderr span
          )
        )
      ) msg;
      exit 1
  end

let () =
  let config = Anvil.Config.parse_args() in
  if config.json_output then
    compile_with_json_output config
  else
    compile_with_normal_output config
