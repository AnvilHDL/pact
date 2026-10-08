type compile_config = {
  debug_mode : bool;
  debug_choice : int;
  verbose: bool;
  silent : bool;
  verbose_max : bool;
  stdin: bool;
  disable_lt_checks : bool;
  disable_session_checks : bool;
  infer : bool;
  disable_compat_checks : bool;
  weak_typecasts : bool;
  opt_level : int;
  merge_reg_writes : bool;
  output_filename : string option;
  log_dir : string option; (* where debug logs go; None disables them *)
  just_check : bool;
  two_round_graph: bool;
  json_output: bool;
  ast_output: bool;
  input_filenames: string list;
}

let parse_args () : compile_config =
  let verbose = ref false in
  let silent = ref false in
  let verbose_max = ref false in
  let disable_compat_checks = ref false in
  let disable_lt_checks = ref false in
  let disable_session_checks = ref false in
  let infer = ref false in
  let strong_typecasts = ref false in
  let opt_level = ref 2 in
  let merge_reg_writes = ref false in
  let debug_choice = ref (-1) in
  let stdin = ref false in
  let two_round_graph = ref false in
  let json_output = ref false in
  let ast_output = ref false in
  let input_filenames = ref []
  and log_dir = ref None
  and output_filename = ref None
  and just_check = ref false in

  let add_input_filename s =
    input_filenames := s::!input_filenames
  in
  Arg.parse
    [
      ("-stdin", Arg.Set stdin, "Read from standard input. If a filename is provided despite this flag, it is treated as the path of standard input data.");
      ("-verbose", Arg.Set verbose, "Show progress and write debug logs to ./logs/<input>/");
      ("-log-dir", Arg.String (fun s -> log_dir := Some s), "Write debug logs to the given directory");
      ("-silent", Arg.Set silent, "Write compatibility traces to the log directory; keep concise results on stderr");
      ("-disable-lt-checks", Arg.Set disable_lt_checks, "Disable lifetime/borrow-related checks");
      ("-strict-dtc", Arg.Set strong_typecasts, "Restrict Abstract Typecasts");
      ("-disable-session-checks", Arg.Set disable_session_checks, "Disable session type related checks");
      ("-infer", Arg.Set infer, "Check compatibility with the types inferred from the spawned processes");
      ("-disable-compat-checks", Arg.Set disable_compat_checks, "Disable compatibility checks");
      ("-debug-choice", Arg.Set_int debug_choice, "Debug mode: 0/2 fast compatibility, 1 profiling, 3 simultaneous compatibility, 4 sequential compatibility, 5/6/7 as 2/3/4 with types inferred from processes");
      ("-O", Arg.Set_int opt_level, "Set optimisation level: 0, 1, 2 (default), 3");
      ("-j", Arg.Set_int WorkerPool.jobs, "Domains used to build compatibility products (default 1)");
      ("-merge-reg-writes", Arg.Set merge_reg_writes, "Merge multi-writer registers into one always_comb next-state signal instead of one guarded non-blocking assign per writer event (behaviour-preserving; off by default, see Config.mli)");
      ("-o", Arg.String (fun s -> output_filename := Some s), "Set output filename");
      ("-just-check", Arg.Set just_check, "Only typecheck and validate the input files");
      ("-two-round", Arg.Set two_round_graph, "Enable codegen of logic for two rounds");
      ("-json", Arg.Set json_output, "Output compilation results in JSON format");
      ("-ast", Arg.Set ast_output, "With -json, check the input and include its AST instead of generating code");
      ("-verbose-max", Arg.Set verbose_max, "Enable verbose output with maximum detail");
    ]
    add_input_filename
    "pact [-stdin] [-verbose] [-log-dir <dir>] [-silent] [-disable-lt-checks] [-O <opt-level>] [-two-round] [-json] [-strict-dtc] <file1> [<file2>] ...";
  {
    debug_mode = (!debug_choice <> -1);
    verbose = !verbose;
    silent = !silent;
    debug_choice = !debug_choice;
    verbose_max = !verbose_max;
    stdin = !stdin;
    disable_lt_checks = !disable_lt_checks;
    disable_session_checks = !disable_session_checks;
    infer = !infer;
    disable_compat_checks = !disable_compat_checks;
    weak_typecasts = not !strong_typecasts;
    opt_level = !opt_level;
    merge_reg_writes = !merge_reg_writes;
    two_round_graph = !two_round_graph;
    json_output = !json_output;
    ast_output = !ast_output;
    input_filenames = !input_filenames;
    output_filename = !output_filename;
    log_dir =
      (match !log_dir, List.rev !input_filenames with
       | Some d, _ -> Some d
       | None, _ when not (!verbose || !verbose_max || !silent) -> None
       | None, first :: _ ->
         Some (Filename.concat "logs"
                 (Filename.remove_extension (Filename.basename first)))
       | None, [] -> Some (Filename.concat "logs" "stdin"));
    just_check = !just_check;
  }


let debug_println (_config : compile_config) (msg : string) =
  DebugLog.line "lifetime" "sync_modes.log" "%s" msg
