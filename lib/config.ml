type compile_config = {
  debug_mode : bool;
  debug_choice : int;
  verbose: bool;
  verbose_max : bool;
  stdin: bool;
  disable_lt_checks : bool;
  disable_session_checks : bool;
  disable_compat_checks : bool;
  weak_typecasts : bool;
  opt_level : int;
  output_filename : string option;
  just_check : bool;
  two_round_graph: bool;
  json_output: bool;
  input_filenames: string list;
}

let parse_args () : compile_config =
  let verbose = ref false in
  let verbose_max = ref false in
  let disable_compat_checks = ref false in
  let disable_lt_checks = ref false in
  let disable_session_checks = ref false in
  let strong_typecasts = ref false in
  let opt_level = ref 2 in
  let debug_choice = ref (-1) in
  let stdin = ref false in
  let two_round_graph = ref false in
  let json_output = ref false in
  let input_filenames = ref []
  and output_filename = ref None
  and just_check = ref false in

  let add_input_filename s =
    input_filenames := s::!input_filenames
  in
  Arg.parse
    [
      ("-stdin", Arg.Set stdin, "Read from standard input. If a filename is provided despite this flag, it is treated as the path of standard input data.");
      ("-verbose", Arg.Set verbose, "Enable verbose output");
      ("-disable-lt-checks", Arg.Set disable_lt_checks, "Disable lifetime/borrow-related checks");
      ("-strict-dtc", Arg.Set strong_typecasts, "Restrict Abstract Typecasts");
      ("-disable-session-checks", Arg.Set disable_session_checks, "Disable session type related checks");
      ("-disable-compat-checks", Arg.Set disable_compat_checks, "Disable compatibility checks");
      ("-debug-choice", Arg.Set_int debug_choice, "Set debug choice for testing");
      ("-O", Arg.Set_int opt_level, "Set optimisation level: 0, 1, 2 (default)");
      ("-o", Arg.String (fun s -> output_filename := Some s), "Set output filename");
      ("-just-check", Arg.Set just_check, "Only typecheck and validate the input files");
      ("-two-round", Arg.Set two_round_graph, "Enable codegen of logic for two rounds");
      ("-json", Arg.Set json_output, "Output compilation results in JSON format");
      ("-verbose-max", Arg.Set verbose_max, "Enable verbose output with maximum detail");
    ]
    add_input_filename
    "anvil [-stdin] [-verbose] [-disable-lt-checks] [-O <opt-level>] [-two-round] [-json] [-strict-dtc] <file1> [<file2>] ...";
  {
    debug_mode = (!debug_choice <> -1);
    verbose = !verbose;
    debug_choice = !debug_choice;
    verbose_max = !verbose_max;
    stdin = !stdin;
    disable_lt_checks = !disable_lt_checks;
    disable_session_checks = !disable_session_checks;
    disable_compat_checks = !disable_compat_checks;
    weak_typecasts = not !strong_typecasts;
    opt_level = !opt_level;
    two_round_graph = !two_round_graph;
    json_output = !json_output;
    input_filenames = !input_filenames;
    output_filename = !output_filename;
    just_check = !just_check;
  }


let debug_println (config : compile_config) (msg : string) =
  if config.verbose then
    Printf.eprintf "%s\n" msg
  else ()
