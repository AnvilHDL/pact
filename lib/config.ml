type compile_config = {
  debug_mode : bool;
  debug_choice : int;
  verbose: bool;
  verbose_max : bool;
  disable_lt_checks : bool;
  disable_session_checks : bool;
  disable_compat_checks : bool;
  weak_typecasts : bool;
  opt_level : int;
  two_round_graph: bool;
  input_filenames: string list;
}

let parse_args () : compile_config =
  let verbose = ref false in
  let verbose_max = ref false in
  let disable_compat_checks = ref false in
  let disable_lt_checks = ref false in
  let disable_session_checks = ref false in
  let weak_typecasts = ref false in
  let opt_level = ref 2 in
  let debug_choice = ref (-1) in
  let two_round_graph = ref false in
  let input_filenames = ref [] in
  let add_input_filename s =
    input_filenames := s::!input_filenames
  in
  Arg.parse
    [
      ("-verbose", Arg.Set verbose, "Enable verbose output");
      ("-verbose-max", Arg.Set verbose_max, "Enable verbose output with maximum detail");
      ("-disable-lt-checks", Arg.Set disable_lt_checks, "Disable lifetime/borrow-related checks");
      ("-disable-session-checks", Arg.Set disable_session_checks, "Disable session type checks");
      ("-disable-compat-checks", Arg.Set disable_compat_checks, "Disable compatibility checks");
      ("-weak-typecasts", Arg.Set weak_typecasts, "Allow Typecasts");
      ("-O", Arg.Set_int opt_level, "Set optimisation level: 0, 1, 2 (default)");
      ("-two-round", Arg.Set two_round_graph, "Enable codegen of logic for two rounds");
      ("-debug", (Arg.Set_int debug_choice), "Enable debug mode for testing")
    ]
    add_input_filename
    "anvil [-verbose] [-disable-lt-checks] [-O <opt-level>] [-debug <debug-choice>] [-two-round] <file1> [<file2>] ...";
  {
    debug_mode = (!debug_choice <> -1);
    verbose = !verbose;
    debug_choice = !debug_choice;
    verbose_max = !verbose_max;
    disable_lt_checks = !disable_lt_checks;
    disable_session_checks = !disable_session_checks;
    disable_compat_checks = !disable_compat_checks;
    weak_typecasts = !weak_typecasts;
    opt_level = !opt_level;
    two_round_graph = !two_round_graph;
    input_filenames = !input_filenames;
  }


let debug_println (config : compile_config) (msg : string) =
  if config.verbose then
    Printf.eprintf "%s\n" msg
  else ()
