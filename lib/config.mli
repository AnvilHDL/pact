(** This module provides handling and parsing of configurations. *)

(** Set of configurations that control the compilation process. *)
type compile_config = {
  debug_mode : bool; (** enable debug mode for testing*)
  debug_choice : int; (** debug choice for testing *)
  verbose : bool; (** output verbose details related to compilation to stderr *)
  silent : bool; (** write compatibility traces to files, retaining concise stderr results *)
  verbose_max : bool; (** output verbose details related to compilation to stderr *)
  stdin : bool; (** read from standard input *)
  disable_lt_checks : bool; (** disable all lifetime and borrow related checks *)
  disable_session_checks : bool; (** disable all session type related checks *)
  disable_compat_checks : bool; (** disable all compatibility checks *)
  weak_typecasts : bool; (** allow weak typecasts
                             between data types of different widths *)
  opt_level : int; (** optimisation level *)
  merge_reg_writes : bool; (** merge each multi-writer register into one always_comb next-state signal instead of per-event non-blocking assigns; off by default *)
  output_filename : string option; (** optional output filename *)

  just_check : bool; (** only typecheck and validate the input files without generating output *)
  two_round_graph: bool; (** enable codegen of two rounds for each thread
                             NOTE: with general recursive graphs, this may not be
                             literally two rounds *)

  json_output : bool; (** output compilation results in JSON format *)
  input_filenames : string list; (** list of file names to be compiled *)
}

(** Parse the process arguments for a set of configurations. *)
val parse_args : unit -> compile_config

val debug_println : compile_config -> string -> unit
