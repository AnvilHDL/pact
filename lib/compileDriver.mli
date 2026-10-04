(** Driver that controls the overall compilation process, handling things include file importing. *)

(** Parses the input files and their imports; [recover] receives non-syntax errors instead of raising. *)
val parse : ?recover:(Except.error_message -> unit) -> Config.compile_config -> (string * Lang.compilation_unit) list

(** Checks the parsed units and, unless [just_check], generates code. *)
val compile_units : out_channel -> Config.compile_config -> (string * Lang.compilation_unit) list -> unit

(** Parses, checks and generates code for the input files. *)
val compile : out_channel -> Config.compile_config -> unit
