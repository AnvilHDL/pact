(** Generate global states for a process. *)
val codegen_proc_states :
    CodegenPrinter.t ->
    EventGraph.proc_graph -> unit

(** Emit one clocked block for registers shared by multiple writing threads. *)
val codegen_shared_reg_transitions :
    CodegenPrinter.t ->
    EventGraph.proc_graph -> Utils.StringSet.t

(** Generate and print out code for states in a given design ({!EventGraph.event_graph}). *)
val codegen_states :
    Utils.StringSet.t ->
    CodegenPrinter.t ->
    Config.compile_config ->
    EventGraph.event_graph_collection ->
    EventGraph.proc_graph ->
    EventGraph.event_graph ->
    Lang.message_specifier option -> unit
