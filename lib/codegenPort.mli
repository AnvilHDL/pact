(** Codegen related to ports. *)

(** A port to be generated. *)
type t = {
  dir : Lang.message_direction;
  dtype : Lang.data_type;
  name : string;
}

(** Check if a message has a [valid] port. *)
val message_has_valid_port : Lang.message_def -> bool

(** Check if a message has an [ack] port under its resolved handshake mode. *)
val message_has_ack_port : ?mode:Lang.handshake_modes -> Lang.message_def -> bool

(** Check if a message has a [ready] port under its resolved handshake mode. *)
val message_has_ready_port : ?mode:Lang.handshake_modes -> Lang.message_def -> bool

(** Which reverse-direction signal a use site drives or waits on. *)
type reverse_signal = UsesAck | UsesReady

(** The reverse signal under the resolved mode, or [None] if there is none. *)
val site_reverse_signal : ?mode:Lang.handshake_modes -> Lang.message_def -> reverse_signal option

(** Whether a use site waits for its peer. Instantaneous sites never do. *)
val site_blocks : ?mode:Lang.handshake_modes -> Lang.message_def -> Lang.handshake_kind -> bool

(** Resolved handshake mode per (endpoint, message) within one process. *)
type resolver = Lang.identifier -> Lang.identifier -> Lang.handshake_modes

(** Resolver used when no resolution has been computed: everything valid/ack. *)
val default_resolver : resolver

(** Produce a list of all ports to be generated for a given end point. *)
val message_has_data_port : Lang.message_def -> int -> bool

(** Produce a list of all ports to be generated for a list of end points. *)
val gather_ports :
  ?resolve:resolver -> Lang.channel_class_def list -> Lang.endpoint_def list -> t list

(** Clock port. *)
val clk : t

(** Reset port. *)
val rst : t

(** Format the definition of a port. This involves translating the
    type and direction into their equivalents in Verilog. *)
val format : TypedefMap.t -> Lang.macro_def list -> t -> string
