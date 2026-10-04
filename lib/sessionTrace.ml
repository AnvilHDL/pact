(** Records where each expression starts and completes in the event graphs, to report session states (off unless [enabled]). *)

open EventGraph

let enabled = ref false

let spans : (Lang.code_span, event * event) Hashtbl.t = Hashtbl.create 256

(* only session-checked graphs carry session states *)
let checked_graphs : event_graph list ref = ref []

(** Records that the expression at [span] starts at [start_ev] and completes at [end_ev]. *)
let record (span : Lang.code_span) (start_ev : event) (end_ev : event) =
  if !enabled && span <> Lang.code_span_dummy then
    Hashtbl.add spans span (start_ev, end_ev)

(** Records that the session check has assigned session states to the events of [g]. *)
let mark_checked (g : event_graph) =
  if !enabled then checked_graphs := g :: !checked_graphs

(** Start and completion events of the expression at [span] in a session-checked graph. *)
let find (span : Lang.code_span) : (event * event) option =
  Hashtbl.find_all spans span
  |> List.rev
  |> List.find_opt (fun ((ev, _) : event * event) -> List.exists (( == ) ev.graph) !checked_graphs)
