let styled out code text =
  let color = Unix.isatty (Unix.descr_of_out_channel out)
    && Sys.getenv_opt "NO_COLOR" = None
    && Sys.getenv_opt "TERM" <> Some "dumb" in
  if color then "\027[" ^ code ^ "m" ^ text ^ "\027[0m" else text

let section title =
  Printf.eprintf "\n%s\n" (styled stderr "1;36" title)

let info fmt =
  Printf.ksprintf (fun message ->
    Printf.eprintf "%s %s\n%!" (styled stderr "36" "[info]") message) fmt

(* Set by -verbose; status lines are shown only then. *)
let verbose = ref false

let status fmt =
  Printf.ksprintf (fun message ->
    if !verbose then
      Printf.eprintf "%s %s\n%!" (styled stderr "36" "[info]") message) fmt

let warning fmt =
  Printf.ksprintf (fun message ->
    Printf.eprintf "%s %s\n%!" (styled stderr "1;33" "[warning]") message) fmt

let error fmt =
  Printf.ksprintf (fun message ->
    Printf.eprintf "%s %s\n%!" (styled stderr "1;31" "[error]") message) fmt

let counts out kind name states transitions =
  Printf.fprintf out "  %s: %d states, %d transitions\n%!"
    (styled out "36" (kind ^ " " ^ name)) states transitions

let compatibility ?mode pool result message =
  let code, label = match result with
    | "true" -> "1;32", "PASS"
    | "false" -> "1;31", "FAIL"
    | _ -> "1;33", "ERROR" in
  let mode = match mode with None -> "" | Some name -> "[" ^ name ^ "] " in
  let headline = Printf.sprintf "[%s] %sPool %s Compatibility: %s"
    label mode pool result in
  Printf.eprintf "%s\n  %s\n%!" (styled stderr code headline) message
