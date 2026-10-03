type combo_verdict = {
  picked : bool;
  from_state : string;
  action : string;
  next_state : string;
  step1_ok : bool;
  use_env : bool;
  clock_ok : bool;
  clock_count : int;
  component_count : int;
  sync_ok : bool;
  changed : bool;
  keep : bool;
  combined_msgs : string;
  component_lines : string list;
  guard_lines : string list;
}

let env_flag_enabled name =
  match Sys.getenv_opt name with
  | None | Some "" | Some "0" | Some "false" | Some "False" | Some "FALSE" ->
      false
  | Some _ -> true

let enabled ~verbose = verbose || env_flag_enabled "DEBUG"

let format_env ~imm ~future ~clock =
  Printf.sprintf "Imm={%s}; F={%s}; clock=%b" imm future clock

let status picked = if picked then "PICKED" else "REJECTED"

let check_status ok = if ok then "ok" else "fail"

let component_pick_line ~component ~from_state ~action ~offers ~maybe_offers
    ~guard ~env ~to_state =
  String.concat "\n"
    [
      Printf.sprintf "    - %s:s%d -> s%d" component from_state to_state;
      Printf.sprintf "        action : %s" action;
      Printf.sprintf "        O      : {%s}" offers;
      Printf.sprintf "        MO     : {%s}" maybe_offers;
      Printf.sprintf "        G      : %s" guard;
      Printf.sprintf "        E      : %s" env;
    ]

let guard_check_line ~component ~state_id ~ok ~guard ~env =
  String.concat "\n"
    [
      Printf.sprintf "    - %s:s%d  %s" component state_id (check_status ok);
      Printf.sprintf "        G_proj : %s" guard;
      Printf.sprintf "        E      : %s" env;
    ]

let print_combo_verdict ~verbose:_ verdict =
    DebugLog.text "product" "combos.log" @@ Printf.sprintf "%s\n\n"
      (String.concat "\n"
         ([
            "------------------------------------------------------------";
            Printf.sprintf "Product combo: %s" (status verdict.picked);
            Printf.sprintf "  from   : [%s]" verdict.from_state;
            Printf.sprintf "  action : %s" verdict.action;
            Printf.sprintf "  to     : [%s]" verdict.next_state;
            "";
            "  checks:";
            Printf.sprintf
              "    step1        : %-5s  use_env=%b"
              (check_status verdict.step1_ok) verdict.use_env;
            Printf.sprintf
              "    clock        : %-5s  selected=%d/%d"
              (check_status verdict.clock_ok) verdict.clock_count
              verdict.component_count;
            Printf.sprintf "    sync         : %-5s"
              (check_status verdict.sync_ok);
            Printf.sprintf "    changed      : %b" verdict.changed;
            Printf.sprintf "    keep         : %b" verdict.keep;
            Printf.sprintf "    combined_msg : {%s}" verdict.combined_msgs;
            "";
            "  component transitions:";
          ]
         @ verdict.component_lines
         @ [
             "";
             "  projected guard checks:";
           ]
         @ verdict.guard_lines
         @ [ "------------------------------------------------------------" ]))
