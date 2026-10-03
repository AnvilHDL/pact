(* Debug logs for one compiler run, kept under a single directory with one
   subdirectory per kind of log. Nothing is written unless logging is enabled. *)

let root : string option ref = ref None

(* Open channels, so a log written piecemeal is truncated once per run. *)
let channels : (string, out_channel) Hashtbl.t = Hashtbl.create 16

(* Marks a directory as created by this module, so it is safe to clear. *)
let marker = ".logs"

let rec mkdir_p path =
  if path <> "" && path <> "." && path <> Filename.dir_sep
     && not (Sys.file_exists path) then begin
    mkdir_p (Filename.dirname path);
    try Sys.mkdir path 0o755 with Sys_error _ when Sys.file_exists path -> ()
  end

let rec remove_tree path =
  if Sys.file_exists path then
    if Sys.is_directory path then begin
      Array.iter (fun f -> remove_tree (Filename.concat path f)) (Sys.readdir path);
      Sys.rmdir path
    end else Sys.remove path

let close_all () =
  Hashtbl.iter (fun _ oc -> close_out_noerr oc) channels;
  Hashtbl.reset channels

(* Start logging into [dir], clearing logs left by a previous run. *)
let enable dir =
  if Sys.file_exists (Filename.concat dir marker) then remove_tree dir;
  mkdir_p dir;
  Out_channel.with_open_text (Filename.concat dir marker) (fun _ -> ());
  root := Some dir;
  at_exit close_all

let enabled () = Option.is_some !root

let sanitize name =
  String.map (function
    | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.') as c -> c
    | _ -> '_') name

let path_of category name =
  Option.map (fun dir ->
    let d = Filename.concat dir category in
    mkdir_p d;
    Filename.concat d (sanitize name)) !root

let channel category name =
  Option.map (fun p ->
    match Hashtbl.find_opt channels p with
    | Some oc -> oc
    | None ->
      let oc = open_out p in
      Hashtbl.replace channels p oc;
      oc) (path_of category name)

(* Write [category/name] through [f], replacing any earlier content this run. *)
let file category name (f : out_channel -> unit) =
  Option.iter (fun p ->
    (match Hashtbl.find_opt channels p with
     | Some oc -> close_out_noerr oc; Hashtbl.remove channels p
     | None -> ());
    Out_channel.with_open_text p f) (path_of category name)

(* Append a formatted line to [category/name]. *)
let line category name fmt =
  Printf.ksprintf (fun s ->
    Option.iter (fun oc -> output_string oc s; output_char oc '\n')
      (channel category name)) fmt

(* Append raw text to [category/name]. *)
let text category name s =
  Option.iter (fun oc -> output_string oc s) (channel category name)

(* Path a log would be written to, for messages that point the user at it. *)
let path category name = path_of category name

let report () =
  match !root with
  | Some dir when Sys.file_exists dir ->
    close_all ();
    let rec count d =
      Array.fold_left (fun acc f ->
        let p = Filename.concat d f in
        if Sys.is_directory p then acc + count p
        else if f = marker then acc else acc + 1) 0 (Sys.readdir d)
    in
    CliOutput.info "Logs: %s (%d files)" dir (count dir)
  | _ -> ()
