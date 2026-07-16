(* Translate every Rust source file in a directory to Isabelle.

   This runner deliberately does not use [Input.build]: per-test directives such
   as [//@ [lean] skip] and [//@ aeneas-args=...] are therefore ignored. *)

type command_status = Success | Failure
type input_kind = Single_file of string | Crate of string
type input = { name : string; kind : input_kind }

let blue = "\x1b[34m[isabelle_runner]\x1b[0m"
let green = "\x1b[32m[isabelle_runner]\x1b[0m"
let yellow = "\x1b[33m[isabelle_runner]\x1b[0m"
let command_to_string args = String.concat " " (List.map Filename.quote args)

let run_command args =
  let command = command_to_string args in
  print_endline (blue ^ " Running: " ^ command);
  let argv = Array.of_list args in
  let pid =
    Unix.create_process argv.(0) argv Unix.stdin Unix.stdout Unix.stderr
  in
  match snd (Unix.waitpid [] pid) with
  | Unix.WEXITED 0 -> Success
  | Unix.WEXITED code ->
      prerr_endline
        (yellow ^ " Command exited with code " ^ string_of_int code ^ ": "
       ^ command);
      Failure
  | Unix.WSIGNALED signal ->
      prerr_endline
        (yellow ^ " Command was killed by signal " ^ string_of_int signal ^ ": "
       ^ command);
      Failure
  | Unix.WSTOPPED signal ->
      prerr_endline
        (yellow ^ " Command was stopped by signal " ^ string_of_int signal
       ^ ": " ^ command);
      Failure

let ensure_directory path =
  if Sys.file_exists path then (
    if not (Sys.is_directory path) then
      failwith ("`" ^ path ^ "` exists but is not a directory"))
  else Unix.mkdir path 0o755

let normalize_crate_name name =
  String.map
    (function
      | '-' -> '_'
      | character -> character)
    name

let inputs input_dir =
  Sys.readdir input_dir |> Array.to_list |> List.sort String.compare
  |> List.filter_map (fun entry ->
         let path = Filename.concat input_dir entry in
         if (not (Sys.is_directory path)) && Filename.check_suffix entry ".rs"
         then
           Some
             {
               name = normalize_crate_name (Filename.remove_extension entry);
               kind = Single_file path;
             }
         else if
           Sys.is_directory path
           && Sys.file_exists (Filename.concat path "Cargo.toml")
         then Some { name = normalize_crate_name entry; kind = Crate path }
         else None)

let run_charon charon_path llbc input =
  match input.kind with
  | Single_file source ->
      run_command
        [
          charon_path;
          "rustc";
          "--dest-file";
          llbc;
          "--preset=aeneas";
          "--";
          source;
          "--crate-name=" ^ input.name;
          "--crate-type=rlib";
          "--allow=unused";
          "--allow=non_snake_case";
          "--edition=2021";
        ]
  | Crate path ->
      let previous_directory = Unix.getcwd () in
      Fun.protect
        ~finally:(fun () -> Unix.chdir previous_directory)
        (fun () ->
          Unix.chdir path;
          run_command
            [
              charon_path;
              "cargo";
              "--preset=aeneas";
              "--rustc-arg=--allow=unused";
              "--dest-file";
              llbc;
            ])

let translate_file charon_path aeneas_path llbc_dir dest_dir aeneas_options
    input =
  let source =
    match input.kind with
    | Single_file path | Crate path -> path
  in
  let llbc = Filename.concat llbc_dir (input.name ^ ".llbc") in
  print_endline ("\n" ^ blue ^ " Translating " ^ source);
  match run_charon charon_path llbc input with
  | Failure -> `Charon_failure
  | Success -> (
      let aeneas_args =
        [ aeneas_path; llbc; "-dest"; dest_dir; "-backend"; "isabelle" ]
        @ aeneas_options
        @ [
            "-print-error-emitters";
            "-no-progress-bar";
            "-checks";
            "-color";
            "-sequential";
          ]
      in
      match run_command aeneas_args with
      | Success -> `Translated
      | Failure -> `Partial)

let () =
  match Array.to_list Sys.argv with
  | _ :: charon_path :: aeneas_path :: llbc_dir :: input_dir :: dest_dir
    :: aeneas_options ->
      ensure_directory llbc_dir;
      ensure_directory dest_dir;
      let charon_path = Unix.realpath charon_path in
      let aeneas_path = Unix.realpath aeneas_path in
      let llbc_dir = Unix.realpath llbc_dir in
      let inputs = inputs input_dir in
      let translated = ref 0 in
      let partial = ref 0 in
      let charon_failures = ref 0 in
      List.iter
        (fun input ->
          match
            translate_file charon_path aeneas_path llbc_dir dest_dir
              aeneas_options input
          with
          | `Translated -> incr translated
          | `Partial -> incr partial
          | `Charon_failure -> incr charon_failures)
        inputs;
      print_endline
        ("\n" ^ green ^ " Finished "
        ^ string_of_int (List.length inputs)
        ^ " Rust inputs: " ^ string_of_int !translated ^ " translated, "
        ^ string_of_int !partial ^ " partial, "
        ^ string_of_int !charon_failures
        ^ " Charon failures")
  | _ ->
      prerr_endline
        "Usage: run_isabelle CHARON AENEAS LLBC_DIR INPUT_DIR DEST_DIR \
         [AENEAS_OPTION ...]";
      exit 2
