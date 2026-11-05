(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Commandline
open Clflags
open CommonOptions
open Timing
open Driveraux
open Frontend
open Assembler
open Linker
open Diagnostics

(* Name used for version string etc. *)
let tool_name = "C verified compiler"

(* Optional sdump suffix *)
let sdump_suffix = ref ".json"

let nolink () =
  !option_c || !option_S || !option_E || !option_interp

let object_filename sourcename =
  if nolink () then
    output_filename ~final: !option_c sourcename ~suffix:".o"
  else
    tmp_file ".o"

(* From CompCert C AST to asm *)

let compile_c_file sourcename ifile ofile =
  (* Prepare to dump Clight, RTL, etc, if requested *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename sourcename ~suffix:ext)
      else None in
  set_dest Cprint.destination option_dparse ".parsed.c";
  set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  set_dest AsmToJSON.destination option_sdump !sdump_suffix;
  (* Parse the ast *)
  let csyntax = parse_c_file sourcename ifile in
  (* Convert to Asm *)
  let asm =
    match Compiler.apply_partial
               (Compiler.transf_c_program csyntax)
               Asmexpand.expand_program with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
      let loc = file_loc sourcename in
        fatal_error loc "%a"  print_error msg in
  (* Dump Asm in binary and JSON format *)
  AsmToJSON.print_if asm sourcename;
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc

(* From C source to asm *)

let compile_i_file sourcename preproname =
  if !option_interp then begin
    Machine.config := Machine.compcert_interpreter !Machine.config;
    let csyntax = parse_c_file sourcename preproname in
    Interp.execute csyntax;
        ""
  end else if !option_S then begin
    compile_c_file sourcename preproname
      (output_filename ~final:true sourcename ~suffix:".s");
    ""
  end else begin
    let asmname =
      if !option_dasm
      then output_filename sourcename ~suffix:".s"
      else tmp_file ".s" in
    compile_c_file sourcename preproname asmname;
    let objname = object_filename sourcename  in
    assemble asmname objname;
    objname
  end

(* Processing of a .c file *)

let process_c_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = if !option_dprepro then
      output_filename sourcename ~suffix:".i"
    else
      tmp_file ".i" in
    preprocess sourcename preproname;
    compile_i_file sourcename preproname
  end

(* Processing of a .i / .p file (preprocessed C) *)

let process_i_file sourcename =
  ensure_inputfile_exists sourcename;
  compile_i_file sourcename sourcename

(* Processing of .S and .s files *)

let process_s_file sourcename =
  ensure_inputfile_exists sourcename;
  let objname = object_filename sourcename in
  assemble sourcename objname;
  objname

let process_S_file sourcename =
  ensure_inputfile_exists sourcename;
  if !option_E then begin
    preprocess sourcename (output_filename_default "-");
    ""
  end else begin
    let preproname = tmp_file ".s" in
    preprocess sourcename preproname;
    let objname = object_filename sourcename in
    assemble preproname objname;
    objname
  end

(* Processing of .h files *)

let process_h_file sourcename =
  if !option_E then begin
    ensure_inputfile_exists sourcename;
    preprocess sourcename (output_filename_default "-");
    ""
  end else
    fatal_error no_loc "input file %s ignored (not in -E mode)\n" sourcename

let target_help =
  if Configuration.arch = "arm" && Configuration.model <> "armv6" then
{|Target processor options:
  -mthumb        Use Thumb2 instruction encoding
  -marm          Use classic ARM instruction encoding
|}
else
  ""

let toolchain_help =
  if not Configuration.gnu_toolchain then begin
{|Toolchain options:
  -t tof:env     Select target processor for the diab toolchain
|} end else
    ""

let usage_string =
  version_string tool_name ^
  {|Usage: ccomp [options] <source files>
Recognized source files:
  .c             C source file
  .i or .p       C source file that should not be preprocessed
  .s             Assembly file
  .S or .sx      Assembly file that must be preprocessed
  .o             Object file
  .a             Library file
Processing options:
  -c             Compile to object file only (no linking), result in <file>.o
  -E             Preprocess only, send result to standard output
  -S             Compile to assembler only, save result in <file>.s
  -o <file>      Generate output in <file>
|} ^
  prepro_help ^
  language_support_help ^
 DebugInit.debugging_help ^
{|Optimization options: (use -fno-<opt> to turn off -f<opt>)
  -O             Optimize the compiled code [on by default]
  -O0            Do not optimize the compiled code
  -O1 -O2 -O3    Synonymous for -O
  -Os            Optimize for code size in preference to code speed
  -Obranchless   Optimize to generate fewer conditional branches; try to produce
                 branch-free instruction sequences as much as possible
  -ftailcalls    Optimize function calls in tail position [on]
  -fconst-prop   Perform global constant propagation  [on]
  -ffloat-const-prop <n>  Control constant propagation of floats
                   (<n>=0: none, <n>=1: limited, <n>=2: full; default is full)
  -fcse          Perform common subexpression elimination [on]
  -fredundancy   Perform redundancy elimination [on]
  -finline       Perform inlining of functions [on]
  -finline-functions-called-once Integrate functions only required by their
                 single caller [on]
  -fif-conversion Perform if-conversion (generation of conditional moves) [on]
Code generation options: (use -fno-<opt> to turn off -f<opt>)
  -fpic / -fPIC  Generate position-independent code [off]
  -fpie / -fPIE  Generate position-independent executables [on if supported]
  -ffpu          Use FP registers for some integer operations [on]
  -fsmall-data <n>  Set maximal size <n> for allocation in small data area
  -fsmall-const <n>  Set maximal size <n> for allocation in small constant area
  -falign-functions <n>  Set alignment (in bytes) of function entry points
  -falign-branch-targets <n>  Set alignment (in bytes) of branch targets
  -falign-cond-branches <n>  Set alignment (in bytes) of conditional branches
  -fcommon       Put uninitialized globals in the common section [on].
|} ^
 target_help ^
 toolchain_help ^
 assembler_help ^
 linker_help ^
{|Tracing options:
  -dprepro       Save C file after preprocessing in <file>.i
  -dparse        Save C file after parsing and elaboration in <file>.parsed.c
  -dc            Save generated Compcert C in <file>.compcert.c
  -dclight       Save generated Clight in <file>.light.c
  -dcminor       Save generated Cminor in <file>.cm
  -drtl          Save RTL at various optimization points in <file>.rtl.<n>
  -dltl          Save LTL after register allocation in <file>.ltl
  -dmach         Save generated Mach code in <file>.mach
  -dasm          Save generated assembly in <file>.s
  -dall          Save all generated intermediate files in <file>.<ext>
  -sdump         Save info for post-linking validation in <file>.json
|} ^
  general_help ^
  warning_help ^
  {|Interpreter mode:
  -interp        Execute given .c files using the reference interpreter
  -quiet         Suppress diagnostic messages for the interpreter
  -trace         Have the interpreter produce a detailed trace of reductions
  -random        Randomize execution order
  -all           Simulate all possible execution orders
  -main <name>   Start executing at function <name> instead of main()
|}

let print_usage_and_exit () =
  printf "%s" usage_string; exit 0

let dump_mnemonics destfile =
  let oc = open_out_bin destfile in
  let pp = Format.formatter_of_out_channel oc in
  AsmToJSON.pp_mnemonics pp;
  Format.pp_print_flush pp ();
  close_out oc;
  exit 0

let optimization_options = [
  option_ftailcalls; option_fifconversion; option_fconstprop; option_fcse;
  option_fredundancy; option_finline; option_finline_functions_called_once;
]

let set_all opts () = List.iter (fun r -> r := true) opts
let unset_all opts () = List.iter (fun r -> r := false) opts

let num_source_files = ref 0

let num_input_files = ref 0

let cmdline_actions =
  let f_opt name ref =
    [Exact("-f" ^ name), Set ref; Exact("-fno-" ^ name), Unset ref] in
  let check_align n =
    if n <= 0 || ((n land (n - 1)) <> 0) then
      error no_loc "requested alignment %d is not a power of 2" n
    in
  let set_pic_mode () =
    if Configuration.pic_supported
    then option_fpic := true
    else warning no_loc Unnamed
         "option -fpic not supported on this platform, ignored" in
  let set_pie_mode () =
    if Configuration.pic_supported
    then option_fpie := true
    else warning no_loc Unnamed
         "option -fpie not supported on this platform, ignored" in
  [
(* Getting help *)
  Exact "-help", Unit print_usage_and_exit;
  Exact "--help", Unit print_usage_and_exit;]
(* Getting version info *)
  @ version_options tool_name @
(* Enforcing CompCert build numbers for QSKs and mnemonics dump *)
  (if Version.buildnr <> "" then
     [Exact "-dump-mnemonics", String  dump_mnemonics;]
   else []) @
(* Processing options *)
 [ Exact "-c", Set option_c;
  Exact "-E", Set option_E;
  Exact "-S", Set option_S;
  Exact "-o", String(fun s -> option_o := Some s);
  Prefix "-o", Self (fun s -> let s = String.sub s 2 ((String.length s) - 2) in
                              option_o := Some s);]
  (* Preprocessing options *)
    @ prepro_actions @
  (* Language support options *)
    language_support_options
  (* Debugging options *)
    @ DebugInit.debugging_actions @
(* Code generation options -- more below *)
 [
  Exact "-O0", Unit (unset_all optimization_options);
  Exact "-O", Unit (set_all optimization_options);
  _Regexp "-O[123]$", Unit (set_all optimization_options);
  Exact "-Os", Set option_Osize;
  Exact "-Obranchless", Set option_Obranchless;
  Exact "-fsmall-data", Integer(fun n -> option_small_data := n);
  Exact "-fsmall-const", Integer(fun n -> option_small_const := n);
  Exact "-ffloat-const-prop", Integer(fun n -> option_ffloatconstprop := n); 
  Exact "-falign-functions", Integer(fun n -> check_align n; option_falignfunctions := Some n);
  Exact "-falign-branch-targets", Integer(fun n -> check_align n; option_falignbranchtargets := n);
  Exact "-falign-cond-branches", Integer(fun n -> check_align n; option_faligncondbranchs := n);
  Exact "-fpic", Unit set_pic_mode;
  Exact "-fPIC", Unit set_pic_mode;
  Exact "-fno-pic", Unset option_fpic;
  Exact "-fno-PIC", Unset option_fpic;
  Exact "-fpie", Unit set_pie_mode;
  Exact "-fPIE", Unit set_pie_mode;
  Exact "-fno-pie", Unset option_fpie;
  Exact "-fno-PIE", Unset option_fpie ] @
      f_opt "common" option_fcommon @
(* Target processor options *)
  (if Configuration.arch = "arm" then
    if Configuration.model = "armv6" then
      [ Exact "-marm", Ignore ] (* Thumb needs ARMv6T2 or ARMv7 *)
    else
      [ Exact "-mthumb", Set option_mthumb;
        Exact "-marm", Unset option_mthumb; ]
   else []) @
(* Toolchain options *)
    (if not Configuration.gnu_toolchain then
       [Exact "-t", String (fun arg -> push_linker_arg "-t"; push_linker_arg arg;
                             prepro_options := arg :: "-t" :: !prepro_options;
                             assembler_options := arg :: "-t" :: !assembler_options;)]
     else
       []) @
(* Assembling options *)
  assembler_actions @
(* Linking options *)
  linker_actions @
(* Tracing options *)
 [ Exact "-dprepro", Set option_dprepro;
  Exact "-dparse", Set option_dparse;
  Exact "-dc", Set option_dcmedium;
  Exact "-dclight", Set option_dclight;
  Exact "-dcminor", Set option_dcminor;
  Exact "-drtl", Set option_drtl;
  Exact "-dltl", Set option_dltl;
  Exact "-dalloctrace", Set option_dalloctrace;
  Exact "-dmach", Set option_dmach;
  Exact "-dasm", Set option_dasm;
  Exact "-dall", Self (fun _ ->
    option_dprepro := true;
    option_dparse := true;
    option_dcmedium := true;
    option_dclight := true;
    option_dcminor := true;
    option_drtl := true;
    option_dltl := true;
    option_dalloctrace := true;
    option_dmach := true;
    option_dasm := true);
  Exact "-sdump", Set option_sdump;
  Exact "-sdump-suffix", String (fun s -> option_sdump := true; sdump_suffix:= s);
  Exact "-sdump-folder", String (fun s -> AsmToJSON.sdump_folder := s);] @
(* General options *)
   general_options @
(* Diagnostic options *)
  warning_options @
(* Interpreter mode *)
 [ Exact "-interp", Set option_interp;
  Exact "-quiet", Unit (fun () -> Interp.trace := 0);
  Exact "-trace", Unit (fun () -> Interp.trace := 2);
  Exact "-random", Unit (fun () -> Interp.mode := Interp.Random);
  Exact "-all", Unit (fun () -> Interp.mode := Interp.All);
  Exact "-main", String (fun s -> main_function_name := s)
 ]
(* Optimization options *)
(* -f options: come in -f and -fno- variants *)
  @ f_opt "tailcalls" option_ftailcalls
  @ f_opt "if-conversion" option_fifconversion
  @ f_opt "const-prop" option_fconstprop
  @ f_opt "cse" option_fcse
  @ f_opt "redundancy" option_fredundancy
  @ f_opt "inline" option_finline
  @ f_opt "inline-functions-called-once" option_finline_functions_called_once
(* Code generation options *)
  @ f_opt "fpu" option_ffpu
  @ f_opt "sse" option_ffpu (* backward compatibility *)
  @ [
(* Catch options that are not handled *)
  Prefix "-", Self (fun s ->
      fatal_error no_loc "Unknown option `%s'" s);
(* File arguments *)
  Suffix ".c", Self (fun s ->
      push_action process_c_file s; incr num_source_files; incr num_input_files);
  Suffix ".i", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".p", Self (fun s ->
      push_action process_i_file s; incr num_source_files; incr num_input_files);
  Suffix ".s", Self (fun s ->
      push_action process_s_file s; incr num_source_files; incr num_input_files);
  Suffix ".S", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".sx", Self (fun s ->
      push_action process_S_file s; incr num_source_files; incr num_input_files);
  Suffix ".o", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".a", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .o.ext files and .so files are also object files *)
  _Regexp ".*\\.o\\.", Self (fun s -> push_linker_arg s; incr num_input_files);
  Suffix ".so", Self (fun s -> push_linker_arg s; incr num_input_files);
  (* GCC compatibility: .h files can be preprocessed with -E *)
  Suffix ".h", Self (fun s ->
      push_action process_h_file s; incr num_source_files; incr num_input_files);
  ]

(* Inspect the same syntax without running the actual option actions.
   Do not attempt an optimized compilation when it could consume or
   overwrite an input that a retry would need. *)
let compilation_plan () =
  let c_sources = ref [] and asm_sources = ref [] and inputs = ref [] in
  let compile = ref true and assembly = ref false and object_only = ref false in
  let output = ref None and depfile = ref None and dependencies = ref false in
  let dumps = ref [] and dump_rtl = ref false and dump_asm_json = ref false in
  let json_suffix = ref !sdump_suffix and json_dir = ref "" in
  let dump_suffixes =
    ["-dprepro", ".i"; "-dparse", ".parsed.c"; "-dc", ".compcert.c";
     "-dclight", ".light.c"; "-dcminor", ".cm"; "-dltl", ".ltl";
     "-dalloctrace", ".alloctrace"; "-dmach", ".mach"; "-dasm", ".s"] in
  let add_input path = inputs := path :: !inputs in
  let add_source sources path = add_input path; sources := path :: !sources in
  let inspect (pattern, action) =
    let action =
      match pattern, action with
      | Suffix (".c" | ".i" | ".p"), Self _ -> Self (add_source c_sources)
      | Suffix (".s" | ".S" | ".sx"), Self _ -> Self (add_source asm_sources)
      | Suffix (".o" | ".a" | ".so" | ".h"), Self _ -> Self add_input
      | Regexp _, Self _ ->
          Self (fun path -> if path.[0] <> '-' then add_input path)
      | Exact ("-include" | "-imacros" | "-T"), String _ -> String add_input
      | Exact ("-E" | "-M" | "-MM" | "-interp"), _ ->
          Unset compile
      | Exact "-S", _ -> Set assembly
      | Exact "-c", _ -> Set object_only
      | Exact "-o", _ -> String (fun path -> output := Some path)
      | Prefix "-o", _ ->
          Self (fun arg -> output := Some (String.sub arg 2 (String.length arg - 2)))
      | Exact ("-MD" | "-MMD"), _ -> Set dependencies
      | Exact "-MF", _ -> String (fun path -> depfile := Some path)
      | Exact "-dall", _ ->
          Unit (fun () -> dumps := List.map snd dump_suffixes; dump_rtl := true)
      | Exact "-drtl", _ -> Set dump_rtl
      | Exact "-sdump", _ -> Set dump_asm_json
      | Exact "-sdump-suffix", _ ->
          String (fun suffix -> dump_asm_json := true; json_suffix := suffix)
      | Exact "-sdump-folder", _ -> String (fun path -> json_dir := path)
      | Exact opt, _ when List.mem_assoc opt dump_suffixes ->
          Unit (fun () -> dumps := List.assoc opt dump_suffixes :: !dumps)
      | _, Self _ -> Self (fun _ -> ())
      | _, (String _ | Integer _ | Ignore) -> Ignore
      | _, (Set _ | Unset _ | Unit _) -> Unit (fun () -> ()) in
    pattern, action in
  try
    parse_cmdline (List.map inspect cmdline_actions);
    let stat path = try Some (Unix.stat path) with Unix.Unix_error _ -> None in
    let input_stats = List.filter_map stat !inputs in
    let aliases_input path =
      List.mem path !inputs ||
      match stat path with
      | None -> false
      | Some out ->
          List.exists (fun input ->
            input.Unix.st_dev = out.Unix.st_dev && input.Unix.st_ino = out.Unix.st_ino)
            input_stats in
    let trace_path = match Sys.getenv_opt "COMPCERT_EXPERIMENT_TRACE" with
      | Some path when path <> "" -> Some path
      | _ -> None in
    let trace_alias = match trace_path with Some path -> aliases_input path | None -> false in
    if not !compile || !c_sources = [] then (`Other, trace_alias) else
    let final default = Option.value !output ~default in
    let outputs =
      if !assembly || !object_only then
        List.map (fun path ->
          final (output_filename path ~suffix:(if !assembly then ".s" else ".o")))
          !c_sources @
        List.map (fun path ->
          let default = output_filename path ~suffix:".o" in
          if !object_only then final default else default) !asm_sources
      else [final "a.out"] in
    let dumps_for path =
      List.filter_map (fun suffix ->
        if suffix = ".i" && not (Filename.check_suffix path ".c") then None
        else Some (output_filename path ~suffix)) !dumps in
    let dependency_outputs =
      if not !dependencies then [] else
      match !depfile with
      | Some path -> [path]
      | None -> List.map (fun path -> output_filename path ~suffix:".d") !c_sources in
    let rtl_outputs () =
      if not !dump_rtl then [] else
      let prefixes = List.map (fun path -> output_filename path ~suffix:".rtl.") !c_sources in
      let is_dump path prefix =
        let length = String.length prefix in
        let suffix_length = String.length path - length in
        suffix_length > 0 && String.sub path 0 length = prefix &&
        int_of_string_opt (String.sub path length suffix_length) <> None in
      let names = try Array.to_list (Sys.readdir ".") with Sys_error _ -> [] in
      List.filter (fun path -> List.exists (is_dump path) prefixes) names in
    let json_outputs =
      if !dump_asm_json && (Configuration.arch = "arm" || Configuration.arch = "powerpc")
      then List.map (fun path ->
        Filename.concat !json_dir (output_filename path ~suffix:!json_suffix)) !c_sources
      else [] in
    let trace_output = match trace_path with
      | Some path ->
          begin match stat path with
          | Some status when status.Unix.st_kind <> Unix.S_REG -> []
          | _ -> [path]
          end
      | None -> [] in
    let fixed_outputs = outputs @ List.concat (List.map dumps_for !c_sources) @
      dependency_outputs @ json_outputs @ trace_output in
    let planned_outputs () = List.sort_uniq String.compare (fixed_outputs @ rtl_outputs ()) in
    let outputs = planned_outputs () in
    let plan =
      if trace_alias || List.exists aliases_input outputs then
        `Reference "input and output alias"
      else if List.exists (fun input -> input.Unix.st_kind <> Unix.S_REG) input_stats
      then `Reference "input is not a regular file"
      else if List.exists (fun path ->
        match stat path with
        | Some out -> out.Unix.st_kind <> Unix.S_REG
        | None -> false) outputs
      then `Reference "output is not a regular file"
      else `Optimize (outputs, planned_outputs) in
    (plan, trace_alias)
  with CmdError _ -> (`Other, false)

(* The command-line module already expanded all response files. Replay the
   same effective arguments, including when a response file was a stream. *)
let replay_arguments () =
  let response arg = String.length arg > 0 && arg.[0] = '@' in
  let snapshot temp_dir =
    try
      let path = Filename.temp_file ?temp_dir "compcert" ".args" in
      at_exit (fun () -> safe_remove path);
      let out = open_out path in
      Fun.protect ~finally:(fun () -> close_out_noerr out) (fun () ->
        for i = 1 to Array.length Commandline.argv - 1 do
          Printf.fprintf out "\"%s\"\n" (Responsefile.gnu_quote Commandline.argv.(i))
        done;
        flush out);
      Some [|Sys.argv.(0); "@" ^ path|]
    with Sys_error _ -> None in
  let replayable arg =
    if not (response arg) then true else
    let path = String.sub arg 1 (String.length arg - 1) in
    try
      (Unix.stat path).Unix.st_kind = Unix.S_REG &&
      let input = open_in_bin path in
      Fun.protect ~finally:(fun () -> close_in_noerr input) (fun () ->
        (* Without a snapshot, do not risk reopening a nested response stream. *)
        let rec no_nested_file () =
          match input_char input with
          | '@' -> false
          | _ -> no_nested_file ()
          | exception End_of_file -> true in
        no_nested_file ())
    with Sys_error _ | Unix.Unix_error _ -> false in
  if not (Array.exists response Sys.argv) then Sys.argv else
  let arguments =
    match snapshot None with
    | None when not Sys.win32 -> snapshot (Some "/tmp")
    | arguments -> arguments in
  match arguments with
  | Some args -> args
  | None when Array.for_all replayable Sys.argv -> Sys.argv
  | None -> Commandline.argv

let attempt_environment reference =
  let overrides =
    [("COMPCERT_EXPERIMENT_FALLBACK", "0")] @
    if reference then [("COMPCERT_EXPERIMENTS", "")] else [] in
  let env = Array.to_list (Unix.environment ()) in
  let assigned key entry =
    let len = String.length key in
    String.length entry > len && entry.[len] = '=' && String.sub entry 0 len = key in
  let retained entry =
    List.for_all (fun (key, _) -> not (assigned key entry)) overrides in
  Array.of_list (List.filter retained env @ List.map (fun (k, v) -> k ^ "=" ^ v) overrides)

let forwarded_signals = [Sys.sigint; Sys.sigterm; Sys.sighup; Sys.sigquit]

let with_cancellation_blocked run =
  if Sys.win32 then run (fun () -> ()) else begin
    let previous_mask = Unix.sigprocmask Unix.SIG_BLOCK forwarded_signals in
    let restore_mask () = ignore (Unix.sigprocmask Unix.SIG_SETMASK previous_mask) in
    Fun.protect ~finally:restore_mask (fun () -> run restore_mask)
  end

let wait_for_attempt start =
  let rec wait pid =
    try snd (Unix.waitpid [] pid)
    with Unix.Unix_error (Unix.EINTR, _, _) -> wait pid in
  if Sys.win32 then wait (start (fun () -> ())) else begin
    with_cancellation_blocked (fun restore_mask ->
      let pid = start restore_mask in
      let cancelled = ref None in
      let forward signal =
        cancelled := Some signal;
        try Unix.kill (-pid) signal with Unix.Unix_error (Unix.ESRCH, _, _) ->
          (* The child may be starting up and not yet have called setsid. *)
          try Unix.kill pid signal with Unix.Unix_error (Unix.ESRCH, _, _) -> () in
      let handlers = List.map (fun signal ->
        signal, Sys.signal signal (Sys.Signal_handle forward)) forwarded_signals in
      Fun.protect
        ~finally:(fun () ->
          List.iter (fun (signal, handler) -> Sys.set_signal signal handler) handlers)
        (fun () ->
          restore_mask ();
          let status = wait pid in
          match !cancelled with
          | Some signal -> Unix.WSIGNALED signal
          | None -> status))
  end

let replay_attempt_log path output =
  let input = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr input) (fun () ->
    let buffer = Bytes.create 8192 in
    let rec copy () =
      let count = Stdlib.input input buffer 0 (Bytes.length buffer) in
      if count > 0 then begin
        Stdlib.output output buffer 0 count;
        copy ()
      end in
    copy ();
    flush output)

(* Keep the original paths passed to the toolchain: changing an output path
   can change the object, e.g. the default install name of a Mach-O dylib.
   Restore outputs before replay because the preprocessor may read one of
   those paths through an include, even if it is absent from the argv. *)
let path_status path =
  try Some (Unix.lstat path)
  with Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> None

let checkpoint_outputs paths =
  let saved = ref [] in
  let save path =
    match path_status path with
    | None -> ()
    | Some status ->
        if status.Unix.st_kind <> Unix.S_REG || status.Unix.st_nlink <> 1 ||
           (not Sys.win32 && status.Unix.st_uid <> Unix.geteuid ()) then
          raise (Sys_error "cannot checkpoint output");
        let backup = Filename.temp_file "compcert" ".output-backup" in
        saved := (path, status, backup) :: !saved;
        let output = open_out_bin backup in
        Fun.protect ~finally:(fun () -> close_out_noerr output)
          (fun () -> replay_attempt_log path output) in
  try List.iter save paths; Some !saved
  with Sys_error _ | Unix.Unix_error _ ->
    List.iter (fun (_, _, backup) -> safe_remove backup) !saved;
    None

let unlink_output path =
  try Unix.unlink path
  with Unix.Unix_error ((Unix.ENOENT | Unix.ENOTDIR), _, _) -> ()

let restore_outputs saved paths =
  let restore (path, original, backup) =
    let same_file status =
      status.Unix.st_kind = Unix.S_REG &&
      status.Unix.st_dev = original.Unix.st_dev &&
      status.Unix.st_ino = original.Unix.st_ino in
    begin match path_status path with
    | Some status when same_file status -> Unix.chmod path (original.Unix.st_perm lor 0o200)
    | _ -> unlink_output path
    end;
    let output = open_out_bin path in
    Fun.protect ~finally:(fun () -> close_out_noerr output)
      (fun () -> replay_attempt_log backup output);
    Unix.chmod path original.Unix.st_perm;
    Unix.utimes path original.Unix.st_atime original.Unix.st_mtime in
  List.iter (fun path ->
    if not (List.exists (fun (saved_path, _, _) -> saved_path = path) saved)
    then unlink_output path) paths;
  List.iter restore saved

let compiler_attempt argv ~reference out_fd err_fd =
  let env = attempt_environment reference in
  wait_for_attempt (fun restore_mask ->
    if Sys.win32 then
      Unix.create_process_env Sys.executable_name argv env Unix.stdin out_fd err_fd
    else
      match Unix.fork () with
      | 0 ->
          (* Put the compiler and its external tools in one process group. *)
          (try
             Unix.dup2 out_fd Unix.stdout;
             Unix.dup2 err_fd Unix.stderr;
             ignore (Unix.setsid ());
             restore_mask ();
             Unix.execvpe Sys.executable_name argv env
           with exn ->
             prerr_endline ("CompCert: cannot start compilation attempt: " ^ Printexc.to_string exn);
             Unix._exit 126)
      | pid -> pid)

let with_attempt_logs run =
  let setup () =
    try
      let out = tmp_file ".stdout" and err = tmp_file ".stderr" in
      Some (out, err)
    with Sys_error _ -> None in
  match setup () with
  | None -> None
  | Some (out, err) ->
      Fun.protect ~finally:(fun () -> safe_remove out; safe_remove err) (fun () ->
        let open_log path = Unix.openfile path [Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CLOEXEC] 0o600 in
        let open_logs () =
          try
            let out_fd = open_log out in
            try Some (out_fd, open_log err)
            with Unix.Unix_error _ -> Unix.close out_fd; None
          with Unix.Unix_error _ -> None in
        match open_logs () with
        | None -> None
        | Some (out_fd, err_fd) ->
            let replay () =
              replay_attempt_log out stdout;
              replay_attempt_log err stderr in
            Fun.protect ~finally:(fun () -> Unix.close out_fd; Unix.close err_fd)
              (fun () -> Some (run out_fd err_fd replay)))

(* A new process is necessary on retry: frontend builtin registration and
   backend oracles have process state. Running the entire invocation again
   also covers failures in assembly and linking of the generated units. *)
let finish_attempt status =
  match status with
  | Unix.WEXITED code -> exit code
  | Unix.WSIGNALED signal | Unix.WSTOPPED signal ->
      if not Sys.win32 then begin
        if signal <> Sys.sigkill then Sys.set_signal signal Sys.Signal_default;
        Unix.kill (Unix.getpid ()) signal
      end;
      exit 2

let reference_attempt argv =
  compiler_attempt argv ~reference:true Unix.stdout Unix.stderr

let run_reference reason argv =
  Printf.eprintf "CompCert: %s; compiling with experiments disabled.\n%!" reason;
  finish_attempt (reference_attempt argv)

let run_with_experiment_fallback argv initial_outputs planned_outputs =
  match checkpoint_outputs initial_outputs with
  | None -> run_reference "cannot preserve experimental outputs" argv
  | Some saved ->
      let keep_backups = ref false in
      let release () =
        if not !keep_backups then
          List.iter (fun (_, _, backup) -> safe_remove backup) saved in
      let status = Fun.protect ~finally:release (fun () ->
        with_attempt_logs (fun out_fd err_fd replay ->
          let optimized = compiler_attempt argv ~reference:false out_fd err_fd in
          match optimized with
          | Unix.WEXITED 0 -> replay (); optimized
          | Unix.WSIGNALED signal when List.mem signal forwarded_signals ->
              replay (); optimized
          | _ ->
              (try with_cancellation_blocked (fun _ ->
                     restore_outputs saved (planned_outputs ()))
               with (Sys_error _ | Unix.Unix_error _) as err ->
                 keep_backups := true;
                 List.iter (fun (path, _, backup) ->
                   Printf.eprintf "CompCert: backup of %S kept in %S.\n%!" path backup) saved;
                 fatal_error no_loc "cannot restore outputs before retry: %s" (Printexc.to_string err));
              prerr_endline "CompCert: experimental compilation failed; retrying with experiments disabled.";
              let reference = reference_attempt argv in
              if reference <> Unix.WEXITED 0 then begin
                prerr_endline "CompCert: diagnostics from the experimental attempt:";
                replay ()
              end;
              reference)) in
      match status with
      | Some status -> finish_attempt status
      | None -> run_reference "cannot capture experimental diagnostics" argv

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
           };
    Printexc.record_backtrace true;
    if ExperimentalOptions.flags <> [] then begin
      let plan, trace_alias = compilation_plan () in
      if Sys.getenv_opt "COMPCERT_EXPERIMENT_FALLBACK" <> Some "0" then begin
        match plan with
        | `Other -> ()
        | `Reference reason -> run_reference reason (replay_arguments ())
        | `Optimize (initial_outputs, planned_outputs) ->
            run_with_experiment_fallback (replay_arguments ()) initial_outputs planned_outputs
      end;
      if trace_alias then ExperimentalOptions.disable_trace ()
      else ExperimentalOptions.start_trace ()
    end;
    Frontend.init ();
    parse_cmdline cmdline_actions;
    Diagnostics.raise_on_errors (); (* Any error for command line arguments? *)
    DebugInit.init (); (* Initialize the debug functions *)
    if nolink () && !option_o <> None && !num_source_files >= 2 then
      fatal_error no_loc "ambiguous '-o' option (multiple source files)";
    if !num_input_files = 0 then
      fatal_error no_loc "no input file";
    if not !option_interp && !main_function_name <> "main" then
      fatal_error no_loc "option '-main' requires option '-interp'";
    let linker_args = time "Total compilation time" perform_actions () in
    if not (nolink ()) && linker_args <> [] then begin
      linker (output_filename_default "a.out") linker_args
    end;
    check_errors ()
  with
  | Sys_error msg
  | CmdError msg -> error no_loc "%s" msg; exit 2
  | Abort -> error_summary (); exit 2
  | e -> crash e
