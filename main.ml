(* main.ml — the `camlstar` driver: parse -> infer -> check -> (optionally) solve.

   Usage: camlstar [--print-vcs] [--solve] [--dump-smt DIR] FILE.cst

   Runs the pipeline and prints a summary. Flags:
     --print-vcs   write FILE.vcs (the generated sequents) beside the source
     --solve       discharge each VC with z3 and report verified/failed/unknown
     --dump-smt D  write each VC's SMT-LIB2 query to D/<reason>_<i>.smt2
   Exits nonzero on a parse/type/check error, or (with --solve) if any VC is not
   verified. *)

let vcs_path (src : string) : string =
  if Filename.check_suffix src ".cst" then Filename.chop_suffix src ".cst" ^ ".vcs"
  else src ^ ".vcs"

let () =
  let print_vcs = ref false in
  let solve = ref false in
  let dump_smt = ref None in
  let file = ref None in
  let args = Sys.argv in
  let i = ref 1 in
  while !i < Array.length args do
    (match args.(!i) with
     | "--print-vcs" -> print_vcs := true
     | "--solve" -> solve := true
     | "--dump-smt" -> incr i; if !i < Array.length args then dump_smt := Some args.(!i)
     | arg -> file := Some arg);
    incr i
  done;
  match !file with
  | None ->
    prerr_endline "usage: camlstar [--print-vcs] [--solve] [--dump-smt DIR] <file.cst>";
    exit 2
  | Some fn ->
    (try
       let m = Parse.parse_file fn in
       let m = Infer.infer_module m in
       let vcs = Check.check_module m in
       if !print_vcs then begin
         let out = vcs_path fn in
         let oc = open_out out in
         Printf.fprintf oc "(* %d verification conditions for %s *)\n\n" (List.length vcs) fn;
         List.iter (fun vc -> output_string oc (Vc.string_of_t vc); output_char oc '\n') vcs;
         close_out oc;
         Printf.printf "wrote %d VCs to %s\n" (List.length vcs) out
       end;
       if !solve || !dump_smt <> None then begin
         let results = Smt.solve_module ?dump_dir:!dump_smt m vcs in
         let verified = ref 0 and failed = ref 0 and unknown = ref 0 and errored = ref 0 in
         List.iter
           (fun (vc, v) ->
             (match v with
              | Smt.Verified -> incr verified
              | Smt.Failed _ -> incr failed
              | Smt.Unknown -> incr unknown
              | Smt.Solver_error _ -> incr errored);
             if !solve then
               Printf.printf "  [%s] %s\n" (Smt.string_of_verdict v) vc.Vc.reason)
           results;
         Printf.printf "%d verified, %d counterexamples, %d unknown, %d errors (of %d VCs)\n"
           !verified !failed !unknown !errored (List.length vcs);
         if !failed > 0 || !unknown > 0 then
           print_endline
             "note: unverified VCs may be spurious \
              (relational abstraction overapproximates functions)";
         if !failed > 0 || !unknown > 0 || !errored > 0 then exit 1
       end
       else
         Printf.printf "%d VCs generated, 0 type errors\n" (List.length vcs)
     with
     | Parse.Parse_error (msg, r) ->
       Printf.eprintf "%s:%d:%d: parse error: %s\n"
         r.Ast.file (fst r.Ast.rstart) (snd r.Ast.rstart) msg;
       exit 1
     | Infer.Type_error msg ->
       Printf.eprintf "type error: %s\n" msg;
       exit 1
     | Check.Check_error msg ->
       Printf.eprintf "check error: %s\n" msg;
       exit 1)
