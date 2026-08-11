(* main.ml — the `camlstar` driver: parse -> infer -> check.

   Usage: camlstar [--print-vcs] FILE.cst

   Runs the full pipeline and prints a one-line summary. With --print-vcs it also
   writes the generated verification conditions to FILE.vcs (same basename) beside
   the source. Exits nonzero on a parse/type/check error. *)

let vcs_path (src : string) : string =
  if Filename.check_suffix src ".cst" then Filename.chop_suffix src ".cst" ^ ".vcs"
  else src ^ ".vcs"

let () =
  let print_vcs = ref false in
  let file = ref None in
  Array.iteri
    (fun i arg ->
      if i = 0 then ()
      else if arg = "--print-vcs" then print_vcs := true
      else file := Some arg)
    Sys.argv;
  match !file with
  | None ->
    prerr_endline "usage: camlstar [--print-vcs] <file.cst>";
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
