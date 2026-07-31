(* parse_test.ml — parse a Caml* source file and print the resulting Ast. *)

let () =
  if Array.length Sys.argv < 2 then (
    prerr_endline "usage: parse_test <file.cst>";
    exit 2);
  let fn = Sys.argv.(1) in
  match Parse.parse_file fn with
  | m ->
    Printf.printf "module %s\n\n"
      (String.concat "." (m.Ast.mod_name.ns @ [ m.Ast.mod_name.bname ]));
    List.iter
      (fun se -> print_endline (Ast.string_of_sigelt se); print_newline ())
      m.Ast.mod_decls
  | exception Parse.Parse_error (msg, r) ->
    let sl, sc = r.Ast.rstart in
    Printf.eprintf "%s:%d:%d: parse error: %s\n" r.Ast.file sl sc msg;
    exit 1
