(* infer_test.ml — parse a Caml* file, run HM inference, print the filled Ast. *)

let () =
  if Array.length Sys.argv < 2 then (
    prerr_endline "usage: infer_test <file.cst>";
    exit 2);
  let fn = Sys.argv.(1) in
  match Parse.parse_file fn with
  | exception Parse.Parse_error (msg, r) ->
    let l, c = r.Ast.rstart in
    Printf.eprintf "%s:%d:%d: parse error: %s\n" r.Ast.file l c msg;
    exit 1
  | m ->
    match Infer.infer_module m with
    | exception Infer.Type_error msg ->
      Printf.eprintf "type error: %s\n" msg; exit 1
    | exception Unify.Unify_error (a, b) ->
      Printf.eprintf "type error: cannot unify %s with %s\n"
        (Unify.string_of_ityp a) (Unify.string_of_ityp b);
      exit 1
    | m' ->
      Printf.printf "module %s\n\n"
        (String.concat "." (m'.Ast.mod_name.ns @ [ m'.Ast.mod_name.bname ]));
      List.iter
        (fun se -> print_endline (Ast.string_of_sigelt se); print_newline ())
        m'.Ast.mod_decls
