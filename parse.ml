(* parse.ml — driver around the ocamllex lexer and Menhir parser. *)

exception Parse_error of string * Ast.range

let range_of (s : Lexing.position) (e : Lexing.position) : Ast.range =
  { Ast.file = s.pos_fname;
    rstart = (s.pos_lnum, s.pos_cnum - s.pos_bol);
    rend   = (e.pos_lnum, e.pos_cnum - e.pos_bol) }

let parse_lexbuf (lexbuf : Lexing.lexbuf) : Ast.modul =
  try Parser.modul Lexer.token lexbuf with
  | Lexer.Lex_error (msg, pos) ->
    raise (Parse_error (msg, range_of pos pos))
  | Parser.Error ->
    let s = Lexing.lexeme_start_p lexbuf and e = Lexing.lexeme_end_p lexbuf in
    raise (Parse_error
             (Printf.sprintf "syntax error at %S" (Lexing.lexeme lexbuf), range_of s e))
  | Failure msg ->
    (* ill-formed construct raised from a semantic action *)
    let s = Lexing.lexeme_start_p lexbuf and e = Lexing.lexeme_end_p lexbuf in
    raise (Parse_error (msg, range_of s e))

let parse_string (src : string) : Ast.modul =
  let lexbuf = Lexing.from_string src in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "<string>" };
  parse_lexbuf lexbuf

let parse_file (fn : string) : Ast.modul =
  let ic = open_in fn in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
    let lexbuf = Lexing.from_channel ic in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fn };
    parse_lexbuf lexbuf)
