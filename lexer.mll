(* lexer.mll — ocamllex lexer for Caml*. Mirrors F*'s surface tokens. *)
{
open Parser   (* the Menhir-generated token type *)

exception Lex_error of string * Lexing.position

let error lexbuf msg = raise (Lex_error (msg, Lexing.lexeme_start_p lexbuf))

(* Keywords → tokens; anything else lexes as a lowercase IDENT. *)
let keyword_table : (string, token) Hashtbl.t = Hashtbl.create 64
let () =
  List.iter (fun (k, t) -> Hashtbl.add keyword_table k t)
    [ "module", MODULE; "let", LET; "rec", REC; "and", AND; "in", IN;
      "val", VAL; "assume", ASSUME; "type", TYPE; "match", MATCH; "with", WITH;
      "fun", FUN; "if", IF; "then", THEN; "else", ELSE;
      "forall", FORALL; "exists", EXISTS; "requires", REQUIRES; "ensures", ENSURES;
      "assert", ASSERT; "true", TRUE; "false", FALSE;
      "Lemma", LEMMA;
      "private", PRIVATE; "irreducible", IRREDUCIBLE; "unfold", UNFOLD;
      "noeq", NOEQ; "logic", LOGIC ]

let ident_or_kw s =
  match Hashtbl.find_opt keyword_table s with
  | Some t -> t
  | None -> IDENT s

(* Uppercase keywords (e.g. Lemma) must also be caught; default to UIDENT. *)
let uident_or_kw s =
  match Hashtbl.find_opt keyword_table s with
  | Some t -> t
  | None -> UIDENT s
}

let digit   = ['0'-'9']
let lower   = ['a'-'z' '_']
let upper   = ['A'-'Z']
let idchar  = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let lident  = lower idchar*
let uident  = upper idchar*
let tyvar   = '\'' ['a'-'z' 'A'-'Z'] idchar*
let intlit  = digit+
let floatlit = digit+ '.' digit* (['e' 'E'] ['+' '-']? digit+)?
             | digit+ ['e' 'E'] ['+' '-']? digit+

rule token = parse
  | [' ' '\t' '\r']+   { token lexbuf }
  | '\n'               { Lexing.new_line lexbuf; token lexbuf }
  | "(*"               { comment 0 lexbuf; token lexbuf }
  | "//"               { line_comment lexbuf; token lexbuf }

  (* pragmas — match before the generic '#'/operators *)
  | "#set-options"     { PRAGMA_SET_OPTIONS }
  | "#push-options"    { PRAGMA_PUSH_OPTIONS }
  | "#pop-options"     { PRAGMA_POP_OPTIONS }
  | "#check"           { PRAGMA_CHECK }
  | "#eval"            { PRAGMA_EVAL }

  (* literals *)
  | floatlit as f      { FLOAT (float_of_string f) }
  | intlit as i        { INT (int_of_string i) }
  | '"'                { STRING (string_lit (Buffer.create 16) lexbuf) }
  | tyvar as tv        { TYVAR (String.sub tv 1 (String.length tv - 1)) }

  (* multi-char operators — longest match first *)
  | "[@@"              { LBRACK_AT_AT }
  | "<==>"             { IFF }
  | "==>"              { IMPLIES }
  | "=="               { EQEQ }
  | "<>"               { NEQ }
  | "<="               { LE }
  | ">="               { GE }
  | "<:"               { SUBTYPE }
  | "->"               { ARROW }
  | "/\\"              { CONJ }
  | "\\/"              { DISJ }

  (* single-char punctuation / operators *)
  | '('                { LPAREN }
  | ')'                { RPAREN }
  | '{'                { LBRACE }
  | '}'                { RBRACE }
  | '['                { LBRACK }
  | ']'                { RBRACK }
  | ':'                { COLON }
  | ';'                { SEMICOLON }
  | '.'                { DOT }
  | '|'                { BAR }
  | '='                { EQUALS }
  | '<'                { LT }
  | '>'                { GT }
  | '~'                { TILDE }
  | '+'                { PLUS }
  | '-'                { MINUS }
  | '*'                { STAR }
  | '/'                { SLASH }
  | '%'                { PERCENT }

  | "instantiate!"     { INSTANTIATE }   (* proof hint; '!' is not an idchar *)
  | lident as s        { ident_or_kw s }
  | uident as s        { uident_or_kw s }

  | eof                { EOF }
  | _ as c             { error lexbuf (Printf.sprintf "unexpected character %C" c) }

and comment depth = parse
  | "(*"   { comment (depth + 1) lexbuf }
  | "*)"   { if depth = 0 then () else comment (depth - 1) lexbuf }
  | '\n'   { Lexing.new_line lexbuf; comment depth lexbuf }
  | eof    { error lexbuf "unterminated comment" }
  | _      { comment depth lexbuf }

and line_comment = parse
  | '\n'   { Lexing.new_line lexbuf }
  | eof    { () }
  | _      { line_comment lexbuf }

and string_lit buf = parse
  | '"'          { Buffer.contents buf }
  | "\\n"        { Buffer.add_char buf '\n'; string_lit buf lexbuf }
  | "\\t"        { Buffer.add_char buf '\t'; string_lit buf lexbuf }
  | "\\r"        { Buffer.add_char buf '\r'; string_lit buf lexbuf }
  | "\\\""       { Buffer.add_char buf '"';  string_lit buf lexbuf }
  | "\\\\"       { Buffer.add_char buf '\\'; string_lit buf lexbuf }
  | '\n'         { error lexbuf "newline inside string literal" }
  | eof          { error lexbuf "unterminated string literal" }
  | _ as c       { Buffer.add_char buf c; string_lit buf lexbuf }
