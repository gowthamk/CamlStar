(* parse.mli — driver: turn Caml* source text into an Ast.modul. *)

(* Raised on lexical or syntactic errors, or on ill-formed constructs detected in
   semantic actions (e.g. refining a function type). Carries a message and the
   source range where the problem was detected. *)
exception Parse_error of string * Ast.range

val parse_string : string -> Ast.modul
val parse_file   : string -> Ast.modul
