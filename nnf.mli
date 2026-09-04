(* nnf.mli — Negation Normal Form for the ANF'd formula language.

   Eliminates [==>] and [<==>], pushes [~] down to atoms (De Morgan, flipping
   quantifiers), and threads through the value-level lets ANF introduced. After
   this pass every negation sits directly on an atom, so relabs can read polarity
   off the syntactic position. *)

val normalize : Ast.term -> Ast.term
