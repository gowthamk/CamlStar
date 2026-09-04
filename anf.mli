(* anf.mli — A-Normal Form for the pre-SMT formula language.

   Every application of an *abstract* symbol (a user function or datatype
   constructor — not an interpreted operator and not an already-formed relation)
   is hoisted into a single-binding [let x = f(atoms) in ...], so that after this
   pass each such call is applied only to atoms (variables/constants) and sits at a
   position where relabs can wrap it in a quantifier. Interpreted operators and
   logical connectives are left in place. *)

val normalize : Ast.term -> Ast.term
