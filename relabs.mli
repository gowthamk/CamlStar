(* relabs.mli — Relational Abstraction (port of raven/backend/src/relabs.rs).

   Consumes an ANF'd, NNF'd formula and replaces every hoisted abstract call
   [let x = f(atoms) in body] by its EPR relation:
     positive position:  forall x. f_rel(atoms, x) ==> body
     negative position:  exists x. f_rel(atoms, x) /\  body
   Polarity flips under [~] and on the antecedent of [==>]. The sort of the
   introduced binder [x] is the result sort of [f], supplied by [ret_sort]. *)

val transform : (string -> Ast.base_typ) -> Ast.term -> Ast.term

(* Relabs at negative polarity: a [let x = f(atoms) in body] chain becomes
   [exists x. f_rel(atoms, x) /\ body]. Used to *materialise* a VC's ground applied
   subterms (assert each has a value) — the auto-instantiation of raven's
   auto_inst.rs, which gives the universal definitional/functionality axioms ground
   terms to fire on. *)
val transform_neg : (string -> Ast.base_typ) -> Ast.term -> Ast.term
