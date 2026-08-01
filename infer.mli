(* infer.mli — Hindley–Milner shape inference for Caml*.

   Works on erased shapes (refinements dropped) using Unify. Fills the optional type
   holes in the Ast in place: unannotated lambda/quantifier binders (`xtyp`/`qty`) and
   let bindings (`lb_scheme`) come back annotated with their inferred (generalized)
   types. Raises Type_error on any ill-typed program. *)

exception Type_error of string

val infer_module : Ast.modul -> Ast.modul
