(* unify.mli — inference-time shape types and numeric-aware unification for Caml*.

   This is the "shape" layer of HM inference: base types, non-dependent arrows, and
   type-constructor applications, with metavariables. Ast refinements are erased into
   this language (see Infer.erase); metavariables live here, never in Ast.

   Some metavariables are *numeric*: they arise from arithmetic/comparison operators
   (`+`, `<`, `neg`, …) and may only be solved to int or float. An unresolved numeric
   metavariable defaults to int (see [default_numeric], [zonk], and Infer.generalize). *)

type ityp =
  | I_int | I_bool | I_float | I_unit | I_string
  | I_var   of Ast.tyvar             (* rigid, scheme-bound type variable *)
  | I_app   of Ast.lid * ityp list   (* type constructor application *)
  | I_arrow of ityp * ityp           (* non-dependent function shape *)
  | I_meta  of meta
and meta = { mid : int; mutable sol : ityp option; mutable numeric : bool }

exception Unify_error of ityp * ityp

val fresh_meta         : unit -> ityp   (* a fresh unconstrained metavariable *)
val fresh_numeric_meta : unit -> ityp   (* a fresh metavariable constrained to {int,float} *)

val repr        : ityp -> ityp          (* follow the solution chain to the head (path-compressing) *)
val occurs      : meta -> ityp -> bool  (* occurs-check *)
val unify       : ityp -> ityp -> unit  (* Robinson + numeric constraint; raises Unify_error *)
val free_metas  : ityp -> meta list     (* distinct unsolved metavariables, for generalization *)
val default_numeric : meta -> unit      (* if unsolved and numeric, solve it to int *)
val zonk        : ityp -> ityp          (* deep-resolve solutions; a stray unsolved numeric ⇒ int *)
val string_of_ityp : ityp -> string
