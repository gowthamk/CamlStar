(* specialize.mli — specialization of higher-order definitions (todo, plan H0–H9).

   Runs between two inferences: parse -> infer -> specialize -> infer -> check. Each
   call of a template (a definition with a function parameter) at a lambda or a
   definition name becomes a call of a first-order clone, so nothing higher-order
   reaches the checker or the solver.

   [specialize_module ~typed parsed] rewrites [parsed], the module as parsed; [typed] is
   the same module after inference and is only read, for types (which parameters are
   functions). The result is untyped, and the second inference types it, clones
   included. Rewriting the parsed tree, not the inferred one, is deliberate: inference
   is not idempotent. A definition checked against a polymorphic `val` leaves its
   binders' types as unsolved metas, which the fill-back turns into fresh type
   variables distinct from the `val`'s, so re-inferring an inferred module fails with
   `let annotation mismatch: 'a vs 'a` (tests/prop_list_append.cst).

   Currently the identity (plan step H2). *)

val specialize_module : typed:Ast.modul -> Ast.modul -> Ast.modul

(* ===== helpers, exposed for specialize_test.ml ===== *)

(* [beta t]: β-normal form of [t]. Contracts every `(fun x -> e) a` in [t], under
   binders, in `let`s, match arms and guards, and quantifier bodies included, until none
   is left (a contraction that creates a new redex is followed). Capture-avoiding
   (by [Subst.subst_term]), so bound variables come back renamed; compare results
   with [Subst.alpha_equal_term]. Types inside [t] (binder annotations, ascriptions)
   are left as they are. *)
val beta : Ast.term -> Ast.term

(* [inline_local_lambdas t]: every `let h = fun x -> e in b` in [t] (non-recursive, one
   binding) replaced by [b] with the lambda substituted for [h], each copy with fresh
   binders. Leaves the applications it creates, `(fun x -> e) a`, to [beta]. *)
val inline_local_lambdas : Ast.term -> Ast.term

(* A program specialization rejects (the C1/C2 rejections, a polymorphic template, …).
   The message names the template and the offending term; terms carry no location, so
   the driver adds the declaration's range. *)
exception Specialize_error of string

(* [as_lambda ~template pty arg]: the argument [arg], passed for a parameter of
   function type [pty] of [template], as a lambda. A lambda is returned as is; a
   top-level name is η-expanded to [pty]'s arity (`succ` ⇒ `fun x1 -> succ x1`, `le`
   at `nat -> nat -> bool` ⇒ `fun x1 x2 -> le x1 x2`); anything else raises
   [Specialize_error] (rejection C1), e.g. `map: the function argument `const_fn v`
   is not a lambda or a definition name`. *)
val as_lambda : template:string -> Ast.typ -> Ast.term -> Ast.term
