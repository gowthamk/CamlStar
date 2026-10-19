(* cegqi.mli — counterexample-guided quantifier instantiation: find the witnesses a
   stuck application is missing.

   Under relational abstraction a ground application [f(args)] can be **stuck**: its
   definitional equation is satisfied vacuously because some relation in the axiom's
   antecedent is left false. The repair is to materialise the terms that antecedent needs,
   which is exactly what [instantiate!] does. This module computes those terms
   mechanically, by matching the *structured* definitional equations
   ([Axioms.definitional_equations]) against the applications a VC already has — so there
   is only one notion of "unfold one step" in the system.

   This module is pure: it never calls the solver. [Smt] owns the round loop. *)

(* Constructor shapes the branch's hypotheses pin, as [term -> C(...)]: the discriminators
   [a = S a'], [c = Z] that a match arm contributes, keyed by the variable as a term. The
   key is a term so that an application can carry a shape too (a derived shape such as
   [len t -> S (len t2)]); lookup is up to alpha-equality, first entry wins. These are
   what let an equation's argument patterns match. *)
val shapes : Ast.modul -> Vc.t -> (Ast.term * Ast.term) list

(* Add a shape for [key] unless one is already recorded for it. *)
val add_shape : (Ast.term * Ast.term) list -> Ast.term -> Ast.term -> (Ast.term * Ast.term) list

(* Rewrite every subterm that has a shape, repeatedly, within the given fuel. *)
val apply_shapes : (Ast.term * Ast.term) list -> int -> Ast.term -> Ast.term

(* Evaluate a source term in a reconstructed counterexample, by lookup in the same
   argument-tuple maps the model prints. [None] means the model assigns the term no value
   — for a data application that is precisely "the relation relates these arguments to
   nothing", i.e. stuck. Bool-returning functions are total SMT predicates, so they always
   yield [Some true]/[Some false]; undefinedness is a data-only signal. *)
val eval_in_cex : Cex.t -> Ast.term -> Cex.value option

(* One matched equation, instantiated: its right-hand side and the guard calls on the path
   to that leaf. [guards = []] means the equation is unconditional, so [rhs] is what the
   application equals rather than one alternative among several. *)
type unfolding = { rhs : Ast.term; guards : Ast.term list }

(* Unfold one application one step: one [unfolding] for every definitional equation of its
   head whose argument patterns match (after expanding [shapes]). Returns [] when no
   equation matches — in particular when an argument has no constructor shape to match
   against. *)
val unroll : Axioms.defeq list -> (Ast.term * Ast.term) list -> Ast.term -> unfolding list

(* The terms an unfolding needs materialised: its right-hand side and its guard calls. *)
val unfolding_terms : unfolding -> Ast.term list

(* The terms to add to [vc.instantiations] this round: unfold every application the VC
   already materialises and keep the results that are not materialised yet and are closed
   over [vc.scope]. [[]] means **saturation** — nothing left to instantiate, so what
   remains needs a lemma. *)
val candidates : Ast.modul -> Vc.t -> Ast.term list
