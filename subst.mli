(* subst.mli — capture-avoiding substitution for the stratified dependent AST.

   Two substitution kinds are needed by the refinement checker:

   - term-for-term, [subst_term]/[subst_typ], which drives dependent-arrow
     application:  typing [f e] with [f : x:T1 -> T2] yields [T2[x := e]].
   - type-for-tyvar, [subst_tyvars], which drives polymorphic instantiation:
     [list 'a] at ['a := int] becomes [list int].

   Capture-avoidance is by *binder freshening*: every bound variable is re-minted
   with a fresh [vid] as we descend, so a moved free variable can never be captured
   and repeated instantiation of a shared scheme value yields distinct bound vids.
   Consequently [subst_term []] / [subst_typ []] are exactly alpha-renaming, exposed
   as [freshen_term] / [freshen_typ]. *)

exception Subst_error of string

val subst_term   : (Ast.var * Ast.term) list -> Ast.term -> Ast.term
val subst_typ    : (Ast.var * Ast.term) list -> Ast.typ  -> Ast.typ
val subst_tyvars : (Ast.tyvar * Ast.typ) list -> Ast.typ -> Ast.typ

val freshen_term : Ast.term -> Ast.term
val freshen_typ  : Ast.typ  -> Ast.typ

val free_vars_term  : Ast.term -> Ast.var list
val free_vars_typ   : Ast.typ  -> Ast.var list
val free_tyvars_typ : Ast.typ  -> Ast.tyvar list

val alpha_equal_term : Ast.term -> Ast.term -> bool
val alpha_equal_typ  : Ast.typ  -> Ast.typ  -> bool
