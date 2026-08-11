(* shape.mli — the bridge between the surface [Ast.typ] and the inference-time
   shape language [Unify.ityp] (refinements erased, arrows non-dependent).

   [erase]/[reflect] and the [ischeme] type are shared by HM inference (infer.ml)
   and the dependent checker. [unify_shape] is a two-sided shape-consistency check;
   [match_typ] is the one-sided instantiation primitive the checker pairs with
   [Subst.subst_tyvars]. *)

(* A type scheme over shapes; the bool marks a *numeric* bound variable. *)
type ischeme = { bound : (Ast.tyvar * bool) list; body : Unify.ityp }

val erase        : Ast.typ -> Unify.ityp
val erase_base   : Ast.base_typ -> Unify.ityp
val reflect      : Unify.ityp -> Ast.typ
val erase_scheme   : Ast.tscheme -> ischeme
val reflect_scheme : ischeme -> Ast.tscheme

(* Consistency of two surface types at the shape level; may raise Unify.Unify_error. *)
val unify_shape : Ast.typ -> Ast.typ -> unit

(* [match_typ pat concrete] reads type-variable bindings off [concrete] by aligning
   the base/arrow skeletons of the two types (refinements ignored). Every [B_var tv]
   in [pat] is bound to the aligned subtree of [concrete]. Raises [Match_error] on a
   skeleton mismatch or an inconsistent repeated binding. *)
exception Match_error of string
val match_typ : Ast.typ -> Ast.typ -> (Ast.tyvar * Ast.typ) list
