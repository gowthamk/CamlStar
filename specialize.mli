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

(* The clone key: a template and its function arguments (lambdas, after [as_lambda]),
   each closed over the captured variables `c1 … ck`. Two call sites whose lambdas
   differ only in the captured values have equal keys and share one clone.
   [k_ncaptured] is k, the number of captured variables (the clone's leading
   parameters). *)
type key = { k_template : string; k_lams : Ast.term list; k_ncaptured : int }

(* [captured lams]: the free local variables of [lams], in order of first occurrence
   (top-level names are not variables). *)
val captured : Ast.term list -> Ast.var list

(* [key_of ~template lams] = (key, cs): the key, and the captured variables [cs], which
   the call site passes to the clone first (`find (fun x -> le v x) l` ⇒ key `find,
   fun c1 -> fun x -> le c1 x`, cs = [v], call `find__0 v l`). *)
val key_of : template:string -> Ast.term list -> key * Ast.var list

(* Same template, and the closed lambdas alpha-equal position by position. *)
val key_equal : key -> key -> bool

(* A template: a top-level definition with a function parameter. [t_lb] is the parsed
   binding, [t_funs] the 0-based positions of its function parameters with their types
   (`map (f:nat -> nat) l` ⇒ [(0, nat -> nat)]), [t_scheme] its type from [typed]. *)
type template = { t_name : string; t_lb : Ast.letbinding; t_funs : (int * Ast.typ) list;
                  t_scheme : Ast.tscheme }

(* [find_templates ~typed parsed]: the templates among [parsed]'s top-level `let`s, in
   order, with types read from [typed] (the user's `val`, else the inferred scheme, so
   an unannotated parameter used as a function counts). Raises [Specialize_error] for a
   polymorphic template: `map: a polymorphic template (type variable 'a) cannot be
   specialized; write a monomorphic copy`. A polymorphic first-order definition is not
   a template and is fine. *)
val find_templates : typed:Ast.modul -> Ast.modul -> template list

(* [clone_body t k ~name]: the first-order clone of template [t] at key [k] (whose
   lambdas are in [t.t_funs] order), as a `let [rec]` group of one binding [name]:
   parameters c1 … ck (captured, unannotated) then [t]'s non-function parameters; the
   body with each function parameter replaced by its lambda, β-reduced, and every
   self-call `g … f … ā` rewritten to `name c1 … ck ā`. For `map (fun y -> S y)`:
   `let rec map__0 (l:nlist) = match l with NNil -> NNil | NCons x r -> NCons (S x)
   (map__0 r)`. No `val` (H5b). Raises [Specialize_error] for a self-call that changes
   a function argument (rejection C2, `iter: the recursive call passes `fun y -> f (f
   y)` for `f`, not `f` itself; specialization would not terminate`) or omits one. *)
val clone_body : template -> key -> name:string -> Ast.letbindings
