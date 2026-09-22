(* smtlib.mli — render Caml* [Ast.term]s and sorts to SMT-LIB2 text.

   The term language handled here is the *post-pipeline* fragment: variables,
   constants, interpreted operators (mapped to SMT builtins), equality/logical
   connectives, quantifiers, and uninterpreted relation applications
   [Tm_app (Tm_fvar f) [args; result]]. Source-only nodes (lambda/let/match) are
   rejected — they must have been eliminated by ANF/NNF/relabs first. *)

(* Is this top-level symbol an interpreted operator (native to SMT) rather than a
   user function/constructor that must be relationally abstracted? *)
val is_interpreted : string -> bool

(* A logical connective (l_and/l_or/l_imp/l_iff/l_not): combines *formulas*. *)
val is_connective : string -> bool

(* A relation symbol (name ends in "_rel"): already a boolean predicate, never
   relationally abstracted. *)
val is_relation : string -> bool

(* Map a raw identifier to an SMT-safe symbol (non-alphanumerics become '_'). *)
val sanitize : string -> string

(* SMT sort name for a base type. Int/Bool/Real/String are builtins; B_unit,
   B_app and B_var render to declared uninterpreted sorts. *)
val sort_of_base : Ast.base_typ -> string

(* Does [sort_of_base b] name a builtin sort (needs no declare-sort)? *)
val is_builtin_sort : Ast.base_typ -> bool

(* A per-query naming for term variables (vid -> chosen readable symbol). Variables
   not in the table render as the default [name_vid]. *)
type naming

(* Build a naming for a set of variables (a VC's scope constants): each prints with
   its bare source name where that is unique, quoted (|name|) if it is not a valid
   simple symbol, and suffixed with the vid only to break an actual clash. *)
val make_naming : Ast.var list -> naming

(* The SMT symbol for a term variable under [naming]: the table's readable symbol if
   present, else a stable, SMT-safe [name_vid] identifier. *)
val smt_var : naming -> Ast.var -> string

(* Render a (pipeline-normalised) term as an SMT-LIB2 s-expression string, using
   [naming] for its variables. *)
val term_to_sexpr : naming -> Ast.term -> string

(* The "instantiated terms" ledger: the user-function/constructor applications a VC
   materialises, grouped [(label, terms)] by source (goal / hypotheses / hints), inner
   applications first. This is the mechanical input for choosing instantiate! hints and
   is printed both after a counterexample and as a comment atop each dumped query. *)
val ledger_sections : Vc.t -> (string * Ast.term list) list
