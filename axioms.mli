(* axioms.mli — the relational encoding of a module's datatypes (and, later,
   functions): SMT declarations plus the logical axioms that make the relations
   behave like the functions/constructors they abstract.

   Each constructor C becomes a relation C_rel(fields, result) over an uninterpreted
   sort UI_T (a 0-ary constructor becomes a constant instead), with functionality,
   injectivity and disjointness axioms — exactly as raven/backend/src/smt/axioms.rs. *)

(* the relation name for a function/constructor symbol (adds the "_rel" suffix) *)
val rel_name : string -> string

(* (declare-sort UI_T 0) for every uninterpreted sort the datatypes reference *)
val datatype_sort_decls : Ast.modul -> string list

(* (declare-const C ..) for 0-ary constructors, (declare-fun C_rel .. Bool) otherwise *)
val constructor_decls : Ast.modul -> string list

(* functionality / injectivity / disjointness axioms as ordinary Ast.terms *)
val datatype_axioms : Ast.modul -> Ast.term list

(* source names of functions that return bool: encoded as SMT predicates [f: args ->
   Bool] under their own name rather than relationally abstracted into [f_rel] *)
val bool_fn_names : Ast.modul -> string list

(* declarations for every user function: [f_rel(args, result)] for data functions,
   [f(args)] (a predicate) for bool-returning ones *)
val function_decls : Ast.modul -> string list

(* functionality axiom for each function *relation* (bool predicates are skipped —
   an SMT predicate is already a function of its arguments) *)
val function_axioms : Ast.modul -> Ast.term list

(* result base sort of each function/constructor, for relabs binder sorts *)
val ret_sort_table : Ast.modul -> (string, Ast.base_typ) Hashtbl.t

(* definitional equations (with bare calls, to be sent through the pipeline) for
   every function with a body, a non-unit return, and no user-annotated refinement
   — one equation per match/if leaf, as in raven's generate_axioms_from_body *)
val definitional_axioms : Ast.modul -> Ast.term list
