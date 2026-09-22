(* vc.mli — verification conditions: the interface between the refinement checker
   and the SMT solver.

   A VC is a self-contained typed sequent. It is valid iff

       forall scope. (/\ axioms  /\  /\ hyps)  ==>  goal

   and [solve] discharges it by asking the SMT solver whether

       (/\ axioms) /\ (/\ hyps) /\ ~goal      is UNSAT under [decls].

   Datatypes are encoded as an uninterpreted sort plus constructor/selector/tester
   function declarations, with their meaning supplied through [axioms]. Sorts reuse
   Ast.base_typ (B_int→Int, B_bool→Bool, B_float→Real, B_var→an uninterpreted sort,
   B_app l _→the sort named l). Propositions (hyps/goal/axioms) are ordinary Ast
   terms of boolean sort. *)

type decl =
  | Dec_sort of Ast.lid                                      (* an uninterpreted sort constructor *)
  | Dec_fun  of Ast.lid * Ast.base_typ list * Ast.base_typ   (* a function symbol: arg sorts, result sort *)

type t = {
  decls  : decl list;                        (* sorts + function symbols this VC references *)
  axioms : Ast.term list;                    (* datatype axioms, function definitions, assumed lemmas *)
  scope  : (Ast.var * Ast.base_typ) list;    (* the logical context Γ: sorted vars, ordered *)
  hyps   : Ast.term list;                    (* local assumptions: Γ's refinements, path conditions, antecedent *)
  goal   : Ast.term;                         (* the proposition to prove *)
  instantiations : Ast.term list;            (* instantiate! hints: terms to materialise *)
  range  : Ast.range;                        (* source of the obligation, for error reporting *)
  reason : string;                           (* human-readable label *)
}

val string_of_t : t -> string
