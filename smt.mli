(* smt.mli — discharge verification conditions with z3.

   Each VC becomes a self-contained SMT-LIB2 query: declare the sorts/relations it
   needs, assert the global axioms (datatype + function encodings) and the negated
   sequent [(/\ hyps) /\ ~goal], then [check-sat]. [unsat] ⇒ the VC is valid. *)

type verdict = Verified | Failed | Unknown | Solver_error of string

val string_of_verdict : verdict -> string

(* Solve every VC of [m]. With [dump_dir], also write each query to
   <dir>/<reason>_<i>.smt2. The z3 binary is $CAMLSTAR_Z3 (default "z3"). *)
val solve_module : ?dump_dir:string -> Ast.modul -> Vc.t list -> (Vc.t * verdict) list
