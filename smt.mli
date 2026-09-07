(* smt.mli — discharge verification conditions with z3 (in-process via the OCaml API).

   Each VC becomes a self-contained SMT-LIB2 query: declare the sorts/relations it
   needs, assert the global axioms (datatype + function encodings) and the negated
   sequent [(/\ hyps) /\ ~goal]. The query text is handed to Z3 with
   [parse_smtlib2_string] and discharged with a [Solver]. [unsat] ⇒ the VC is valid;
   [sat] yields a [Z3.Model.model] counterexample. Requires Z3 4.13.3. *)

type verdict =
  | Verified
  | Failed of Z3.Model.model    (* sat: the counterexample model, for reconstruction *)
  | Unknown
  | Solver_error of string

val string_of_verdict : verdict -> string

(* Solve every VC of [m]. With [dump_dir], also write each query to
   <dir>/<reason>_<i>.smt2. *)
val solve_module : ?dump_dir:string -> Ast.modul -> Vc.t list -> (Vc.t * verdict) list
