(* smt.mli — discharge verification conditions with z3 (in-process via the OCaml API).

   Each VC becomes a self-contained SMT-LIB2 query: declare the sorts/relations it
   needs, assert the global axioms (datatype + function encodings) and the negated
   sequent [(/\ hyps) /\ ~goal]. The query text is handed to Z3 with
   [parse_smtlib2_string] and discharged with a [Solver]. [unsat] ⇒ the VC is valid;
   [sat] yields a [Z3.Model.model] counterexample. Requires Z3 4.13.3. *)

type verdict =
  | Verified
  | Saturated of Cex.t          (* sat and instantiation is exhausted: needs a lemma *)
  | Fuel_exhausted of Cex.t     (* sat and unrolling was cut off: effectively "unknown" *)
  | Unknown
  | Solver_error of string

val string_of_verdict : verdict -> string

(* Solve every VC of [m], running the CEGQI loop (see [Cegqi]): on [sat], materialise the
   witnesses the stuck applications are missing and solve again.

   - [cegqi] (default true): false restores a single solve per VC, so every [sat] is
     reported as [Saturated] and only hand-written [instantiate!] hints apply.
   - [fuel] (default 3): maximum rounds, equivalently maximum unrolling depth. Reaching it
     gives [Fuel_exhausted], which — unlike [Saturated] — is not evidence that a lemma is
     needed.
   - [trace]: print each round's added instantiations.
   - [timeout_ms] (default 10000): per-query solver timeout. Needed because EPR only bounds
     queries over uninterpreted sorts: an equation with no constructor pattern on its
     argument triggers on every term of its sort, so adding instantiations can make one
     query blow up. Such a query reports [Unknown] instead of hanging.

   The returned [Vc.t] is the *final* one, so its [instantiations] include everything CEGQI
   added. With [dump_dir], each round's query is written to <dir>/<reason>_<i>.smt2, with a
   _r<round> suffix after the first. *)
val solve_module :
  ?dump_dir:string -> ?cegqi:bool -> ?fuel:int -> ?trace:bool -> ?timeout_ms:int ->
  Ast.modul -> Vc.t list -> (Vc.t * verdict) list

(* queries sent to z3 by the last [solve_module] *)
val solver_calls : unit -> int
