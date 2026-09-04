(* skolem.mli — skolemize positive existentials in a VC's hypotheses.

   Existential closure of [let]/[match] types (Check.close_type) leaves hypotheses of
   the form [exists z. Psi]. A hypothesis is asserted *positively* (never under a
   universal) in the refutation [(/\ hyps) /\ ~goal], so such an existential can be
   replaced by a fresh Skolem *constant*, added to the VC scope. This keeps the query
   in EPR and turns the escaping facts into ground terms that the auto-instantiation
   (Smt.materialization) can fire the universal axioms on.

   Only plainly-positive existentials are skolemized: those reached from the root of a
   hypothesis through [/\], [\/] and the consequent of [==>], without crossing a
   negation or another quantifier. Anything else is left untouched for the solver. *)

val skolemize : Vc.t -> Vc.t
