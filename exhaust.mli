(* exhaust.mli — expand the default arm of a datatype match into constructor arms.

   A default arm ([_ -> e] or [x -> e]) placed after constructor arms means "every
   constructor the earlier arms did not name". Both consumers of a match — the
   definitional equations (axioms.ml) and the refinement checker (check.ml) — know
   only how to guard a *constructor* arm, so handed a default arm they would read it
   as unconditional. [expand] rewrites the arm list so that no default arm on a
   datatype scrutinee survives: each one becomes one [C f1 .. fn -> e] arm per
   constructor [C] not covered by an earlier arm, with fresh field variables, and
   with [x := scrutinee] substituted into [e] for a variable pattern. Arms after a
   default are unreachable and dropped.

   [ctors] lists the scrutinee type's constructors with their arities. An empty list
   (a non-datatype scrutinee: int, bool) leaves the arms unchanged. *)

val expand : (Ast.lid * int) list -> Ast.term -> Ast.branch list -> Ast.branch list
