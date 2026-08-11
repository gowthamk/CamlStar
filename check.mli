(* check.mli — the dependent/refinement type checker as a VC generator.

   [check_module] runs over an *inference-filled* module (every binder type and
   let scheme already populated by [Infer.infer_module]) and emits the subtyping
   verification conditions [Vc.t] the definitions give rise to. It does NOT call a
   solver — discharging the VCs is a later phase. Obligations whose goal is
   syntactically [true] are elided. *)

exception Check_error of string

val check_module : Ast.modul -> Vc.t list
