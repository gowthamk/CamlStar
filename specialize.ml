(* specialize.ml — see specialize.mli. *)

let specialize_module ~(typed : Ast.modul) (parsed : Ast.modul) : Ast.modul =
  ignore typed;
  parsed
