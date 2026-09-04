(* nnf.ml — see nnf.mli. *)

open Ast

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

(* [nnf neg t]: the NNF of [t], negated iff [neg]. *)
let rec nnf (neg : bool) (t : term) : term =
  match t with
  | Tm_let (lbs, body) -> Tm_let (lbs, nnf neg body)     (* let binds a value: descend into body *)
  | Tm_quant { qk; qv; qty; qbody } ->
    let qk' = if neg then (match qk with Forall -> Exists | Exists -> Forall) else qk in
    Tm_quant { qk = qk'; qv; qty; qbody = nnf neg qbody }
  | Tm_ascribed (e, _) -> nnf neg e
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head, args with
     | Tm_fvar l, [ a ] when l.bname = "l_not" -> nnf (not neg) a
     | Tm_fvar l, [ a; b ] when l.bname = "l_and" ->
       if neg then mk_or (nnf true a) (nnf true b) else mk_and (nnf false a) (nnf false b)
     | Tm_fvar l, [ a; b ] when l.bname = "l_or" ->
       if neg then mk_and (nnf true a) (nnf true b) else mk_or (nnf false a) (nnf false b)
     | Tm_fvar l, [ a; b ] when l.bname = "l_imp" ->
       nnf neg (mk_or (mk_not a) b)
     | Tm_fvar l, [ a; b ] when l.bname = "l_iff" ->
       nnf neg (mk_and (mk_imp a b) (mk_imp b a))
     | _ -> if neg then mk_not t else t)                 (* atom: predicate / relation / bool var *)
  | _ -> if neg then mk_not t else t

let normalize (t : term) : term = nnf false t
