(* skolem.ml — see skolem.mli. *)

open Ast

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

(* the base sort of an existential binder, if it carries one *)
let base_of_qty (q : typ option) : base_typ option =
  match q with Some (T_refine { rbase; _ }) -> Some rbase | _ -> None

(* Rewrite the plainly-positive existentials of one hypothesis to fresh constants,
   accumulating (constant, sort) pairs. [sk] tracks whether we are still in a
   positive, quantifier-free-above position where constant-skolemization is sound. *)
let skolemize_hyp (h : term) : term * (var * base_typ) list =
  let acc = ref [] in
  let rec go sk t =
    match t with
    | Tm_quant { qk = Exists; qv; qty; qbody } when sk ->
      (match base_of_qty qty with
       | Some b ->
         let c = fresh_var qv.vname in
         acc := !acc @ [ (c, b) ];
         go sk (Subst.subst_term [ (qv, Tm_var c) ] qbody)
       | None -> Tm_quant { qk = Exists; qv; qty; qbody = go false qbody })
    | Tm_quant q ->
      (* crossing any quantifier disables constant-skolemization below it *)
      Tm_quant { q with qbody = go false q.qbody }
    | Tm_app _ ->
      let head, args = spine t [] in
      (match head, args with
       | Tm_fvar l, [ a ] when l.bname = "l_not" -> mk_not (go false a)
       | Tm_fvar l, [ a; b ] when l.bname = "l_and" -> mk_and (go sk a) (go sk b)
       | Tm_fvar l, [ a; b ] when l.bname = "l_or" -> mk_or (go sk a) (go sk b)
       | Tm_fvar l, [ a; b ] when l.bname = "l_imp" -> mk_imp (go false a) (go sk b)
       | _ -> t)                              (* atom / relation / other application *)
    | _ -> t
  in
  let h' = go true h in
  (h', !acc)

let skolemize (vc : Vc.t) : Vc.t =
  let extra = ref [] in
  let hyps =
    List.map
      (fun h -> let h', consts = skolemize_hyp h in extra := !extra @ consts; h')
      vc.Vc.hyps
  in
  { vc with Vc.hyps = hyps; Vc.scope = vc.Vc.scope @ !extra }
