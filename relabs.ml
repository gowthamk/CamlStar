(* relabs.ml — see relabs.mli. *)

open Ast

let is_abstract (b : string) : bool =
  not (Smtlib.is_interpreted b) && not (Smtlib.is_relation b)

let head_name (h : term) : string option =
  match h with Tm_fvar l -> Some l.bname | Tm_var v -> Some v.vname | _ -> None

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

let rec relabs (ret_sort : string -> base_typ) (is_pos : bool) (t : term) : term =
  match t with
  (* let x = f(atoms) in body  =>  forall/exists x. f_rel(atoms, x) op body *)
  | Tm_let ({ lb_rec = false; lbs = [ lb ] }, body) ->
    let x = lb.lb_name in
    let bound = lb.lb_def in
    let head, args = spine bound [] in
    (match head_name head with
     | Some name when args <> [] && is_abstract name ->
       call_to_rel ret_sort is_pos x name args body
     | _ ->
       (* not an abstract call (constant / alias / interpreted): inline and drop *)
       relabs ret_sort is_pos (Subst.subst_term [ (x, bound) ] body))
  | Tm_let _ -> failwith "relabs: expected an ANF single-binding let"
  | Tm_quant q -> Tm_quant { q with qbody = relabs ret_sort is_pos q.qbody }
  | Tm_ascribed (e, _) -> relabs ret_sort is_pos e
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head, args with
     | Tm_fvar l, [ a ] when l.bname = "l_not" ->
       mk_not (relabs ret_sort (not is_pos) a)
     | Tm_fvar l, [ a; b ] when l.bname = "l_and" ->
       mk_and (relabs ret_sort is_pos a) (relabs ret_sort is_pos b)
     | Tm_fvar l, [ a; b ] when l.bname = "l_or" ->
       mk_or (relabs ret_sort is_pos a) (relabs ret_sort is_pos b)
     | Tm_fvar l, [ a; b ] when l.bname = "l_imp" ->
       mk_imp (relabs ret_sort (not is_pos) a) (relabs ret_sort is_pos b)
     | _ -> t)                                      (* atom: args are already atomic *)
  | _ -> t

and call_to_rel ret_sort is_pos (x : var) (fname : string) (args : term list) (body : term) : term =
  let args' = List.map (relabs ret_sort is_pos) args in
  let ap = mk_app (Tm_fvar (lid_of_str (Axioms.rel_name fname))) (args' @ [ Tm_var x ]) in
  let inner = relabs ret_sort is_pos body in
  let qty = Some (mk_base (ret_sort fname)) in
  if is_pos then Tm_quant { qk = Forall; qv = x; qty; qbody = mk_imp ap inner }
  else Tm_quant { qk = Exists; qv = x; qty; qbody = mk_and ap inner }

let transform (ret_sort : string -> base_typ) (t : term) : term = relabs ret_sort true t
let transform_neg (ret_sort : string -> base_typ) (t : term) : term = relabs ret_sort false t
