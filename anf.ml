(* anf.ml — see anf.mli. *)

open Ast

(* an abstract call is a user function/constructor application: neither an
   interpreted operator nor an already-formed relation *)
let is_abstract (b : string) : bool =
  not (Smtlib.is_interpreted b) && not (Smtlib.is_relation b)

(* the callee name of an application head: a top-level symbol (Tm_fvar) or a
   locally-bound function, e.g. a recursive self-reference (Tm_var) *)
let head_name (h : term) : string option =
  match h with Tm_fvar l -> Some l.bname | Tm_var v -> Some v.vname | _ -> None

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

let single_let (x : var) (def : term) (body : term) : term =
  Tm_let ({ lb_rec = false;
            lbs = [ { lb_name = x; lb_scheme = None; lb_def = def; lb_measure = None } ] },
          body)

let wrap (binds : (var * term) list) (body : term) : term =
  List.fold_right (fun (x, def) acc -> single_let x def acc) binds body

(* Atomise a value term: return an atom plus the abstract-call bindings hoisted
   out of it (in dependency order — earlier entries are the outer lets). *)
let rec value (t : term) : term * (var * term) list =
  match t with
  | Tm_var _ | Tm_const _ | Tm_fvar _ -> (t, [])
  | Tm_ascribed (e, _) -> value e
  | Tm_let ({ lb_rec = false; lbs = [ lb ]; _ }, body) ->
    (* a source let in value position: flatten its rhs, then inline the (atomic)
       result into the body and continue *)
    let a1, b1 = value lb.lb_def in
    let a2, b2 = value (Subst.subst_term [ (lb.lb_name, a1) ] body) in
    (a2, b1 @ b2)
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head_name head with
     | Some name ->
       let args', binds = atomise args in
       if is_abstract name then
         let x = fresh_var "anf" in
         (Tm_var x, binds @ [ (x, mk_app head args') ])
       else
         (* interpreted operator (or a stray relation): stays inline over atoms *)
         (mk_app head args', binds)
     | None -> failwith "anf: application head is not a symbol")
  | _ -> failwith "anf: unexpected node in value position"

and atomise (args : term list) : term list * (var * term) list =
  List.fold_left
    (fun (acc_args, acc_binds) a ->
      let a', b = value a in (acc_args @ [ a' ], acc_binds @ b))
    ([], []) args

(* Normalise a formula: recurse through connectives/quantifiers, and at each atom
   hoist its abstract calls into enclosing lets. *)
let rec form (t : term) : term =
  match t with
  | Tm_quant q -> Tm_quant { q with qbody = form q.qbody }
  | Tm_ascribed (e, _) -> form e
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head with
     | Tm_fvar l when Smtlib.is_connective l.bname ->
       mk_app head (List.map form args)              (* args are formulas *)
     | _ ->
       (match head_name head with
        | Some name when is_abstract name ->
          (* a boolean-valued abstract call in formula position: lift the whole call *)
          let v, binds = value t in wrap binds v
        | Some _ ->
          (* a predicate atom (comparison / equality / relation): atomise its args *)
          let args', binds = atomise args in wrap binds (mk_app head args')
        | None -> failwith "anf: application head is not a symbol"))
  | Tm_var _ | Tm_const _ | Tm_fvar _ -> t          (* boolean atom *)
  | _ -> failwith "anf: unexpected node in formula position"

let normalize (t : term) : term = form t
