(* anf.ml — see anf.mli. *)

open Ast

(* an abstract call is a user function/constructor application: neither an
   interpreted operator nor an already-formed relation *)
(* [is_pred b] holds for a bool-returning user function: it is encoded as an SMT
   predicate, so — like interpreted operators and relations — its applications stay
   inline as boolean atoms rather than being hoisted and relationally abstracted. *)
let is_abstract (is_pred : string -> bool) (b : string) : bool =
  not (Smtlib.is_interpreted b) && not (Smtlib.is_relation b) && not (is_pred b)

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
let rec value (is_pred : string -> bool) (t : term) : term * (var * term) list =
  match t with
  | Tm_var _ | Tm_const _ | Tm_fvar _ -> (t, [])
  | Tm_ascribed (e, _) -> value is_pred e
  | Tm_let ({ lb_rec = false; lbs = [ lb ]; _ }, body) ->
    (* a source let in value position: flatten its rhs, then inline the (atomic)
       result into the body and continue *)
    let a1, b1 = value is_pred lb.lb_def in
    let a2, b2 = value is_pred (Subst.subst_term [ (lb.lb_name, a1) ] body) in
    (a2, b1 @ b2)
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head_name head with
     | Some name ->
       let args', binds = atomise is_pred args in
       if is_abstract is_pred name then
         let x = fresh_var "anf" in
         (Tm_var x, binds @ [ (x, mk_app head args') ])
       else
         (* interpreted op, relation, or bool predicate: stays inline over atoms *)
         (mk_app head args', binds)
     | None -> failwith "anf: application head is not a symbol")
  | _ -> failwith "anf: unexpected node in value position"

and atomise (is_pred : string -> bool) (args : term list) : term list * (var * term) list =
  List.fold_left
    (fun (acc_args, acc_binds) a ->
      let a', b = value is_pred a in (acc_args @ [ a' ], acc_binds @ b))
    ([], []) args

(* Normalise a formula: recurse through connectives/quantifiers, and at each atom
   hoist its abstract calls into enclosing lets. *)
let rec form (is_pred : string -> bool) (t : term) : term =
  match t with
  | Tm_quant q -> Tm_quant { q with qbody = form is_pred q.qbody }
  | Tm_ascribed (e, _) -> form is_pred e
  | Tm_app _ ->
    let head, args = spine t [] in
    (match head with
     | Tm_fvar l when Smtlib.is_connective l.bname ->
       mk_app head (List.map (form is_pred) args)    (* args are formulas *)
     | _ ->
       (match head_name head with
        | Some name when is_abstract is_pred name ->
          (* a data-returning abstract call in formula position: lift the whole call *)
          let v, binds = value is_pred t in wrap binds v
        | Some _ ->
          (* a predicate atom (comparison / equality / relation / bool fn): atomise args *)
          let args', binds = atomise is_pred args in wrap binds (mk_app head args')
        | None -> failwith "anf: application head is not a symbol"))
  | Tm_var _ | Tm_const _ | Tm_fvar _ -> t          (* boolean atom *)
  | _ -> failwith "anf: unexpected node in formula position"

let normalize (is_pred : string -> bool) (t : term) : term = form is_pred t

(* The abstract-call bindings hoisted out of a *value* term, in dependency order.
   Used to materialise instantiate! hints (each hoisted call gets an ∃-witness). *)
let hoist (is_pred : string -> bool) (e : term) : (var * term) list = snd (value is_pred e)
