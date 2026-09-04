(* relabs.ml — see relabs.mli. *)

open Ast

let is_abstract (b : string) : bool =
  not (Smtlib.is_interpreted b) && not (Smtlib.is_relation b)

let head_name (h : term) : string option =
  match h with Tm_fvar l -> Some l.bname | Tm_var v -> Some v.vname | _ -> None

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

(* Is [inner] an equality that pins the just-introduced result [x] to some other
   term [t]?  Recognises  [x = t]  and  [t = x]  and returns [Some t].

   The [x ∉ fv(t)] guard is essential: it is what makes it sound to drop the binder
   and substitute [t] for [x] in the relation.  If [x] occurred in [t] the equality
   would constrain [x] recursively and could not be eliminated.  In practice [t] is
   already an atom (ANF atomises an equality's operands), but the guard keeps the
   rewrite correct for any [t]. *)
let pinned_to (x : var) (inner : term) : term option =
  match spine inner [] with
  | Tm_fvar l, [ a; b ] when l.bname = "eq" || l.bname = "==" ->
    let is_x = function Tm_var v -> v.vid = x.vid | _ -> false in
    let free_x t = List.exists (fun v -> v.vid = x.vid) (Subst.free_vars_term t) in
    if is_x a && not (free_x b) then Some b
    else if is_x b && not (free_x a) then Some a
    else None
  | _ -> None

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
  let rel t = mk_app (Tm_fvar (lid_of_str (Axioms.rel_name fname))) (args' @ [ t ]) in
  let inner = relabs ret_sort is_pos body in
  match pinned_to x inner with
  | Some t ->
    (* Peephole: the result of this call is immediately pinned to a term [t]
       (selfification [v = f args], a match discriminator [scrut = C fields], or a
       definitional-equation leaf).  Emit the bare literal [f_rel(args, t)] instead of
       quantifying over the fresh result — shorter, and it names the result directly.

       - Negative position: [∃x. f_rel(args,x) ∧ x = t] ≡ [f_rel(args,t)] exactly
         (the one-point rule); no assumptions needed.
       - Positive position: [∀x. f_rel(args,x) ⇒ x = t] is *weaker* than [f_rel(args,t)]
         — the literal additionally asserts the relation is inhabited at [args].  Using
         it is a deliberate *strengthening*, sound because Caml* functions and
         constructors are total: the applied value exists and the source pins it to [t].
         This is the same pointwise totality that Smt.materialization injects as
         [∃v. f_rel(args,v)]; asserting it here prunes the spurious empty-relation
         models the over-approximation would otherwise admit (so it can also turn a
         spurious counterexample into a proof). *)
    rel t
  | None ->
    (* General case: the result flows into a larger formula (a disequality, a nested
       call, the negated goal, …), so keep the sound over-approximating quantifier. *)
    let ap = rel (Tm_var x) in
    let qty = Some (mk_base (ret_sort fname)) in
    if is_pos then Tm_quant { qk = Forall; qv = x; qty; qbody = mk_imp ap inner }
    else Tm_quant { qk = Exists; qv = x; qty; qbody = mk_and ap inner }

let transform (ret_sort : string -> base_typ) (t : term) : term = relabs ret_sort true t
let transform_neg (ret_sort : string -> base_typ) (t : term) : term = relabs ret_sort false t
