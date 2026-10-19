(* cegqi.ml — see cegqi.mli. *)

open Ast

let rec head_spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> head_spine f (a :: acc) | _ -> (t, acc)

(* the symbol an application is headed by: a top-level name, or a local binder for a
   recursive self-call (inside a body the recursive reference is a [Tm_var]) *)
let head_name (h : term) : string option =
  match h with Tm_fvar l -> Some l.bname | Tm_var v -> Some v.vname | _ -> None

let ctor_names (m : modul) : (string, unit) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  List.iter
    (fun se ->
      match se.sig_el with
      | Sig_inductive ind ->
        List.iter (fun c -> Hashtbl.replace tbl c.dc_name.bname ()) ind.ind_ctors
      | _ -> ())
    m.mod_decls;
  tbl

(* a (possibly nullary) constructor application *)
let is_ctor_term (ctors : (string, unit) Hashtbl.t) (t : term) : bool =
  match fst (head_spine t []) with
  | Tm_fvar l -> Hashtbl.mem ctors l.bname
  | _ -> false

(* ===== shapes ===== *)

(* Hypotheses arrive as single propositions, but a branch can contribute a conjunction
   (a lemma call's postcondition alongside its binding), so flatten before scanning. *)
let rec conjuncts (t : term) : term list =
  match head_spine t [] with
  | Tm_fvar l, [ a; b ] when lid_eq l and_lid -> conjuncts a @ conjuncts b
  | _ -> [ t ]

(* The table is keyed by term, not by variable id, so that a shape can belong to an
   application as well as to a variable (a derived shape, [len t ↦ S (len t2)]); the
   first entry for a key wins. *)
let add_shape (sh : (term * term) list) (k : term) (s : term) : (term * term) list =
  if List.exists (fun (k', _) -> Subst.alpha_equal_term k' k) sh then sh else (k, s) :: sh

let shapes (m : modul) (vc : Vc.t) : (term * term) list =
  let ctors = ctor_names m in
  let acc = ref [] in
  let add (v : var) (t : term) = acc := add_shape !acc (Tm_var v) t in
  List.iter
    (fun h ->
      List.iter
        (fun c ->
          match head_spine c [] with
          | Tm_fvar l, [ lhs; rhs ] when lid_eq l eq_lid ->
            (match (lhs, rhs) with
             | Tm_var v, r when is_ctor_term ctors r -> add v r
             | r, Tm_var v when is_ctor_term ctors r -> add v r
             | _ -> ())
          | _ -> ())
        (conjuncts h))
    vc.Vc.hyps;
  List.rev !acc

(* Expand known shapes inside a term, so an equation's constructor patterns have something
   to match: [xs] with [xs = Cons h t] and [t = Nil] becomes [Cons h Nil]. Any subterm
   with an entry is rewritten, a variable or an application alike. Bounded, so a
   pathological cyclic shape cannot loop. *)
let rec apply_shapes (sh : (term * term) list) (fuel : int) (t : term) : term =
  if fuel <= 0 then t
  else
    match List.find_opt (fun (k, _) -> Subst.alpha_equal_term k t) sh with
    | Some (_, s) -> apply_shapes sh (fuel - 1) s
    | None ->
      (match t with
       | Tm_app (f, a) -> Tm_app (apply_shapes sh fuel f, apply_shapes sh fuel a)
       | _ -> t)

(* ===== evaluating a term in the counterexample ===== *)

let eval_in_cex (c : Cex.t) (t : term) : Cex.value option =
  let rec ev (t : term) : Cex.value option =
    match t with
    | Tm_const (C_bool b) -> Some (Cex.Scalar (if b then "true" else "false"))
    | Tm_const (C_int n) -> Some (Cex.Scalar (string_of_int n))
    | Tm_ascribed (e, _) -> ev e
    | Tm_var v ->
      (match List.assoc_opt v.vname c with Some (Cex.Scalar s) -> Some (Cex.Scalar s) | _ -> None)
    | Tm_fvar l ->
      (* a nullary constructor is rendered as its own name in the model *)
      (match List.assoc_opt l.bname c with
       | Some (Cex.Scalar s) -> Some (Cex.Scalar s)
       | _ -> Some (Cex.Scalar l.bname))
    | Tm_app _ ->
      let h, args = head_spine t [] in
      (match head_name h with
       | None -> None
       | Some f ->
         let argvs = List.map ev args in
         if List.exists (fun a -> a = None) argvs then None
         else
           let argvs = List.map (function Some v -> v | None -> assert false) argvs in
           (match List.assoc_opt f c with
            | Some (Cex.Entries es) ->
              (* absent from the map = the relation relates these args to nothing *)
              (match List.find_opt (fun (k, _) -> k = argvs) es with
               | Some (_, v) -> Some v
               | None -> None)
            | _ -> None))
    | _ -> None
  in
  ev t

(* ===== matching an equation's argument patterns ===== *)

(* One-way match of [pats] (containing the equation's binders) against [concrete].
   Non-linear patterns must agree. *)
let match_args (binders : (var * base_typ) list) (pats : term list) (concrete : term list)
  : (var * term) list option =
  let is_binder (v : var) = List.exists (fun (b, _) -> b.vid = v.vid) binders in
  let sub : (var * term) list ref = ref [] in
  let ok = ref true in
  let bind (v : var) (t : term) =
    match List.find_opt (fun (b, _) -> b.vid = v.vid) !sub with
    | Some (_, t') -> if not (Subst.alpha_equal_term t t') then ok := false
    | None -> sub := (v, t) :: !sub
  in
  let rec go (p : term) (c : term) =
    if !ok then
      match (p, c) with
      | Tm_var v, _ when is_binder v -> bind v c
      | Tm_var v, Tm_var w when var_eq v w -> ()
      | Tm_fvar l, Tm_fvar l' when lid_eq l l' -> ()
      | Tm_const a, Tm_const b when a = b -> ()
      | Tm_app (f, a), Tm_app (g, b) -> go f g; go a b
      | _ -> ok := false
  in
  (try List.iter2 go pats concrete with Invalid_argument _ -> ok := false);
  if !ok then Some !sub else None

(* ===== unrolling ===== *)

(* The guard calls of an equation: an ANF'd let shows up as [g = def], and [def] is the
   call the branch inspects (the skill's "guard term"). Branch tests [g = true] carry no
   call and are skipped. *)
let guard_calls (s : (var * term) list) (guards : term list) : term list =
  List.filter_map
    (fun g ->
      match head_spine g [] with
      | Tm_fvar l, [ Tm_var _; def ] when lid_eq l eq_lid ->
        (match def with Tm_const _ -> None | _ -> Some (Subst.subst_term s def))
      | _ -> None)
    guards

(* Inside a function body a recursive call is a [Tm_var] bound by the enclosing [let rec],
   whereas a VC refers to the same function as a top-level [Tm_fvar]. Rewrite unfolded
   right-hand sides accordingly, so a candidate is structurally what the VC would have
   written — otherwise the function's own name looks like a free variable and relabs has no
   [f_rel] to build. *)
let externalize (fns : (string, unit) Hashtbl.t) (t : term) : term =
  let rec go t =
    match t with
    | Tm_var v when Hashtbl.mem fns v.vname -> Tm_fvar (lid_of_str v.vname)
    | Tm_app (f, a) -> Tm_app (go f, go a)
    | Tm_ascribed (e, ty) -> Tm_ascribed (go e, ty)
    | _ -> t
  in
  go t

(* One matched equation, instantiated: its right-hand side and the guard calls on the
   path to that leaf. [guards = []] means the equation is unconditional — its result is
   what the application equals, not one alternative among several. *)
type unfolding = { rhs : term; guards : term list }

let unroll (eqs : Axioms.defeq list) (sh : (term * term) list) (t : term) : unfolding list =
  let h, args = head_spine t [] in
  if args = [] then []
  else
    match head_name h with
    | None -> []
    | Some f ->
      let fns = Hashtbl.create 16 in
      List.iter (fun (e : Axioms.defeq) -> Hashtbl.replace fns e.Axioms.de_fn ()) eqs;
      let args' = List.map (apply_shapes sh 8) args in
      List.filter_map
        (fun (e : Axioms.defeq) ->
          if e.Axioms.de_fn <> f then None
          else
            match match_args e.Axioms.de_binders e.Axioms.de_args args' with
            | None -> None
            | Some s ->
              Some
                { rhs = externalize fns (Subst.subst_term s e.Axioms.de_rhs);
                  guards = List.map (externalize fns) (guard_calls s e.Axioms.de_guards) })
        eqs

(* The flat list of terms an unfolding needs: the right-hand side and the guard calls. *)
let unfolding_terms (u : unfolding) : term list = u.rhs :: u.guards

(* ===== candidate selection ===== *)

let candidates (m : modul) (vc : Vc.t) : term list =
  let eqs = Axioms.definitional_equations m in
  let ctors = ctor_names m in
  (* grows within the round with derived shapes (below) *)
  let sh = ref (shapes m vc) in
  let frontier = Smtlib.ledger_terms vc in
  (* What the query already materialises, by printed form — under both the term as written
     and its shape-expanded form, so an unfolding of a present term is recognised as present:
     [sorted (Cons h2 t2)] is [sorted t] under [t = Cons h2 t2], and the solver already
     relates the two through the hypothesis. The table is consulted as the round's shapes
     grow, so the expanded key follows the derived shapes too. *)
  let present : (string, unit) Hashtbl.t = Hashtbl.create 64 in
  let keys t =
    let w = Ast.string_of_term t and x = Ast.string_of_term (apply_shapes !sh 8 t) in
    if w = x then [ w ] else [ w; x ]
  in
  let is_present t = List.exists (Hashtbl.mem present) (keys t) in
  let mark t = List.iter (fun k -> Hashtbl.replace present k ()) (keys t) in
  List.iter mark frontier;
  (* a candidate must be writable from the VC's scope, else it would render as an unbound
     symbol; a witness that cannot be named here is exactly the lemma case *)
  let in_scope (v : var) = List.exists (fun (s, _) -> s.vid = v.vid) vc.Vc.scope in
  let closed t = List.for_all in_scope (Subst.free_vars_term t) in
  let out = ref [] in
  (* A candidate is only progress if it materialises an application that is not there yet.
     Unfolding a base case can yield a bare constructor ([count n Nil = Z]), which hoists to
     nothing: counting that as progress would keep the loop alive and burn fuel on a VC that
     has in fact saturated. *)
  let adds_something t =
    List.exists (fun sub -> not (is_present sub)) (Smtlib.collect_apps [ t ])
  in
  let add t =
    if (not (is_present t)) && closed t && adds_something t then begin
      mark t;
      (* the subterms it materialises are present from now on, too *)
      List.iter mark (Smtlib.collect_apps [ t ]);
      out := t :: !out
    end
  in
  (* [ledger_terms] is inner-first, so inner applications are unfolded before the outer
     ones that are stuck only because of them. An unfolding whose equation has no guard
     and whose result is a constructor term fixes the application's shape — a *derived*
     shape, [len t ↦ S (len t2)] — recorded at once so that an outer application matching
     on it ([double (len t)]) can unfold in the same round. A guarded result is one
     alternative among several and is not a shape. *)
  List.iter
    (fun app ->
      List.iter
        (fun (u : unfolding) ->
          List.iter add (unfolding_terms u);
          if u.guards = [] && is_ctor_term ctors u.rhs then sh := add_shape !sh app u.rhs)
        (unroll eqs !sh app))
    frontier;
  List.rev !out
