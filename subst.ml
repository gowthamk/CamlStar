(* subst.ml — see subst.mli. *)

open Ast

exception Subst_error of string

(* ===== term-for-term substitution (keyed by vid) =====
   Capture-avoiding by freshening every binder as we descend. *)

type tsub = (int * term) list

let rec tm_term (s : tsub) (t : term) : term =
  match t with
  | Tm_var v -> (match List.assoc_opt v.vid s with Some t' -> t' | None -> t)
  | Tm_fvar _ | Tm_const _ -> t
  | Tm_abs { xbinder; xtyp; xbody } ->
    let x' = fresh_var xbinder.vname in
    let s' = (xbinder.vid, Tm_var x') :: s in
    (* the binder's own type annotation is not in the scope of the binder *)
    Tm_abs { xbinder = x'; xtyp = Option.map (tm_typ s) xtyp; xbody = tm_term s' xbody }
  | Tm_app (f, a) -> Tm_app (tm_term s f, tm_term s a)
  | Tm_let (lbs, body) ->
    let lbs', s_body = tm_letbindings s lbs in
    Tm_let (lbs', tm_term s_body body)
  | Tm_match (scrut, brs) -> Tm_match (tm_term s scrut, List.map (tm_branch s) brs)
  | Tm_ascribed (e, ty) -> Tm_ascribed (tm_term s e, tm_typ s ty)
  | Tm_quant { qk; qv; qty; qbody } ->
    let v' = fresh_var qv.vname in
    let s' = (qv.vid, Tm_var v') :: s in
    Tm_quant { qk; qv = v'; qty = Option.map (tm_typ s) qty; qbody = tm_term s' qbody }

and tm_typ (s : tsub) (t : typ) : typ =
  match t with
  | T_refine { rv; rbase; rphi } ->
    let v' = fresh_var rv.vname in
    let s' = (rv.vid, Tm_var v') :: s in
    T_refine { rv = v'; rbase = tm_base s rbase; rphi = tm_term s' rphi }
  | T_arrow { abinder; adom; acod } ->
    let x' = fresh_var abinder.vname in
    let s' = (abinder.vid, Tm_var x') :: s in
    T_arrow { abinder = x'; adom = tm_typ s adom; acod = tm_typ s' acod }

and tm_base (s : tsub) (b : base_typ) : base_typ =
  match b with
  | B_app (l, args) -> B_app (l, List.map (tm_typ s) args)
  | _ -> b

and tm_scheme (s : tsub) (sch : tscheme) : tscheme =
  { sch with ts_typ = tm_typ s sch.ts_typ }

and tm_branch (s : tsub) (br : branch) : branch =
  let pat', s' = tm_pat s br.br_pat in
  { br_pat = pat';
    br_when = Option.map (tm_term s') br.br_when;
    br_body = tm_term s' br.br_body }

and tm_pat (s : tsub) (p : pat) : pat * tsub =
  match p with
  | P_const _ -> (p, s)
  | P_var v  -> let v' = fresh_var v.vname in (P_var v',  (v.vid, Tm_var v') :: s)
  | P_wild v -> let v' = fresh_var v.vname in (P_wild v', (v.vid, Tm_var v') :: s)
  | P_cons (l, subs) ->
    let subs', s' =
      List.fold_left (fun (acc, s) p -> let p', s' = tm_pat s p in (p' :: acc, s'))
        ([], s) subs
    in
    (P_cons (l, List.rev subs'), s')

and tm_letbindings (s : tsub) (lbs : letbindings) : letbindings * tsub =
  (* Freshen every bound name; those bindings scope over the body (and, when
     [rec], over the definitions as well). *)
  let renamed = List.map (fun lb -> (lb, fresh_var lb.lb_name.vname)) lbs.lbs in
  let s_body =
    List.fold_left (fun s (lb, nv) -> (lb.lb_name.vid, Tm_var nv) :: s) s renamed in
  let s_def = if lbs.lb_rec then s_body else s in
  let lbs' =
    List.map (fun (lb, nv) ->
      { lb_name = nv;
        lb_scheme = Option.map (tm_scheme s) lb.lb_scheme;
        lb_def = tm_term s_def lb.lb_def;
        lb_measure = Option.map (tm_measure s_def) lb.lb_measure })
      renamed
  in
  ({ lbs with lbs = lbs' }, s_body)

and tm_measure (s : tsub) (d : decreases) : decreases =
  match d with
  | Dec_lex ts -> Dec_lex (List.map (tm_term s) ts)
  | Dec_wf (a, b) -> Dec_wf (tm_term s a, tm_term s b)

let subst_term (pairs : (var * term) list) (t : term) : term =
  tm_term (List.map (fun (v, tm) -> (v.vid, tm)) pairs) t

let subst_typ (pairs : (var * term) list) (t : typ) : typ =
  tm_typ (List.map (fun (v, tm) -> (v.vid, tm)) pairs) t

let freshen_term (t : term) : term = tm_term [] t
let freshen_typ  (t : typ)  : typ  = tm_typ  [] t

(* ===== type-for-tyvar substitution (keyed by tvid) ===== *)

type tysub = (int * typ) list

let rec ty_typ (s : tysub) (t : typ) : typ =
  match t with
  | T_refine { rv; rbase = B_var tv; rphi } when List.mem_assoc tv.tvid s ->
    (* base-position replacement: merge the local refinement with the target's *)
    merge_refine rv (ty_term s rphi) (List.assoc tv.tvid s)
  | T_refine { rv; rbase; rphi } ->
    T_refine { rv; rbase = ty_base s rbase; rphi = ty_term s rphi }
  | T_arrow { abinder; adom; acod } ->
    T_arrow { abinder; adom = ty_typ s adom; acod = ty_typ s acod }

and merge_refine (rv : var) (phi : term) (repl : typ) : typ =
  match repl with
  | T_refine { rv = w; rbase = b'; rphi = psi } ->
    let psi' = subst_term [ (w, Tm_var rv) ] psi in
    let conj = match phi, psi' with
      | Tm_const (C_bool true), p | p, Tm_const (C_bool true) -> p
      | _ -> mk_and phi psi'
    in
    T_refine { rv; rbase = b'; rphi = conj }
  | T_arrow _ ->
    (match phi with
     | Tm_const (C_bool true) -> repl
     | _ -> raise (Subst_error "cannot refine a function type"))

and ty_base (s : tysub) (b : base_typ) : base_typ =
  match b with
  | B_app (l, args) -> B_app (l, List.map (ty_typ s) args)
  | _ -> b

and ty_term (s : tysub) (t : term) : term =
  (* tyvars occur inside terms only within embedded type annotations *)
  match t with
  | Tm_var _ | Tm_fvar _ | Tm_const _ -> t
  | Tm_abs a -> Tm_abs { a with xtyp = Option.map (ty_typ s) a.xtyp; xbody = ty_term s a.xbody }
  | Tm_app (f, x) -> Tm_app (ty_term s f, ty_term s x)
  | Tm_let (lbs, body) ->
    let lbs' =
      { lbs with lbs =
          List.map (fun lb ->
            { lb with lb_scheme = Option.map (ty_scheme s) lb.lb_scheme;
                      lb_def = ty_term s lb.lb_def;
                      lb_measure = Option.map (ty_measure s) lb.lb_measure })
            lbs.lbs }
    in
    Tm_let (lbs', ty_term s body)
  | Tm_match (scrut, brs) ->
    Tm_match (ty_term s scrut,
      List.map (fun br ->
        { br with br_when = Option.map (ty_term s) br.br_when;
                  br_body = ty_term s br.br_body })
        brs)
  | Tm_ascribed (e, ty) -> Tm_ascribed (ty_term s e, ty_typ s ty)
  | Tm_quant q -> Tm_quant { q with qty = Option.map (ty_typ s) q.qty; qbody = ty_term s q.qbody }

and ty_scheme (s : tysub) (sch : tscheme) : tscheme =
  (* the scheme's own bound tyvars shadow the substitution *)
  let s' = List.filter
      (fun (tvid, _) -> not (List.exists (fun tv -> tv.tvid = tvid) sch.ts_vars)) s in
  { sch with ts_typ = ty_typ s' sch.ts_typ }

and ty_measure (s : tysub) (d : decreases) : decreases =
  match d with
  | Dec_lex ts -> Dec_lex (List.map (ty_term s) ts)
  | Dec_wf (a, b) -> Dec_wf (ty_term s a, ty_term s b)

let subst_tyvars (pairs : (tyvar * typ) list) (t : typ) : typ =
  ty_typ (List.map (fun (tv, ty) -> (tv.tvid, ty)) pairs) t

(* ===== free variables ===== *)

let rec fv_term (bound : int list) (acc : var list) (t : term) : var list =
  match t with
  | Tm_var v -> if List.mem v.vid bound then acc else v :: acc
  | Tm_fvar _ | Tm_const _ -> acc
  | Tm_abs { xbinder; xtyp; xbody } ->
    let acc = match xtyp with Some ty -> fv_typ bound acc ty | None -> acc in
    fv_term (xbinder.vid :: bound) acc xbody
  | Tm_app (f, a) -> fv_term bound (fv_term bound acc f) a
  | Tm_let (lbs, body) ->
    let names = List.map (fun lb -> lb.lb_name.vid) lbs.lbs in
    let def_bound = if lbs.lb_rec then names @ bound else bound in
    let acc =
      List.fold_left (fun acc lb ->
        let acc = match lb.lb_scheme with Some s -> fv_typ bound acc s.ts_typ | None -> acc in
        fv_term def_bound acc lb.lb_def)
        acc lbs.lbs
    in
    fv_term (names @ bound) acc body
  | Tm_match (scrut, brs) ->
    List.fold_left (fun acc br ->
      let pbound = pat_binders br.br_pat @ bound in
      let acc = match br.br_when with Some g -> fv_term pbound acc g | None -> acc in
      fv_term pbound acc br.br_body)
      (fv_term bound acc scrut) brs
  | Tm_ascribed (e, ty) -> fv_typ bound (fv_term bound acc e) ty
  | Tm_quant { qv; qty; qbody; _ } ->
    let acc = match qty with Some ty -> fv_typ bound acc ty | None -> acc in
    fv_term (qv.vid :: bound) acc qbody

and fv_typ (bound : int list) (acc : var list) (t : typ) : var list =
  match t with
  | T_refine { rv; rbase; rphi } -> fv_term (rv.vid :: bound) (fv_base bound acc rbase) rphi
  | T_arrow { abinder; adom; acod } ->
    fv_typ (abinder.vid :: bound) (fv_typ bound acc adom) acod

and fv_base (bound : int list) (acc : var list) (b : base_typ) : var list =
  match b with
  | B_app (_, args) -> List.fold_left (fv_typ bound) acc args
  | _ -> acc

and pat_binders (p : pat) : int list =
  match p with
  | P_const _ -> []
  | P_var v | P_wild v -> [ v.vid ]
  | P_cons (_, subs) -> List.concat_map pat_binders subs

let dedup_vars (vs : var list) : var list =
  let seen = Hashtbl.create 16 in
  List.filter (fun v -> if Hashtbl.mem seen v.vid then false else (Hashtbl.add seen v.vid (); true))
    vs

let free_vars_term (t : term) : var list = dedup_vars (List.rev (fv_term [] [] t))
let free_vars_typ  (t : typ)  : var list = dedup_vars (List.rev (fv_typ  [] [] t))

(* ===== free type variables ===== *)

let rec ftv_typ (bound : int list) (acc : tyvar list) (t : typ) : tyvar list =
  match t with
  | T_refine { rbase; rphi; _ } -> ftv_term bound (ftv_base bound acc rbase) rphi
  | T_arrow { adom; acod; _ } -> ftv_typ bound (ftv_typ bound acc adom) acod

and ftv_base (bound : int list) (acc : tyvar list) (b : base_typ) : tyvar list =
  match b with
  | B_var tv -> if List.mem tv.tvid bound then acc else tv :: acc
  | B_app (_, args) -> List.fold_left (ftv_typ bound) acc args
  | _ -> acc

and ftv_term (bound : int list) (acc : tyvar list) (t : term) : tyvar list =
  match t with
  | Tm_var _ | Tm_fvar _ | Tm_const _ -> acc
  | Tm_abs a ->
    let acc = match a.xtyp with Some ty -> ftv_typ bound acc ty | None -> acc in
    ftv_term bound acc a.xbody
  | Tm_app (f, x) -> ftv_term bound (ftv_term bound acc f) x
  | Tm_let (lbs, body) ->
    let acc =
      List.fold_left (fun acc lb ->
        let acc = match lb.lb_scheme with
          | Some s ->
            let inner = List.map (fun tv -> tv.tvid) s.ts_vars @ bound in
            ftv_typ inner acc s.ts_typ
          | None -> acc
        in
        ftv_term bound acc lb.lb_def)
        acc lbs.lbs
    in
    ftv_term bound acc body
  | Tm_match (scrut, brs) ->
    List.fold_left (fun acc br ->
      let acc = match br.br_when with Some g -> ftv_term bound acc g | None -> acc in
      ftv_term bound acc br.br_body)
      (ftv_term bound acc scrut) brs
  | Tm_ascribed (e, ty) -> ftv_typ bound (ftv_term bound acc e) ty
  | Tm_quant q ->
    let acc = match q.qty with Some ty -> ftv_typ bound acc ty | None -> acc in
    ftv_term bound acc q.qbody

let dedup_tyvars (vs : tyvar list) : tyvar list =
  let seen = Hashtbl.create 16 in
  List.filter (fun tv -> if Hashtbl.mem seen tv.tvid then false else (Hashtbl.add seen tv.tvid (); true))
    vs

let free_tyvars_typ (t : typ) : tyvar list = dedup_tyvars (List.rev (ftv_typ [] [] t))

(* ===== alpha-equivalence (bound vids matched under a bijection) ===== *)

let rec ae_term (m : (int * int) list) (a : term) (b : term) : bool =
  match a, b with
  | Tm_var x, Tm_var y ->
    (match List.assoc_opt x.vid m with
     | Some ry -> ry = y.vid
     | None -> not (List.exists (fun (_, ry) -> ry = y.vid) m) && x.vid = y.vid)
  | Tm_fvar l1, Tm_fvar l2 -> lid_eq l1 l2
  | Tm_const c1, Tm_const c2 -> c1 = c2
  | Tm_abs a1, Tm_abs a2 ->
    ae_opt_typ m a1.xtyp a2.xtyp
    && ae_term ((a1.xbinder.vid, a2.xbinder.vid) :: m) a1.xbody a2.xbody
  | Tm_app (f1, x1), Tm_app (f2, x2) -> ae_term m f1 f2 && ae_term m x1 x2
  | Tm_let (l1, b1), Tm_let (l2, b2) ->
    (match ae_letbindings m l1 l2 with Some m' -> ae_term m' b1 b2 | None -> false)
  | Tm_match (s1, br1), Tm_match (s2, br2) ->
    ae_term m s1 s2 && List.length br1 = List.length br2 && List.for_all2 (ae_branch m) br1 br2
  | Tm_ascribed (e1, t1), Tm_ascribed (e2, t2) -> ae_term m e1 e2 && ae_typ m t1 t2
  | Tm_quant q1, Tm_quant q2 ->
    q1.qk = q2.qk && ae_opt_typ m q1.qty q2.qty
    && ae_term ((q1.qv.vid, q2.qv.vid) :: m) q1.qbody q2.qbody
  | _ -> false

and ae_typ (m : (int * int) list) (a : typ) (b : typ) : bool =
  match a, b with
  | T_refine r1, T_refine r2 ->
    ae_base m r1.rbase r2.rbase
    && ae_term ((r1.rv.vid, r2.rv.vid) :: m) r1.rphi r2.rphi
  | T_arrow a1, T_arrow a2 ->
    ae_typ m a1.adom a2.adom
    && ae_typ ((a1.abinder.vid, a2.abinder.vid) :: m) a1.acod a2.acod
  | _ -> false

and ae_base (m : (int * int) list) (a : base_typ) (b : base_typ) : bool =
  match a, b with
  | B_int, B_int | B_bool, B_bool | B_float, B_float
  | B_unit, B_unit | B_string, B_string -> true
  | B_var t1, B_var t2 -> t1.tvid = t2.tvid
  | B_app (l1, a1), B_app (l2, a2) ->
    lid_eq l1 l2 && List.length a1 = List.length a2 && List.for_all2 (ae_typ m) a1 a2
  | _ -> false

and ae_opt_typ m o1 o2 =
  match o1, o2 with None, None -> true | Some t1, Some t2 -> ae_typ m t1 t2 | _ -> false

and ae_opt_term m o1 o2 =
  match o1, o2 with None, None -> true | Some t1, Some t2 -> ae_term m t1 t2 | _ -> false

and ae_branch (m : (int * int) list) (br1 : branch) (br2 : branch) : bool =
  match ae_pat m br1.br_pat br2.br_pat with
  | Some m' -> ae_opt_term m' br1.br_when br2.br_when && ae_term m' br1.br_body br2.br_body
  | None -> false

and ae_pat (m : (int * int) list) (p1 : pat) (p2 : pat) : (int * int) list option =
  match p1, p2 with
  | P_const c1, P_const c2 -> if c1 = c2 then Some m else None
  | P_var v1, P_var v2 -> Some ((v1.vid, v2.vid) :: m)
  | P_wild v1, P_wild v2 -> Some ((v1.vid, v2.vid) :: m)
  | P_cons (l1, s1), P_cons (l2, s2) ->
    if lid_eq l1 l2 && List.length s1 = List.length s2 then
      List.fold_left2
        (fun acc p1 p2 -> match acc with None -> None | Some m -> ae_pat m p1 p2)
        (Some m) s1 s2
    else None
  | _ -> None

and ae_letbindings (m : (int * int) list) (l1 : letbindings) (l2 : letbindings)
  : (int * int) list option =
  if l1.lb_rec = l2.lb_rec && List.length l1.lbs = List.length l2.lbs then
    let m' = List.fold_left2 (fun m a b -> (a.lb_name.vid, b.lb_name.vid) :: m) m l1.lbs l2.lbs in
    let def_m = if l1.lb_rec then m' else m in
    if List.for_all2 (fun a b -> ae_term def_m a.lb_def b.lb_def) l1.lbs l2.lbs
    then Some m' else None
  else None

let alpha_equal_term (a : term) (b : term) : bool = ae_term [] a b
let alpha_equal_typ  (a : typ)  (b : typ)  : bool = ae_typ  [] a b
