(* infer.ml — see infer.mli. *)

open Unify

exception Type_error of string

(* A type scheme over shapes; the bool marks a *numeric* bound variable. *)
type ischeme = { bound : (Ast.tyvar * bool) list; body : ityp }

(* ===== Ast.typ <-> ityp (refinements erased) ===== *)

let rec erase (t : Ast.typ) : ityp =
  match t with
  | Ast.T_refine { rbase; _ } -> erase_base rbase
  | Ast.T_arrow { adom; acod; _ } -> I_arrow (erase adom, erase acod)
and erase_base (b : Ast.base_typ) : ityp =
  match b with
  | Ast.B_int -> I_int | Ast.B_bool -> I_bool | Ast.B_float -> I_float
  | Ast.B_unit -> I_unit | Ast.B_string -> I_string
  | Ast.B_var tv -> I_var tv
  | Ast.B_app (l, args) -> I_app (l, List.map erase args)

(* ityp -> Ast.typ with trivial refinements. Stray unsolved metas: numeric ⇒ int
   (via zonk), otherwise a fresh generalized type variable (memoized by mid). *)
let reflect (t : ityp) : Ast.typ =
  let memo : (int, Ast.tyvar) Hashtbl.t = Hashtbl.create 8 in
  let rec go t =
    match repr t with
    | I_int -> Ast.mk_base Ast.B_int
    | I_bool -> Ast.mk_base Ast.B_bool
    | I_float -> Ast.mk_base Ast.B_float
    | I_unit -> Ast.mk_base Ast.B_unit
    | I_string -> Ast.mk_base Ast.B_string
    | I_var tv -> Ast.mk_base (Ast.B_var tv)
    | I_app (l, args) -> Ast.mk_base (Ast.B_app (l, List.map go args))
    | I_arrow (a, b) -> Ast.mk_arrow (Ast.fresh_var "_") (go a) (go b)
    | I_meta m ->
      if m.numeric then Ast.mk_base Ast.B_int
      else
        let tv = match Hashtbl.find_opt memo m.mid with
          | Some tv -> tv
          | None -> let tv = Ast.fresh_tyvar "a" in Hashtbl.add memo m.mid tv; tv
        in
        Ast.mk_base (Ast.B_var tv)
  in
  go t

let erase_scheme (ts : Ast.tscheme) : ischeme =
  { bound = List.map (fun tv -> (tv, false)) ts.Ast.ts_vars; body = erase ts.Ast.ts_typ }

let reflect_scheme (sch : ischeme) : Ast.tscheme =
  { Ast.ts_vars = List.map fst sch.bound; ts_typ = reflect sch.body }

(* ===== instantiation / generalization ===== *)

let instantiate (sch : ischeme) : ityp =
  let subs =
    List.map (fun (tv, num) ->
      (tv.Ast.tvid, if num then fresh_numeric_meta () else fresh_meta ()))
      sch.bound
  in
  let rec go t =
    match repr t with
    | I_var tv -> (match List.assoc_opt tv.Ast.tvid subs with Some m -> m | None -> t)
    | I_arrow (a, b) -> I_arrow (go a, go b)
    | I_app (l, args) -> I_app (l, List.map go args)
    | (I_int | I_bool | I_float | I_unit | I_string | I_meta _) as t -> t
  in
  go sch.body

let free_metas_env (lenv : (int * ischeme) list) : meta list =
  List.concat_map (fun (_, sch) -> free_metas sch.body) lenv

(* Generalize [ty] w.r.t. [lenv]: numeric free metas default to int (not generalized);
   the rest become fresh rigid type variables. *)
let generalize (lenv : (int * ischeme) list) (ty : ityp) : ischeme =
  let env_metas = free_metas_env lenv in
  let is_env m = List.exists (fun m' -> m'.mid = m.mid) env_metas in
  let frees = List.filter (fun m -> not (is_env m)) (free_metas ty) in
  let gens =
    List.filter (fun m -> if m.numeric then (default_numeric m; false) else true) frees
  in
  let names = "abcdefghijklmnopqrstuvwxyz" in
  let bound =
    List.mapi (fun i m ->
      let nm = if i < String.length names then String.make 1 names.[i]
               else Printf.sprintf "t%d" i in
      let tv = Ast.fresh_tyvar nm in
      m.sol <- Some (I_var tv);
      (tv, false))
      gens
  in
  { bound; body = zonk ty }

(* ===== global environment / prelude ===== *)

let genv : (string, ischeme) Hashtbl.t = Hashtbl.create 64

let numeric_binop () =
  let tv = Ast.fresh_tyvar "n" in let n = I_var tv in
  { bound = [(tv, true)]; body = I_arrow (n, I_arrow (n, n)) }
let numeric_cmp () =
  let tv = Ast.fresh_tyvar "n" in let n = I_var tv in
  { bound = [(tv, true)]; body = I_arrow (n, I_arrow (n, I_bool)) }
let numeric_unop () =
  let tv = Ast.fresh_tyvar "n" in let n = I_var tv in
  { bound = [(tv, true)]; body = I_arrow (n, n) }
let poly_eq () =
  let tv = Ast.fresh_tyvar "a" in let a = I_var tv in
  { bound = [(tv, false)]; body = I_arrow (a, I_arrow (a, I_bool)) }
let bool_binop = { bound = []; body = I_arrow (I_bool, I_arrow (I_bool, I_bool)) }
let bool_unop  = { bound = []; body = I_arrow (I_bool, I_bool) }
let assert_ty  = { bound = []; body = I_arrow (I_bool, I_unit) }

let setup_prelude () =
  let add name sch = Hashtbl.replace genv name sch in
  List.iter (fun op -> add op (numeric_binop ())) ["+"; "-"; "*"; "/"; "%"];
  List.iter (fun op -> add op (numeric_cmp ())) ["<"; "<="; ">"; ">="];
  add "neg" (numeric_unop ());
  (* eq_lid's base name is "eq"; == and <> come straight from the lexer *)
  List.iter (fun op -> add op (poly_eq ())) ["eq"; "=="; "<>"];
  List.iter (fun op -> add op bool_binop) ["l_and"; "l_or"; "l_imp"; "l_iff"];
  add "l_not" bool_unop;
  add "assert" assert_ty;
  add "assume" assert_ty

(* ===== side tables for hole-filling (keyed by binder/let vid) ===== *)

let binder_typ : (int, ityp) Hashtbl.t = Hashtbl.create 64
let let_scheme : (int, ischeme) Hashtbl.t = Hashtbl.create 64

(* ===== inference ===== *)

let unify_expect (a : ityp) (b : ityp) (msg : string) : unit =
  try unify a b
  with Unify_error (x, y) ->
    raise (Type_error
             (Printf.sprintf "%s: %s vs %s" msg (string_of_ityp x) (string_of_ityp y)))

let shape_of_const : Ast.constant -> ityp = function
  | Ast.C_int _ -> I_int | Ast.C_bool _ -> I_bool | Ast.C_float _ -> I_float
  | Ast.C_unit -> I_unit | Ast.C_string _ -> I_string

let rec infer_term (lenv : (int * ischeme) list) (t : Ast.term) : ityp =
  match t with
  | Ast.Tm_const c -> shape_of_const c
  | Ast.Tm_var v ->
    (match List.assoc_opt v.Ast.vid lenv with
     | Some sch -> instantiate sch
     | None -> raise (Type_error (Printf.sprintf "unbound variable %s" v.Ast.vname)))
  | Ast.Tm_fvar l ->
    (match Hashtbl.find_opt genv l.Ast.bname with
     | Some sch -> instantiate sch
     | None -> raise (Type_error (Printf.sprintf "unbound symbol %s" l.Ast.bname)))
  | Ast.Tm_abs { xbinder; xtyp; xbody } ->
    let dom = match xtyp with Some ty -> erase ty | None -> fresh_meta () in
    Hashtbl.replace binder_typ xbinder.Ast.vid dom;
    let cod = infer_term ((xbinder.Ast.vid, { bound = []; body = dom }) :: lenv) xbody in
    I_arrow (dom, cod)
  | Ast.Tm_app (f, a) ->
    let tf = infer_term lenv f in
    let ta = infer_term lenv a in
    let r = fresh_meta () in
    unify_expect tf (I_arrow (ta, r)) "cannot apply";
    r
  | Ast.Tm_let (lbs, body) ->
    let lenv' = infer_letbindings lenv lbs in
    infer_term lenv' body
  | Ast.Tm_match (scrut, branches) ->
    let ts = infer_term lenv scrut in
    let r = fresh_meta () in
    List.iter (fun (br : Ast.branch) ->
      let lenv2 = infer_pat lenv br.Ast.br_pat ts in
      (match br.Ast.br_when with
       | Some g -> unify_expect (infer_term lenv2 g) I_bool "match guard must be bool"
       | None -> ());
      unify_expect (infer_term lenv2 br.Ast.br_body) r "match branches must agree")
      branches;
    r
  | Ast.Tm_ascribed (e, ty) ->
    let te = infer_term lenv e in
    let it = erase ty in
    unify_expect te it "ascription mismatch";
    it
  | Ast.Tm_quant { qv; qty; qbody; _ } ->
    let dom = match qty with Some ty -> erase ty | None -> fresh_meta () in
    Hashtbl.replace binder_typ qv.Ast.vid dom;
    let tb = infer_term ((qv.Ast.vid, { bound = []; body = dom }) :: lenv) qbody in
    unify_expect tb I_bool "quantifier body must be a proposition";
    I_bool

and infer_letbindings (lenv : (int * ischeme) list) (lbs : Ast.letbindings)
  : (int * ischeme) list =
  let named = List.map (fun lb -> (lb, fresh_meta ())) lbs.Ast.lbs in
  let mono =
    List.map (fun (lb, m) -> (lb.Ast.lb_name.Ast.vid, { bound = []; body = m })) named in
  let def_env = if lbs.Ast.lb_rec then mono @ lenv else lenv in
  List.iter (fun (lb, m) ->
    let td = infer_term def_env lb.Ast.lb_def in
    unify_expect td m "let binding";
    match lb.Ast.lb_scheme with
    | Some s -> unify_expect m (erase s.Ast.ts_typ) "let annotation mismatch"
    | None -> ())
    named;
  let bindings =
    List.map (fun (lb, m) ->
      let sch = match lb.Ast.lb_scheme with
        | Some s -> erase_scheme s
        | None ->
          let sch = generalize lenv m in
          Hashtbl.replace let_scheme lb.Ast.lb_name.Ast.vid sch;
          sch
      in
      (lb.Ast.lb_name.Ast.vid, sch))
      named
  in
  bindings @ lenv

and infer_pat (lenv : (int * ischeme) list) (p : Ast.pat) (ts : ityp)
  : (int * ischeme) list =
  match p with
  | Ast.P_const c -> unify_expect (shape_of_const c) ts "pattern constant"; lenv
  | Ast.P_wild _ -> lenv
  | Ast.P_var v -> (v.Ast.vid, { bound = []; body = ts }) :: lenv
  | Ast.P_cons (l, subs) ->
    let csch = match Hashtbl.find_opt genv l.Ast.bname with
      | Some s -> s
      | None -> raise (Type_error (Printf.sprintf "unknown constructor %s" l.Ast.bname))
    in
    let cty = instantiate csch in
    let rec peel cty subs env =
      match subs with
      | [] -> (cty, env)
      | p :: rest ->
        let arg = fresh_meta () and res = fresh_meta () in
        unify_expect cty (I_arrow (arg, res))
          (Printf.sprintf "constructor %s applied to too many patterns" l.Ast.bname);
        let env' = infer_pat env p arg in
        peel res rest env'
    in
    let (result_ty, env') = peel cty subs lenv in
    unify_expect result_ty ts "constructor result type";
    env'

(* ===== top level ===== *)

let process_top_let (lbs : Ast.letbindings) : unit =
  let named = List.map (fun lb -> (lb, fresh_meta ())) lbs.Ast.lbs in
  let mono =
    List.map (fun (lb, m) -> (lb.Ast.lb_name.Ast.vid, { bound = []; body = m })) named in
  let def_env = if lbs.Ast.lb_rec then mono else [] in
  List.iter (fun (lb, m) ->
    let td = infer_term def_env lb.Ast.lb_def in
    unify_expect td m "top-level let";
    (match lb.Ast.lb_scheme with
     | Some s -> unify_expect m (erase s.Ast.ts_typ) "let annotation mismatch"
     | None -> ());
    (match Hashtbl.find_opt genv lb.Ast.lb_name.Ast.vname with
     | Some declared -> unify_expect m (instantiate declared) "let does not match its val"
     | None -> ()))
    named;
  List.iter (fun (lb, m) ->
    let name = lb.Ast.lb_name.Ast.vname and vid = lb.Ast.lb_name.Ast.vid in
    let sch = match lb.Ast.lb_scheme with
      | Some s -> erase_scheme s
      | None ->
        (match Hashtbl.find_opt genv name with
         | Some declared -> Hashtbl.replace let_scheme vid declared; declared
         | None -> let sch = generalize [] m in Hashtbl.replace let_scheme vid sch; sch)
    in
    Hashtbl.replace genv name sch)
    named

let rec process_sigelt (se : Ast.sigelt) : unit =
  match se.Ast.sig_el with
  | Ast.Sig_inductive ind ->
    List.iter (fun (dc : Ast.data_con) ->
      Hashtbl.replace genv dc.Ast.dc_name.Ast.bname (erase_scheme dc.Ast.dc_typ))
      ind.Ast.ind_ctors
  | Ast.Sig_val (l, sch) -> Hashtbl.replace genv l.Ast.bname (erase_scheme sch)
  | Ast.Sig_let lbs -> process_top_let lbs
  | Ast.Sig_assume (_, phi) ->
    unify_expect (infer_term [] phi) I_bool "assume must be a proposition"
  | Ast.Sig_pragma (Ast.P_check t | Ast.P_eval t) -> ignore (infer_term [] t)
  | Ast.Sig_pragma _ -> ()
  | Ast.Sig_fail (ses, _) ->
    (* expected to fail: swallow inference errors *)
    (try List.iter process_sigelt ses with Type_error _ | Unify_error _ -> ())

(* ===== hole-filling pass ===== *)

let rec fill_term (t : Ast.term) : Ast.term =
  match t with
  | Ast.Tm_var _ | Ast.Tm_fvar _ | Ast.Tm_const _ -> t
  | Ast.Tm_abs a ->
    let xtyp = match a.Ast.xtyp with
      | Some _ as s -> s
      | None ->
        (match Hashtbl.find_opt binder_typ a.Ast.xbinder.Ast.vid with
         | Some ity -> Some (reflect ity) | None -> None)
    in
    Ast.Tm_abs { a with xtyp; xbody = fill_term a.Ast.xbody }
  | Ast.Tm_app (f, x) -> Ast.Tm_app (fill_term f, fill_term x)
  | Ast.Tm_let (lbs, body) -> Ast.Tm_let (fill_letbindings lbs, fill_term body)
  | Ast.Tm_match (s, brs) ->
    Ast.Tm_match (fill_term s,
      List.map (fun (br : Ast.branch) ->
        { br with Ast.br_when = Option.map fill_term br.Ast.br_when;
                  br_body = fill_term br.Ast.br_body }) brs)
  | Ast.Tm_ascribed (e, ty) -> Ast.Tm_ascribed (fill_term e, ty)
  | Ast.Tm_quant q ->
    let qty = match q.Ast.qty with
      | Some _ as s -> s
      | None ->
        (match Hashtbl.find_opt binder_typ q.Ast.qv.Ast.vid with
         | Some ity -> Some (reflect ity) | None -> None)
    in
    Ast.Tm_quant { q with qty; qbody = fill_term q.Ast.qbody }

and fill_letbindings (lbs : Ast.letbindings) : Ast.letbindings =
  { lbs with Ast.lbs =
      List.map (fun (lb : Ast.letbinding) ->
        let lb_scheme = match lb.Ast.lb_scheme with
          | Some _ as s -> s
          | None ->
            (match Hashtbl.find_opt let_scheme lb.Ast.lb_name.Ast.vid with
             | Some sch -> Some (reflect_scheme sch) | None -> None)
        in
        { lb with Ast.lb_scheme; lb_def = fill_term lb.Ast.lb_def })
        lbs.Ast.lbs }

let rec fill_sigelt (se : Ast.sigelt) : Ast.sigelt =
  let el = match se.Ast.sig_el with
    | Ast.Sig_let lbs -> Ast.Sig_let (fill_letbindings lbs)
    | Ast.Sig_assume (l, phi) -> Ast.Sig_assume (l, fill_term phi)
    | Ast.Sig_pragma (Ast.P_check t) -> Ast.Sig_pragma (Ast.P_check (fill_term t))
    | Ast.Sig_pragma (Ast.P_eval t) -> Ast.Sig_pragma (Ast.P_eval (fill_term t))
    | Ast.Sig_fail (ses, codes) -> Ast.Sig_fail (List.map fill_sigelt ses, codes)
    | other -> other
  in
  { se with Ast.sig_el = el }

let infer_module (m : Ast.modul) : Ast.modul =
  Hashtbl.reset binder_typ;
  Hashtbl.reset let_scheme;
  Hashtbl.reset genv;
  setup_prelude ();
  List.iter process_sigelt m.Ast.mod_decls;
  { m with Ast.mod_decls = List.map fill_sigelt m.Ast.mod_decls }
