(* check.ml — see check.mli.

   Bidirectional refinement checking with selfification. [synth] gives a term the
   most precise type it can ({v:B | v = e} singletons for constants, variables and
   applications); [check] pushes an expected type inward; [subtype] turns a
   refinement subtyping obligation {x:B|φ} <: {y:B|ψ} into a Vc. Base shapes are
   guaranteed consistent by prior inference, so [subtype] only produces refinement
   implications (and structural obligations for function types). *)

open Ast

exception Check_error of string

(* ===== small helpers ===== *)

let is_true (t : term) : bool = match t with Tm_const (C_bool true) -> true | _ -> false

let base_of_typ (t : typ) : base_typ option =
  match t with T_refine { rbase; _ } -> Some rbase | T_arrow _ -> None

let base_of_const : constant -> base_typ = function
  | C_int _ -> B_int | C_bool _ -> B_bool | C_float _ -> B_float
  | C_unit -> B_unit | C_string _ -> B_string

(* {v:B | v = e} for a base type; functions are returned unchanged. *)
let selfify (t : typ) (e : term) : typ =
  match t with
  | T_refine { rbase; _ } ->
    let w = fresh_var "v" in
    T_refine { rv = w; rbase; rphi = mk_eq (Tm_var w) e }
  | T_arrow _ -> t

let singleton (b : base_typ) (e : term) : typ =
  let w = fresh_var "v" in
  T_refine { rv = w; rbase = b; rphi = mk_eq (Tm_var w) e }

let rec head_spine (t : term) (acc : term list) : term * term list =
  match t with
  | Tm_app (f, a) -> head_spine f (a :: acc)
  | _ -> (t, acc)

(* ===== typing context ===== *)

type binding = B_typed of var * typ | B_hyp of term
type env = binding list                       (* innermost first *)

let rec lookup (env : env) (x : var) : typ option =
  match env with
  | [] -> None
  | B_typed (y, t) :: rest -> if y.vid = x.vid then Some t else lookup rest x
  | B_hyp _ :: rest -> lookup rest x

(* Flatten Γ (innermost-first) into a VC scope + hypotheses, in source order. *)
let to_scope_hyps (env : env) : (var * base_typ) list * term list =
  List.fold_left
    (fun (scope, hyps) b ->
      match b with
      | B_typed (x, T_refine { rv; rbase; rphi }) ->
        let phi = Subst.subst_term [ (rv, Tm_var x) ] rphi in
        (scope @ [ (x, rbase) ], if is_true phi then hyps else hyps @ [ phi ])
      | B_typed (_, T_arrow _) -> (scope, hyps)   (* higher-order: not first-order *)
      | B_hyp p -> (scope, if is_true p then hyps else hyps @ [ p ]))
    ([], []) (List.rev env)

(* ===== global signature + module axioms ===== *)

let genv : (string, tscheme) Hashtbl.t = Hashtbl.create 64
let module_axioms : term list ref = ref []

let cur_range : range ref = ref dummy_range
let cur_reason : string ref = ref "subtyping"

let mk_vc (env : env) (goal : term) : Vc.t list =
  if is_true goal then []
  else
    let scope, hyps = to_scope_hyps env in
    [ { Vc.decls = []; axioms = !module_axioms; scope; hyps; goal;
        range = !cur_range; reason = !cur_reason } ]

(* interpreted operators: synthesized from their operands, not from [genv] *)
let arith_ops = [ "+"; "-"; "*"; "/"; "%"; "neg" ]
let bool_ops  = [ "<"; "<="; ">"; ">="; "=="; "<>"; "eq"; "l_and"; "l_or"; "l_imp"; "l_iff"; "l_not" ]
let is_interpreted (b : string) : bool = List.mem b arith_ops || List.mem b bool_ops

let peel_arrows (ty : typ) (n : int) : (var * typ) list * typ =
  let rec go ty n =
    if n = 0 then ([], ty)
    else match ty with
      | T_arrow { abinder; adom; acod } ->
        let doms, cod = go acod (n - 1) in
        ((abinder, adom) :: doms, cod)
      | T_refine _ -> raise (Check_error "applied to too many arguments")
  in
  go ty n

let merge_binds (a : (tyvar * typ) list) (b : (tyvar * typ) list) : (tyvar * typ) list =
  List.fold_left
    (fun acc (tv, ty) ->
      if List.exists (fun (tv', _) -> tv'.tvid = tv.tvid) acc then acc else (tv, ty) :: acc)
    a b

(* ===== the checker ===== *)

let rec subtype (env : env) (s : typ) (t : typ) : Vc.t list =
  match s, t with
  | T_refine rs, T_refine rt ->
    if is_true rt.rphi then []
    else begin
      let w = fresh_var "v" in
      let phi = Subst.subst_term [ (rs.rv, Tm_var w) ] rs.rphi in
      let psi = Subst.subst_term [ (rt.rv, Tm_var w) ] rt.rphi in
      let env' = B_typed (w, mk_base rs.rbase) :: env in
      let env'' = if is_true phi then env' else B_hyp phi :: env' in
      mk_vc env'' psi
    end
  | T_arrow as_, T_arrow at ->
    let dom_vcs = subtype env at.adom as_.adom in           (* contravariant *)
    let z = fresh_var "z" in
    let t1 = Subst.subst_typ [ (as_.abinder, Tm_var z) ] as_.acod in
    let t2 = Subst.subst_typ [ (at.abinder, Tm_var z) ] at.acod in
    dom_vcs @ subtype (B_typed (z, at.adom) :: env) t1 t2
  | _ -> raise (Check_error "subtype: base/function mismatch")

and synth (env : env) (e : term) : typ * Vc.t list =
  match e with
  | Tm_const c -> (singleton (base_of_const c) e, [])
  | Tm_var x ->
    (match lookup env x with
     | Some ty -> (selfify ty e, [])
     | None -> raise (Check_error (Printf.sprintf "unbound variable %s" x.vname)))
  | Tm_fvar l ->
    (match Hashtbl.find_opt genv l.bname with
     | Some sch -> (sch.ts_typ, [])
     | None -> raise (Check_error (Printf.sprintf "unbound symbol %s" l.bname)))
  | Tm_app _ ->
    let head, args = head_spine e [] in
    synth_app env head args e
  | Tm_ascribed (e0, ty) ->
    let s, v = synth env e0 in
    (ty, v @ subtype env s ty)
  | Tm_let (lbs, body) ->
    let env', v = extend_lets env lbs in
    let ty, v2 = synth env' body in
    (ty, v @ v2)
  | Tm_quant _ -> (t_bool, [])            (* a proposition *)
  | Tm_abs _ -> raise (Check_error "cannot synthesize a function; annotation required")
  | Tm_match _ -> raise (Check_error "cannot synthesize a match; expected type required")

and synth_app (env : env) (head : term) (args : term list) (whole : term) : typ * Vc.t list =
  match head with
  | Tm_fvar l when lid_eq l assert_lid ->
    (match args with
     | [ phi ] -> (t_unit, mk_vc env phi)
     | _ -> raise (Check_error "assert expects a single argument"))
  | Tm_fvar l when lid_eq l assume_lid -> (t_unit, [])
  | Tm_fvar l when is_interpreted l.bname ->
    let arg_ts = List.map (synth env) args in
    let vcs = List.concat_map snd arg_ts in
    let b =
      if List.mem l.bname bool_ops then B_bool
      else match arg_ts with
        | (t0, _) :: _ -> (match base_of_typ t0 with Some b -> b | None -> B_int)
        | [] -> B_int
    in
    (singleton b whole, vcs)
  | Tm_fvar l ->
    (match Hashtbl.find_opt genv l.bname with
     | Some sch -> synth_declared_app env sch args whole
     | None -> raise (Check_error (Printf.sprintf "unbound symbol %s" l.bname)))
  | Tm_var x ->
    (* a locally-bound function: rec/mutual self-reference or a let-bound lambda *)
    (match lookup env x with
     | Some ty -> synth_declared_app env { ts_vars = []; ts_typ = ty } args whole
     | None -> raise (Check_error (Printf.sprintf "unbound variable %s" x.vname)))
  | _ -> raise (Check_error (Printf.sprintf "application head is not a symbol: %s" (string_of_term head)))

and synth_declared_app (env : env) (sch : tscheme) (args : term list) (whole : term)
  : typ * Vc.t list =
  let arg_ts = List.map (synth env) args in
  let doms, cod = peel_arrows sch.ts_typ (List.length args) in
  (* recover the type-variable instantiation by matching declared domains against
     the actual argument types *)
  let tybinds =
    List.fold_left2
      (fun acc (_, si) (ti, _) ->
        let b = try Shape.match_typ si ti with Shape.Match_error _ -> [] in
        merge_binds acc b)
      [] doms arg_ts
  in
  (* check each argument against its (tyvar- and prior-arg-substituted) domain *)
  let rec go doms args arg_ts tsub vcs =
    match doms, args, arg_ts with
    | [], [], [] -> (vcs, tsub)
    | (x, si) :: ds, e :: es, (ti, vt) :: ats ->
      let si' = Subst.subst_typ tsub (Subst.subst_tyvars tybinds si) in
      let vc = subtype env ti si' in
      go ds es ats ((x, e) :: tsub) (vcs @ vt @ vc)
    | _ -> raise (Check_error "argument arity mismatch")
  in
  let vcs, tsub = go doms args arg_ts [] [] in
  let cod' = Subst.subst_typ tsub (Subst.subst_tyvars tybinds cod) in
  let result = match base_of_typ cod' with Some _ -> selfify cod' whole | None -> cod' in
  (result, vcs)

and check (env : env) (e : term) (t : typ) : Vc.t list =
  match e, t with
  | Tm_abs { xbinder; xbody; _ }, T_arrow { abinder; adom; acod } ->
    let acod' = Subst.subst_typ [ (abinder, Tm_var xbinder) ] acod in
    check (B_typed (xbinder, adom) :: env) xbody acod'
  | Tm_let (lbs, body), _ ->
    let env', v = extend_lets env lbs in
    v @ check env' body t
  | Tm_match (scrut, brs), _ ->
    let ts, v0 = synth env scrut in
    v0 @ List.concat_map (check_branch env scrut ts t) brs
  | _ ->
    let s, v = synth env e in
    v @ subtype env s t

and check_branch (env : env) (scrut : term) (ts : typ) (t : typ) (br : branch) : Vc.t list =
  let env', path = bind_pattern env scrut ts br.br_pat in
  let env'' = match path with Some p -> B_hyp p :: env' | None -> env' in
  let env''' = match br.br_when with Some g -> B_hyp g :: env'' | None -> env'' in
  check env''' br.br_body t

and bind_pattern (env : env) (scrut : term) (ts : typ) (p : pat) : env * term option =
  match p with
  | P_wild _ -> (env, None)
  | P_var v -> (B_typed (v, ts) :: env, None)
  | P_const c -> (env, Some (mk_eq scrut (Tm_const c)))
  | P_cons (l, subs) ->
    (match Hashtbl.find_opt genv l.bname with
     | None -> raise (Check_error (Printf.sprintf "unknown constructor %s" l.bname))
     | Some sch ->
       let doms, cod = peel_arrows sch.ts_typ (List.length subs) in
       let tybinds = try Shape.match_typ cod ts with Shape.Match_error _ -> [] in
       let env' =
         List.fold_left2
           (fun env (_, si) sub ->
             match sub with
             | P_var v -> B_typed (v, Subst.subst_tyvars tybinds si) :: env
             | P_wild _ -> env
             | _ -> raise (Check_error "nested constructor patterns are unsupported in v1"))
           env doms subs
       in
       (env', None))

and extend_lets (env : env) (lbs : letbindings) : env * Vc.t list =
  let named =
    List.map
      (fun lb -> match lb.lb_scheme with
         | Some sch -> (lb, sch)
         | None -> raise (Check_error "let binding is missing its inferred scheme"))
      lbs.lbs
  in
  let add env0 = List.fold_left (fun env (lb, sch) -> B_typed (lb.lb_name, sch.ts_typ) :: env) env0 named in
  let def_env = if lbs.lb_rec then add env else env in
  let vcs = List.concat_map (fun (lb, sch) -> check def_env lb.lb_def sch.ts_typ) named in
  (add env, vcs)

(* ===== module entry point ===== *)

let check_module (m : modul) : Vc.t list =
  Hashtbl.reset genv;
  module_axioms := [];
  (* pass 1: populate the global signature and collect axioms *)
  List.iter
    (fun se ->
      match se.sig_el with
      | Sig_inductive ind ->
        List.iter (fun dc -> Hashtbl.replace genv dc.dc_name.bname dc.dc_typ) ind.ind_ctors
      | Sig_val (l, sch) -> Hashtbl.replace genv l.bname sch
      | Sig_let lbs ->
        List.iter
          (fun lb -> match lb.lb_scheme with
             | Some sch -> Hashtbl.replace genv lb.lb_name.vname sch
             | None -> ())
          lbs.lbs
      | Sig_assume (_, phi) -> module_axioms := !module_axioms @ [ phi ]
      | _ -> ())
    m.mod_decls;
  (* pass 2: generate VCs from definitions and #check pragmas *)
  List.concat_map
    (fun se ->
      cur_range := se.sig_rng;
      match se.sig_el with
      | Sig_let lbs ->
        (* bind the whole group's names so rec/mutual references resolve; these are
           function-typed, so [to_scope_hyps] keeps them out of the VC scope *)
        let named =
          List.filter_map
            (fun lb -> match lb.lb_scheme with Some sch -> Some (lb, sch) | None -> None)
            lbs.lbs
        in
        let env0 =
          if lbs.lb_rec then
            List.fold_left (fun env (lb, sch) -> B_typed (lb.lb_name, sch.ts_typ) :: env) [] named
          else []
        in
        List.concat_map
          (fun (lb, sch) ->
            cur_reason := Printf.sprintf "definition of %s" lb.lb_name.vname;
            check env0 lb.lb_def sch.ts_typ)
          named
      | Sig_pragma (P_check t) -> cur_reason := "#check"; snd (synth [] t)
      | _ -> [])
    m.mod_decls
