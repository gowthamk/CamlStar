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

let is_true (t : term) : bool = 
  match t with Tm_const (C_bool true) -> true | _ -> false

let base_of_typ (t : typ) : base_typ option =
  match t with T_refine { rbase; _ } -> Some rbase | T_arrow _ -> None

let base_of_const : constant -> base_typ = function
  | C_int _ -> B_int | C_bool _ -> B_bool | C_float _ -> B_float
  | C_unit -> B_unit | C_string _ -> B_string

(* Strengthen a base type with the fact [v = e], keeping its existing refinement;
   functions are returned unchanged. *)
let selfify (t : typ) (e : term) : typ =
  match t with
  | T_refine { rv; rbase; rphi } ->
    let w = fresh_var "v" in
    let eq = mk_eq (Tm_var w) e in
    let phi = Subst.subst_term [ (rv, Tm_var w) ] rphi in
    let rphi = if is_true phi then eq else mk_and phi eq in
    T_refine { rv = w; rbase; rphi }
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

(* Does a type carry a non-trivial (user-written) refinement anywhere? Used to
   decide whether a let annotation is worth enforcing (an erased inference shape
   has only [true] refinements). *)
let rec has_refinement (t : typ) : bool =
  match t with
  | T_refine { rphi; _ } -> not (is_true rphi)
  | T_arrow { adom; acod; _ } -> has_refinement adom || has_refinement acod

(* the base-typed term variables a binding list introduces, in source order *)
let delta_base_binders (delta : env) : (var * base_typ) list =
  List.filter_map
    (function B_typed (z, T_refine { rbase; _ }) -> Some (z, rbase) | _ -> None)
    (List.rev delta)

(* Existentially close a synthesized type over Δ — the bindings introduced since the
   outer scope (innermost-first). Only the refinement predicate is closed; a base
   type never mentions Δ. [{v:B | φ}] becomes [{v:B | ∃ z1..zn. facts(Δ) ∧ φ}], where
   facts(Δ) are the definitional refinements of Δ's typed binders plus its path/guard
   hypotheses (exactly [to_scope_hyps]'s per-binding extraction, folded into an ∃).
   A function-typed local that escapes cannot be closed (documented v1 limitation). *)
let close_type (delta : env) (t : typ) : typ =
  match t with
  | T_arrow _ ->
    let dvars = List.filter_map (function B_typed (z, _) -> Some z | B_hyp _ -> None) delta in
    let free = Subst.free_vars_typ t in
    if List.exists (fun z -> List.exists (fun v -> v.vid = z.vid) free) dvars then
      raise (Check_error "cannot synthesize a higher-order let/match result that captures local bindings");
    t
  | T_refine { rv; rbase; rphi } ->
    let ordered = List.rev delta in                        (* source order *)
    let facts =
      List.filter_map
        (function
          | B_typed (z, T_refine { rv = w; rphi = chi; _ }) ->
            let f = Subst.subst_term [ (w, Tm_var z) ] chi in
            if is_true f then None else Some f
          | B_typed (_, T_arrow _) -> None
          | B_hyp p -> if is_true p then None else Some p)
        ordered
    in
    let conjuncts = facts @ (if is_true rphi then [] else [ rphi ]) in
    let body = match conjuncts with [] -> mk_true | h :: r -> List.fold_left mk_and h r in
    let fv = Subst.free_vars_term body in
    List.iter
      (function
        | B_typed (z, T_arrow _) when List.exists (fun v -> v.vid = z.vid) fv ->
          raise (Check_error "cannot synthesize a let/match result that captures a local function binding")
        | _ -> ())
      ordered;
    (* quantify each base-typed local that actually escapes into the body *)
    let binders =
      List.filter (fun (z, _) -> List.exists (fun v -> v.vid = z.vid) fv) (delta_base_binders delta)
    in
    let closed = List.fold_right (fun (z, b) acc -> mk_exists z (Some (mk_base b)) acc) binders body in
    T_refine { rv; rbase; rphi = closed }

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
    let delta, v = extend_lets env lbs in
    let ty, v2 = synth (delta @ env) body in
    (close_type delta ty, v @ v2)
  | Tm_match (scrut, brs) ->
    let ts, v0 = synth env scrut in
    let v = fresh_var "v" in
    let base = ref None in
    let disjuncts, vcs =
      List.fold_left
        (fun (ds, vcs) br ->
          let closed, vb = synth_branch env scrut ts br in
          match closed with
          | T_refine { rv; rbase; rphi } ->
            base := Some rbase;
            (ds @ [ Subst.subst_term [ (rv, Tm_var v) ] rphi ], vcs @ vb)
          | T_arrow _ -> raise (Check_error "a match branch has a function type; unsupported in synthesis"))
        ([], v0) brs
    in
    let rbase = match !base with Some b -> b | None -> raise (Check_error "cannot synthesize an empty match") in
    let rphi = match disjuncts with [] -> mk_true | h :: r -> List.fold_left mk_or h r in
    (T_refine { rv = v; rbase; rphi }, vcs)
  | Tm_quant _ -> (t_bool, [])            (* a proposition *)
  | Tm_abs _ -> raise (Check_error "cannot synthesize a function; annotation required")

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
    let delta, v = extend_lets env lbs in
    v @ check (delta @ env) body t
  | Tm_match (scrut, brs), _ ->
    let ts, v0 = synth env scrut in
    v0 @ List.concat_map (check_branch env scrut ts t) brs
  | _ ->
    let s, v = synth env e in
    v @ subtype env s t

and check_branch (env : env) (scrut : term) (ts : typ) (t : typ) (br : branch) : Vc.t list =
  check (branch_delta scrut ts br @ env) br.br_body t

(* Synthesize a branch's type, closed over the branch-local bindings (pattern
   fields, discriminator, guard). Returns [{v:B | ψ}] and the branch's VCs. *)
and synth_branch (env : env) (scrut : term) (ts : typ) (br : branch) : typ * Vc.t list =
  let delta = branch_delta scrut ts br in
  let tbody, v = synth (delta @ env) br.br_body in
  (close_type delta tbody, v)

(* the bindings a branch introduces (innermost-first): pattern fields, then the
   discriminator path condition, then the [when] guard *)
and branch_delta (scrut : term) (ts : typ) (br : branch) : binding list =
  let delta, path = bind_pattern scrut ts br.br_pat in
  let delta = match path with Some p -> B_hyp p :: delta | None -> delta in
  match br.br_when with Some g -> B_hyp g :: delta | None -> delta

(* Bindings (innermost-first) and the discriminator a pattern contributes. *)
and bind_pattern (scrut : term) (ts : typ) (p : pat) : binding list * term option =
  match p with
  | P_wild _ -> ([], None)
  | P_var v -> ([ B_typed (v, ts) ], None)
  | P_const c -> ([], Some (mk_eq scrut (Tm_const c)))
  | P_cons (l, subs) ->
    (match Hashtbl.find_opt genv l.bname with
     | None -> raise (Check_error (Printf.sprintf "unknown constructor %s" l.bname))
     | Some sch ->
       let doms, cod = peel_arrows sch.ts_typ (List.length subs) in
       let tybinds = try Shape.match_typ cod ts with Shape.Match_error _ -> [] in
       (* bind each field to its (tyvar-substituted) type, and collect a term for it
          so we can state the discriminator hypothesis  scrut = C(fields...).  Wild
          fields get a fresh binder too, so they can appear in that equality. *)
       let delta, rev_fields =
         List.fold_left2
           (fun (delta, fields) (_, si) sub ->
             let si' = Subst.subst_tyvars tybinds si in
             match sub with
             | P_var v  -> (B_typed (v, si') :: delta, Tm_var v :: fields)
             | P_wild w -> (B_typed (w, si') :: delta, Tm_var w :: fields)
             | _ -> raise (Check_error "nested constructor patterns are unsupported in v1"))
           ([], []) doms subs
       in
       let disc = mk_eq scrut (mk_app (Tm_fvar l) (List.rev rev_fields)) in
       (delta, Some disc))

(* Elaborate a [let]/[let rec] group, returning the bindings it adds (innermost-first)
   and the VCs from its definitions. Non-recursive base-typed bindings are elaborated
   in *synthesis* mode and bound at their selfified precise type, so intermediate
   facts (name = rhs, and the rhs's own refinement) reach Γ. Function-typed and
   recursive bindings keep check-mode against their scheme. *)
and extend_lets (env : env) (lbs : letbindings) : binding list * Vc.t list =
  let named =
    List.map
      (fun lb -> match lb.lb_scheme with
         | Some sch -> (lb, sch)
         | None -> raise (Check_error "let binding is missing its inferred scheme"))
      lbs.lbs
  in
  if lbs.lb_rec then begin
    let delta = List.map (fun (lb, sch) -> B_typed (lb.lb_name, sch.ts_typ)) named in
    let def_env = delta @ env in
    let vcs = List.concat_map (fun (lb, sch) -> check def_env lb.lb_def sch.ts_typ) named in
    (delta, vcs)
  end else
    let process (lb, sch) =
      match sch.ts_typ with
      | T_arrow _ ->
        (* not first-order and not synthesizable from a bare lambda *)
        (B_typed (lb.lb_name, sch.ts_typ), check env lb.lb_def sch.ts_typ)
      | T_refine _ ->
        (* [synth] already selfifies the selfifiable cases (var/const/application),
           so [s] carries [name = rhs] where that is expressible; a match/let RHS is
           not selfifiable (no [v = match …] term), and its disjunctive/closed type is
           the information we keep. *)
        let s, v = synth env lb.lb_def in
        let v_ann = if has_refinement sch.ts_typ then subtype env s sch.ts_typ else [] in
        (B_typed (lb.lb_name, s), v @ v_ann)
    in
    let results = List.map process named in
    (List.map fst results, List.concat_map snd results)

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
        (* a matching [val] (registered earlier) is the refined spec and wins; only
           supply the shape-only [lb_scheme] when no [val] declared this name *)
        List.iter
          (fun lb -> match lb.lb_scheme with
             | Some sch ->
               if not (Hashtbl.mem genv lb.lb_name.vname) then
                 Hashtbl.replace genv lb.lb_name.vname sch
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
        (* Check each definition against its *declared* type: the refined [val] spec
           in [genv] when one exists, else the inferred (shape-only) [lb_scheme]. The
           reflected [lb_scheme] has erased refinements, so it is only the fallback. *)
        let decl_typ (lb : letbinding) : typ option =
          match Hashtbl.find_opt genv lb.lb_name.vname with
          | Some sch -> Some sch.ts_typ
          | None -> Option.map (fun s -> s.ts_typ) lb.lb_scheme
        in
        let named =
          List.filter_map
            (fun lb -> match decl_typ lb with Some ty -> Some (lb, ty) | None -> None)
            lbs.lbs
        in
        (* bind the group's names so rec/mutual references resolve; they are
           function-typed, so [to_scope_hyps] keeps them out of the VC scope *)
        let env0 =
          if lbs.lb_rec then
            List.fold_left (fun env (lb, ty) -> B_typed (lb.lb_name, ty) :: env) [] named
          else []
        in
        List.concat_map
          (fun (lb, ty) ->
            cur_reason := Printf.sprintf "definition of %s" lb.lb_name.vname;
            check env0 lb.lb_def ty)
          named
      | Sig_pragma (P_check t) -> cur_reason := "#check"; snd (synth [] t)
      | _ -> [])
    m.mod_decls
