(* axioms.ml — see axioms.mli. Port of raven/backend/src/smt/axioms.rs. *)

open Ast

let rel_name (s : string) : string = s ^ "_rel"

(* ===== small builders ===== *)

let base_of_typ (t : typ) : base_typ =
  match t with T_refine { rbase; _ } -> rbase
             | T_arrow _ -> failwith "axioms: higher-order field/return not supported"

(* apply an uninterpreted relation/constructor symbol to argument terms *)
let apply (name : string) (args : term list) : term =
  mk_app (Tm_fvar (lid_of_str name)) args

let sorted_quant (qk : quantifier) (binders : (var * base_typ) list) (body : term) : term =
  List.fold_right
    (fun (v, b) acc -> Tm_quant { qk; qv = v; qty = Some (mk_base b); qbody = acc })
    binders body

let forall_sorted = sorted_quant Forall

let neq a b = mk_not (mk_eq a b)

(* input sorts and result sort of a constructor from its declared arrow type *)
let rec ctor_sig (ty : typ) : base_typ list * base_typ =
  match ty with
  | T_arrow { adom; acod; _ } ->
    let ins, out = ctor_sig acod in
    (base_of_typ adom :: ins, out)
  | T_refine { rbase; _ } -> ([], rbase)

(* ===== the three datatype axiom shapes ===== *)

(* ∀ in.., r1, r2. (R(in..,r1) ∧ R(in..,r2)) ⇒ r1 = r2 *)
let functionality (rel : string) (inputs : base_typ list) (output : base_typ) : term =
  let ins = List.map (fun b -> (fresh_var "in", b)) inputs in
  let r1 = fresh_var "r1" and r2 = fresh_var "r2" in
  let in_terms = List.map (fun (v, _) -> Tm_var v) ins in
  let a1 = apply rel (in_terms @ [ Tm_var r1 ]) in
  let a2 = apply rel (in_terms @ [ Tm_var r2 ]) in
  forall_sorted (ins @ [ (r1, output); (r2, output) ])
    (mk_imp (mk_and a1 a2) (mk_eq (Tm_var r1) (Tm_var r2)))

(* ∀ x.., y.., r. (C(x..,r) ∧ C(y..,r)) ⇒ (x_0=y_0 ∧ ..) ;  trivial when 0-ary *)
let injectivity (rel : string) (inputs : base_typ list) (output : base_typ) : term =
  if inputs = [] then mk_true
  else begin
    let xs = List.map (fun b -> (fresh_var "x", b)) inputs in
    let ys = List.map (fun b -> (fresh_var "y", b)) inputs in
    let r = fresh_var "r" in
    let xt = List.map (fun (v, _) -> Tm_var v) xs in
    let yt = List.map (fun (v, _) -> Tm_var v) ys in
    let cx = apply rel (xt @ [ Tm_var r ]) in
    let cy = apply rel (yt @ [ Tm_var r ]) in
    let eqs = List.map2 (fun (vx, _) (vy, _) -> mk_eq (Tm_var vx) (Tm_var vy)) xs ys in
    let concl = match List.rev eqs with
      | [] -> mk_true
      | last :: rest -> List.fold_left (fun acc e -> mk_and e acc) last rest
    in
    forall_sorted (xs @ ys @ [ (r, output) ]) (mk_imp (mk_and cx cy) concl)
  end

(* constructor descriptor: source name, 0-ary?, input sorts, result sort *)
type cinfo = { cname : string; inputs : base_typ list; output : base_typ }

let disjointness (c1 : cinfo) (c2 : cinfo) : term =
  let const1 = c1.inputs = [] and const2 = c2.inputs = [] in
  match const1, const2 with
  | true, true ->
    (* two constants: C1 ≠ C2 *)
    neq (Tm_fvar (lid_of_str c1.cname)) (Tm_fvar (lid_of_str c2.cname))
  | _ ->
    (* at least one relation: ∀ …, r. hypotheses ⇒ (r ≠ const | false) *)
    let r = fresh_var "r" in
    let rel_hyp (c : cinfo) : (var * base_typ) list * term option =
      if c.inputs = [] then ([], None)  (* constant side: no relation, no binders *)
      else
        let ins = List.map (fun b -> (fresh_var "in", b)) c.inputs in
        let terms = List.map (fun (v, _) -> Tm_var v) ins in
        (ins, Some (apply (rel_name c.cname) (terms @ [ Tm_var r ])))
    in
    let b1, h1 = rel_hyp c1 and b2, h2 = rel_hyp c2 in
    let hyp = match h1, h2 with
      | Some a, Some b -> mk_and a b
      | Some a, None | None, Some a -> a
      | None, None -> assert false            (* both const handled above *)
    in
    let concl = match const1, const2 with
      | true, false -> neq (Tm_var r) (Tm_fvar (lid_of_str c1.cname))
      | false, true -> neq (Tm_var r) (Tm_fvar (lid_of_str c2.cname))
      | _ -> mk_false
    in
    forall_sorted (b1 @ b2 @ [ (r, c1.output) ]) (mk_imp hyp concl)

(* ===== driving over the module ===== *)

let inductives (m : modul) : inductive list =
  List.filter_map (fun se -> match se.sig_el with Sig_inductive i -> Some i | _ -> None)
    m.mod_decls

let cinfos (ind : inductive) : cinfo list =
  List.map
    (fun (dc : data_con) ->
      let inputs, output = ctor_sig dc.dc_typ.ts_typ in
      { cname = dc.dc_name.bname; inputs; output })
    ind.ind_ctors

(* every uninterpreted sort the datatypes reference (self + fields), deduped *)
let datatype_sort_decls (m : modul) : string list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  let acc = ref [] in
  let add (b : base_typ) =
    if not (Smtlib.is_builtin_sort b) && b <> B_unit then begin
      let s = Smtlib.sort_of_base b in
      if not (Hashtbl.mem seen s) then (Hashtbl.add seen s (); acc := s :: !acc)
    end
  in
  List.iter
    (fun ind ->
      add (B_app (ind.ind_name, []));
      List.iter (fun c -> List.iter add c.inputs; add c.output) (cinfos ind))
    (inductives m);
  List.rev_map (fun s -> Printf.sprintf "(declare-sort %s 0)" s) !acc

let constructor_decls (m : modul) : string list =
  List.concat_map
    (fun ind ->
      List.map
        (fun c ->
          if c.inputs = [] then
            Printf.sprintf "(declare-const %s %s)"
              (Smtlib.sanitize c.cname) (Smtlib.sort_of_base c.output)
          else
            Printf.sprintf "(declare-fun %s (%s) Bool)"
              (Smtlib.sanitize (rel_name c.cname))
              (String.concat " " (List.map Smtlib.sort_of_base (c.inputs @ [ c.output ]))))
        (cinfos ind))
    (inductives m)

let datatype_axioms (m : modul) : term list =
  List.concat_map
    (fun ind ->
      let cs = cinfos ind in
      let per_ctor =
        List.concat_map
          (fun c ->
            if c.inputs = [] then []           (* constants are trivially functional/injective *)
            else
              [ functionality (rel_name c.cname) c.inputs c.output;
                injectivity (rel_name c.cname) c.inputs c.output ])
          cs
      in
      let rec pairs = function
        | [] | [ _ ] -> []
        | c :: rest -> List.map (fun c' -> disjointness c c') rest @ pairs rest
      in
      per_ctor @ pairs cs)
    (inductives m)

(* ===== functions ===== *)

(* (name, (arg sorts, result sort)) for every user function, val taking precedence
   over its definition, deduped by name *)
let function_sigs (m : modul) : (string * (base_typ list * base_typ)) list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  let add acc name (ty : typ) =
    match ty with
    | T_arrow _ ->
      if Hashtbl.mem seen name then acc
      else (Hashtbl.add seen name (); (name, ctor_sig ty) :: acc)
    | _ -> acc
  in
  List.rev
    (List.fold_left
       (fun acc se ->
         match se.sig_el with
         | Sig_val (l, sch) -> add acc l.bname sch.ts_typ
         | Sig_let lbs ->
           List.fold_left
             (fun acc lb -> match lb.lb_scheme with
                | Some sch -> add acc lb.lb_name.vname sch.ts_typ
                | None -> acc)
             acc lbs.lbs
         | _ -> acc)
       [] m.mod_decls)

let function_decls (m : modul) : string list =
  List.map
    (fun (name, (ins, out)) ->
      Printf.sprintf "(declare-fun %s (%s) Bool)"
        (Smtlib.sanitize (rel_name name))
        (String.concat " " (List.map Smtlib.sort_of_base (ins @ [ out ]))))
    (function_sigs m)

let function_axioms (m : modul) : term list =
  List.map (fun (name, (ins, out)) -> functionality (rel_name name) ins out) (function_sigs m)

let ret_sort_table (m : modul) : (string, base_typ) Hashtbl.t =
  let tbl : (string, base_typ) Hashtbl.t = Hashtbl.create 32 in
  List.iter
    (fun ind -> List.iter (fun c -> Hashtbl.replace tbl c.cname c.output) (cinfos ind))
    (inductives m);
  List.iter (fun (name, (_, out)) -> Hashtbl.replace tbl name out) (function_sigs m);
  tbl

(* ===== definitional equations ===== *)

let conj_terms : term list -> term = function
  | [] -> mk_true
  | h :: t -> List.fold_left mk_and h t

let rec fun_doms (ty : typ) : base_typ list =
  match ty with T_arrow { adom; acod; _ } -> base_of_typ adom :: fun_doms acod | _ -> []

let rec fun_result (ty : typ) : base_typ =
  match ty with T_arrow { acod; _ } -> fun_result acod | T_refine { rbase; _ } -> rbase

let rec peel_lams (n : int) (e : term) : var list * term =
  if n <= 0 then ([], e)
  else match e with
    | Tm_abs { xbinder; xbody; _ } -> let ps, b = peel_lams (n - 1) xbody in (xbinder :: ps, b)
    | _ -> ([], e)

let is_true_term (t : term) : bool = match t with Tm_const (C_bool true) -> true | _ -> false

(* does the declared type carry any user refinement (a non-trivial predicate)? *)
let rec has_refinement (t : typ) : bool =
  match t with
  | T_refine { rbase; rphi; _ } -> (not (is_true_term rphi)) || base_has_ref rbase
  | T_arrow { adom; acod; _ } -> has_refinement adom || has_refinement acod
and base_has_ref (b : base_typ) : bool =
  match b with B_app (_, args) -> List.exists has_refinement args | _ -> false

let ctor_fields_table (m : modul) : (string, base_typ list) Hashtbl.t =
  let tbl : (string, base_typ list) Hashtbl.t = Hashtbl.create 16 in
  List.iter (fun ind -> List.iter (fun c -> Hashtbl.replace tbl c.cname c.inputs) (cinfos ind))
    (inductives m);
  tbl

let val_map (m : modul) : (string, tscheme) Hashtbl.t =
  let tbl : (string, tscheme) Hashtbl.t = Hashtbl.create 16 in
  List.iter (fun se -> match se.sig_el with Sig_val (l, sch) -> Hashtbl.replace tbl l.bname sch | _ -> ())
    m.mod_decls;
  tbl

(* one equation per match/if leaf of a function body *)
let gen_equations (fname : string) (params : (var * base_typ) list)
    (field_sorts : string -> base_typ list) (body : term) : term list =
  let lhs (args_map : (int * term) list) : term =
    mk_app (Tm_fvar (lid_of_str fname))
      (List.map
         (fun (p, _) -> match List.assoc_opt p.vid args_map with Some t -> t | None -> Tm_var p)
         params)
  in
  let rec walk args_map binders guards (e : term) : term list =
    match e with
    | Tm_match (scrut, branches) ->
      let sv = match scrut with
        | Tm_var v -> v
        | _ -> failwith "defeq: match scrutinee is not a variable"
      in
      List.concat_map
        (fun (br : branch) ->
          match br.br_pat with
          | P_cons (l, subs) ->
            let fvars =
              List.map (function P_var v | P_wild v -> v
                               | _ -> failwith "defeq: nested constructor pattern") subs
            in
            let fsorts = field_sorts l.bname in
            let fbinders =
              try List.combine fvars fsorts
              with Invalid_argument _ -> List.map (fun v -> (v, B_int)) fvars
            in
            let pat_expr = mk_app (Tm_fvar l) (List.map (fun v -> Tm_var v) fvars) in
            let binders' =
              List.filter (fun (v, _) -> v.vid <> sv.vid) binders @ fbinders in
            let s = [ (sv, pat_expr) ] in
            (* Substitute the pattern into the surviving arg mappings too: a nested
               match may scrutinize a variable (e.g. a list tail) that appears inside
               another argument's mapping, so [xs -> Cons h t] must become
               [xs -> Cons h (Cons h2 t2)] — otherwise the dropped [t] leaks into the
               equation's LHS as an unbound symbol. *)
            let args_map' =
              (sv.vid, pat_expr)
              :: List.map (fun (k, tm) -> (k, Subst.subst_term s tm))
                   (List.remove_assoc sv.vid args_map)
            in
            walk args_map' binders' (List.map (Subst.subst_term s) guards)
              (Subst.subst_term s br.br_body)
          | P_const c ->
            walk args_map binders (guards @ [ mk_eq scrut (Tm_const c) ]) br.br_body
          | P_var v -> walk args_map binders guards (Subst.subst_term [ (v, scrut) ] br.br_body)
          | P_wild _ -> walk args_map binders guards br.br_body)
        branches
    | Tm_let ({ lb_rec = false; lbs = [ lb ] }, body) ->
      (* A-normalized let: introduce the (universally quantified) result variable and
         record its definition as a guard [g = def], then keep walking the body. This
         keeps any subsequent match scrutinee a *variable*, so an [if]/nested match
         flattens into guarded equations (a bool [g] stays with [g = def] + [g = c];
         a datatype [g] is substituted away by [P_cons], leaving [def = C(...)]), and
         no [let]/[match] survives into the equation RHS for ANF to choke on. *)
      let g = lb.lb_name in
      let gsort = match lb.lb_scheme with
        | Some { ts_typ = T_refine { rbase; _ }; _ } -> rbase
        | _ -> B_int in
      walk args_map (binders @ [ (g, gsort) ]) (guards @ [ mk_eq (Tm_var g) lb.lb_def ]) body
    | _ ->
      let eq = mk_eq (lhs args_map) e in
      let g = match guards with [] -> eq | _ -> mk_imp (conj_terms guards) eq in
      [ forall_sorted binders g ]
  in
  walk (List.map (fun (p, _) -> (p.vid, Tm_var p)) params) params [] body

let definitional_axioms (m : modul) : term list =
  let vals = val_map m in
  let fields = ctor_fields_table m in
  let field_sorts cname =
    match Hashtbl.find_opt fields cname with Some s -> s | None -> [] in
  List.concat_map
    (fun se ->
      match se.sig_el with
      | Sig_let lbs ->
        List.concat_map
          (fun lb ->
            let name = lb.lb_name.vname in
            let declared =
              match Hashtbl.find_opt vals name with
              | Some sch -> sch.ts_typ
              | None -> (match lb.lb_scheme with Some s -> s.ts_typ | None -> mk_base B_unit)
            in
            match declared with
            | T_arrow _
              when fun_result declared <> B_unit && not (has_refinement declared) ->
              let dom_bases = fun_doms declared in
              let vars, inner = peel_lams (List.length dom_bases) lb.lb_def in
              (try gen_equations name (List.combine vars dom_bases) field_sorts inner
               with Invalid_argument _ -> [])
            | _ -> [])
          lbs.lbs
      | _ -> [])
    m.mod_decls
