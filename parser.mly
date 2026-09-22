/* parser.mly — Menhir grammar for Caml*. Builds Ast directly, resolving names to
   vids and desugaring surface sugar (Lemma/requires/ensures, assert/assume,
   if/then/else, unrefined base types) inline in the semantic actions.

   Term/type nonterminals are synthesized as functions `scope -> Ast.x`, so binders
   can extend the scope for their bodies despite LR's bottom-up reductions. */
%{
open Ast

(* Parse-time scope: local term vars resolved to `var`; type vars generalized
   per top-level declaration. *)
type scope = {
  tm   : (string * var) list;              (* innermost first *)
  ty   : (string, tyvar) Hashtbl.t;        (* one table per top-level decl *)
  tord : string list ref;                  (* tyvar names, first-seen order *)
}
let empty_scope () = { tm = []; ty = Hashtbl.create 8; tord = ref [] }
let bind_tm sc name v = { sc with tm = (name, v) :: sc.tm }
let resolve_tm sc name =
  match List.assoc_opt name sc.tm with
  | Some v -> Tm_var v
  | None   -> Tm_fvar (lid_of_str name)     (* free name ⇒ top-level symbol *)
let get_tyvar sc name =
  match Hashtbl.find_opt sc.ty name with
  | Some tv -> tv
  | None ->
    let tv = fresh_tyvar name in
    Hashtbl.add sc.ty name tv;
    sc.tord := name :: !(sc.tord);
    tv
let scope_tyvars sc = List.rev_map (fun n -> Hashtbl.find sc.ty n) !(sc.tord)

let mk_iff a b = mk_app (Tm_fvar iff_lid) [a; b]

let prim_base = function
  | "int" -> Some B_int | "bool" -> Some B_bool | "float" -> Some B_float
  | "unit" -> Some B_unit | "string" -> Some B_string | _ -> None

(* Unwrap an unrefined base type from a `typ`; refinements only apply to bases. *)
let base_of (t : typ) : base_typ =
  match t with
  | T_refine { rphi = Tm_const (C_bool true); rbase; _ } -> rbase
  | T_refine _ -> failwith "cannot refine an already-refined type"
  | T_arrow _  -> failwith "cannot refine a function type"

(* Arrow-domain descriptor: the binder, its type, and the scope for the codomain. *)
type domd = { d_binder : var; d_typ : typ; d_scope : scope }

(* Surface let-binding, before scope is applied. *)
type lb_syntax = { s_name : string; s_typ : (scope -> typ) option; s_def : scope -> term }

(* Attributes we care about (only expect_failure for now). *)
type attr = A_expect_failure of int list | A_other of string

let rec build_abs binders body sc =
  match binders with
  | [] -> body sc
  | b :: rest ->
    let (v, tyo, sc') = b sc in
    Tm_abs { xbinder = v; xtyp = tyo; xbody = build_abs rest body sc' }

let rec build_quant qk binders body sc =
  match binders with
  | [] -> body sc
  | b :: rest ->
    let (v, tyo, sc') = b sc in
    Tm_quant { qk; qv = v; qty = tyo; qbody = build_quant qk rest body sc' }

let mk_if c a b =
  Tm_match (c, [ { br_pat = P_const (C_bool true);  br_when = None; br_body = a };
                 { br_pat = P_const (C_bool false); br_when = None; br_body = b } ])

(* Build a (possibly recursive, possibly mutual) let group. `outer` is the scope
   outside the let; returns (letbindings, scope-for-body). *)
let build_lets is_rec (lbs : lb_syntax list) outer =
  let named = List.map (fun lb -> (lb, fresh_var lb.s_name)) lbs in
  let body_scope = List.fold_left (fun s (lb, v) -> bind_tm s lb.s_name v) outer named in
  let def_scope = if is_rec then body_scope else outer in
  let lbs' =
    List.map (fun (lb, v) ->
      let scheme = match lb.s_typ with
        | Some t -> let tt = t def_scope in Some { ts_vars = scope_tyvars outer; ts_typ = tt }
        | None   -> None
      in
      { lb_name = v; lb_scheme = scheme; lb_def = lb.s_def def_scope; lb_measure = None })
      named
  in
  ({ lb_rec = is_rec; lbs = lbs' }, body_scope)
%}

/* ===== Tokens ===== */
%token <string> IDENT UIDENT TYVAR STRING
%token <int> INT
%token <float> FLOAT

%token MODULE LET REC AND IN VAL ASSUME TYPE MATCH WITH FUN IF THEN ELSE
%token FORALL EXISTS REQUIRES ENSURES ASSERT WHEN TRUE FALSE LEMMA INSTANTIATE
%token PRIVATE IRREDUCIBLE UNFOLD NOEQ LOGIC

%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK LBRACK_AT_AT
%token COLON SEMICOLON DOT BAR ARROW SUBTYPE EQUALS
%token IMPLIES IFF CONJ DISJ TILDE
%token EQEQ NEQ LT LE GT GE PLUS MINUS STAR SLASH PERCENT

%token PRAGMA_SET_OPTIONS PRAGMA_PUSH_OPTIONS PRAGMA_POP_OPTIONS
%token PRAGMA_CHECK PRAGMA_EVAL
%token EOF

/* A trailing `| pat -> e` after a nested match attaches to the innermost match
   (shift over reduce): give the end-of-branch-list reduction a precedence lower
   than BAR so the shift wins deterministically (0 conflicts). */
%nonassoc LOW_BRANCH
%nonassoc BAR

%start <Ast.modul> modul

%%

/* ===== Module / declarations ===== */
modul:
  | MODULE n=quident ds=list(decl) EOF
      { { mod_name = n; mod_decls = ds; mod_is_iface = false } }

quident:
  | parts=separated_nonempty_list(DOT, UIDENT)
      { match List.rev parts with
        | last :: rev_ns -> lid_of_path (List.rev rev_ns) last
        | [] -> assert false }

decl:
  | attrs=list(attribute) quals=list(qualifier) d=rawDecl
      { let sc = empty_scope () in
        let (sigel, xq) = d sc in
        let base = { sig_el = sigel; sig_quals = quals @ xq;
                     sig_attrs = []; sig_rng = dummy_range } in
        if List.exists (function A_expect_failure _ -> true | _ -> false) attrs then
          let codes =
            List.concat_map (function A_expect_failure c -> c | _ -> []) attrs in
          { sig_el = Sig_fail ([base], codes); sig_quals = [];
            sig_attrs = []; sig_rng = dummy_range }
        else base }

qualifier:
  | PRIVATE      { Q_private }
  | IRREDUCIBLE  { Q_irreducible }
  | UNFOLD       { Q_unfold }
  | NOEQ         { Q_noeq }
  | LOGIC        { Q_logic }

attribute:
  | LBRACK_AT_AT name=IDENT codes=intListOpt RBRACK
      { if name = "expect_failure" then A_expect_failure codes else A_other name }

intListOpt:
  | /* empty */                                    { [] }
  | LBRACK codes=separated_list(SEMICOLON, INT) RBRACK { codes }

/* rawDecl : scope -> (sigelt' * extra qualifiers) */
rawDecl:
  | VAL name=IDENT COLON t=compTyp
      { fun sc -> let tt = t sc in
                  (Sig_val (lid_of_str name, { ts_vars = scope_tyvars sc; ts_typ = tt }), []) }
  | ASSUME VAL name=IDENT COLON t=compTyp
      { fun sc -> let tt = t sc in
                  (Sig_val (lid_of_str name, { ts_vars = scope_tyvars sc; ts_typ = tt }),
                   [Q_assumption]) }
  | ASSUME name=anyname COLON phi=term
      { fun sc -> (Sig_assume (name, phi sc), []) }
  | LET r=recflag lbs=separated_nonempty_list(AND, letbinding)
      { fun sc -> let (lbs', _) = build_lets r lbs sc in (Sig_let lbs', []) }
  | TYPE name=IDENT ps=list(TYVAR) EQUALS cs=nonempty_list(constructor)
      { fun sc ->
          let params = List.map (get_tyvar sc) ps in
          let ctors =
            List.map (fun (nm, t) ->
              let tt = t sc in
              { dc_name = lid_of_str nm; dc_typ = { ts_vars = params; ts_typ = tt } })
              cs
          in
          (Sig_inductive { ind_name = lid_of_str name; ind_params = params;
                           ind_ctors = ctors }, []) }
  | p=pragma
      { fun _ -> (Sig_pragma p, []) }

anyname:
  | id=IDENT  { lid_of_str id }
  | id=UIDENT { lid_of_str id }

recflag:
  | REC { true }
  | /* empty */ { false }

constructor:
  | BAR name=UIDENT COLON t=compTyp { (name, t) }

pragma:
  | PRAGMA_SET_OPTIONS s=STRING   { P_set_options s }
  | PRAGMA_PUSH_OPTIONS s=STRING  { P_push_options (Some s) }
  | PRAGMA_PUSH_OPTIONS           { P_push_options None }
  | PRAGMA_POP_OPTIONS            { P_pop_options }
  | PRAGMA_CHECK t=term           { P_check (t (empty_scope ())) }
  | PRAGMA_EVAL  t=term           { P_eval  (t (empty_scope ())) }

/* ===== Types ===== */

/* Result/computation-type position: a plain type, or the Lemma sugar. */
compTyp:
  | t=typ { t }
  | LEMMA LPAREN REQUIRES p=term RPAREN LPAREN ENSURES q=term RPAREN
      { fun sc -> mk_arrow (fresh_var "_") (mk_squash (p sc)) (mk_squash (q sc)) }
  | LEMMA LPAREN ENSURES q=term RPAREN
      { fun sc -> mk_squash (q sc) }
  | LEMMA LPAREN REQUIRES p=term RPAREN
      { fun sc -> mk_arrow (fresh_var "_") (mk_squash (p sc)) (mk_squash mk_true) }

typ:
  | d=domain ARROW cod=compTyp
      { fun sc -> let dd = d sc in
                  T_arrow { abinder = dd.d_binder; adom = dd.d_typ; acod = cod dd.d_scope } }
  | d=domain
      { fun sc -> (d sc).d_typ }

/* domain : scope -> domd  (an arrow domain, possibly named and/or refined) */
domain:
  | x=IDENT COLON b=appTyp p=refineOpt
      { fun sc ->
          let v = fresh_var x in
          let sc' = bind_tm sc x v in
          let dt = match p with
            | None     -> b sc
            | Some phi -> T_refine { rv = v; rbase = base_of (b sc); rphi = phi sc' }
          in
          { d_binder = v; d_typ = dt; d_scope = sc' } }
  | b=appTyp p=refineOpt
      { fun sc ->
          match p with
          | None -> { d_binder = fresh_var "_"; d_typ = b sc; d_scope = sc }
          | Some phi ->
            let v = fresh_var "_" in
            { d_binder = v;
              d_typ = T_refine { rv = v; rbase = base_of (b sc); rphi = phi (bind_tm sc "_" v) };
              d_scope = sc } }

refineOpt:
  | /* empty */          { None }
  | LBRACE phi=term RBRACE { Some phi }

/* appTyp : scope -> typ  (prefix type application, e.g. `list int`, `either a b`) */
appTyp:
  | ats=nonempty_list(atomicTyp)
      { fun sc ->
          match ats with
          | [] -> assert false                 (* nonempty_list guarantees ≥ 1 *)
          | [single] -> single sc
          | head :: args ->
            (match head sc with
             | T_refine { rphi = Tm_const (C_bool true); rbase = B_app (l, []); _ } ->
               mk_base (B_app (l, List.map (fun a -> a sc) args))
             | _ -> failwith "type application: head is not a type constructor") }

atomicTyp:
  | id=IDENT
      { fun _ -> match prim_base id with
                 | Some b -> mk_base b
                 | None   -> mk_base (B_app (lid_of_str id, [])) }
  | tv=TYVAR
      { fun sc -> mk_base (B_var (get_tyvar sc tv)) }
  | LPAREN t=typ RPAREN
      { t }

/* ===== Terms / formulas (phi ⊂ term) ===== */
term:
  | FUN bs=nonempty_list(binder) ARROW e=term
      { fun sc -> build_abs bs e sc }
  | LET r=recflag lbs=separated_nonempty_list(AND, letbinding) IN body=term
      { fun sc -> let (lbs', bsc) = build_lets r lbs sc in Tm_let (lbs', body bsc) }
  | IF c=term THEN a=term ELSE b=term
      { fun sc -> mk_if (c sc) (a sc) (b sc) }
  | MATCH e=term WITH bs=branches
      { fun sc -> Tm_match (e sc, bs sc) }
  | FORALL bs=nonempty_list(binder) DOT e=term
      { fun sc -> build_quant Forall bs e sc }
  | EXISTS bs=nonempty_list(binder) DOT e=term
      { fun sc -> build_quant Exists bs e sc }
  | ASSERT e=term
      { fun sc -> mk_app (Tm_fvar assert_lid) [e sc] }
  | ASSUME e=term
      { fun sc -> mk_app (Tm_fvar assume_lid) [e sc] }
  | INSTANTIATE LPAREN e=term RPAREN
      { fun sc -> mk_app (Tm_fvar instantiate_lid) [e sc] }
  | e=tmIff { e }

binder:
  | LPAREN x=IDENT COLON t=typ RPAREN
      { fun sc -> let v = fresh_var x in (v, Some (t sc), bind_tm sc x v) }
  | x=IDENT
      { fun sc -> let v = fresh_var x in (v, None, bind_tm sc x v) }

letbinding:
  | name=IDENT params=list(binder) ty=letAnnot EQUALS e=term
      { (* `let f p1 .. pn = e`  desugars the params to `fun p1 .. pn -> e`.
           A type annotation is only kept for the param-less form in v1. *)
        let s_typ = match params with [] -> ty | _ -> None in
        { s_name = name; s_typ; s_def = (fun sc -> build_abs params e sc) } }

letAnnot:
  | /* empty */    { None }
  | COLON t=typ    { Some t }

branches:
  | b=branch %prec LOW_BRANCH { fun sc -> [ b sc ] }
  | b=branch bs=branches      { fun sc -> b sc :: bs sc }

branch:
  | BAR p=pattern g=option(preceded(WHEN, term)) ARROW e=term
      { fun sc ->
          let (pat, sc') = p sc in
          { br_pat = pat;
            br_when = (match g with Some w -> Some (w sc') | None -> None);
            br_body = e sc' } }

tmIff:
  | l=tmImplies IFF r=tmIff  { fun sc -> mk_iff (l sc) (r sc) }
  | e=tmImplies              { e }

tmImplies:
  | l=tmDisj IMPLIES r=tmImplies { fun sc -> mk_imp (l sc) (r sc) }
  | e=tmDisj                     { e }

tmDisj:
  | l=tmDisj DISJ r=tmConj  { fun sc -> mk_or (l sc) (r sc) }
  | e=tmConj                { e }

tmConj:
  | l=tmConj CONJ r=tmCmp   { fun sc -> mk_and (l sc) (r sc) }
  | e=tmCmp                 { e }

tmCmp:
  | l=tmCmp op=cmpOp r=tmAdd { fun sc -> mk_app (Tm_fvar op) [l sc; r sc] }
  | e=tmAdd                  { e }

tmAdd:
  | l=tmAdd op=addOp r=tmMul { fun sc -> mk_app (Tm_fvar op) [l sc; r sc] }
  | e=tmMul                  { e }

tmMul:
  | l=tmMul op=mulOp r=tmPrefix { fun sc -> mk_app (Tm_fvar op) [l sc; r sc] }
  | e=tmPrefix                  { e }

tmPrefix:
  | TILDE e=tmPrefix { fun sc -> mk_not (e sc) }
  | MINUS e=tmPrefix { fun sc -> mk_app (Tm_fvar (lid_of_str "neg")) [e sc] }
  | e=appTerm        { e }

cmpOp:
  | EQUALS { eq_lid } | EQEQ { lid_of_str "==" } | NEQ { lid_of_str "<>" }
  | LT { lid_of_str "<" } | LE { lid_of_str "<=" }
  | GT { lid_of_str ">" } | GE { lid_of_str ">=" }
addOp:
  | PLUS { lid_of_str "+" } | MINUS { lid_of_str "-" }
mulOp:
  | STAR { lid_of_str "*" } | SLASH { lid_of_str "/" } | PERCENT { lid_of_str "%" }

appTerm:
  | f=appTerm a=atomicTerm { fun sc -> Tm_app (f sc, a sc) }
  | e=atomicTerm           { e }

atomicTerm:
  | i=INT    { fun _ -> Tm_const (C_int i) }
  | f=FLOAT  { fun _ -> Tm_const (C_float f) }
  | s=STRING { fun _ -> Tm_const (C_string s) }
  | TRUE     { fun _ -> mk_true }
  | FALSE    { fun _ -> mk_false }
  | id=IDENT  { fun sc -> resolve_tm sc id }
  | uid=UIDENT { fun _ -> Tm_fvar (lid_of_str uid) }
  | LPAREN RPAREN               { fun _ -> Tm_const C_unit }
  | LPAREN e=term RPAREN        { e }
  | LPAREN e=term SUBTYPE t=typ RPAREN { fun sc -> Tm_ascribed (e sc, t sc) }

/* ===== Patterns : scope -> (pat * scope) ===== */
pattern:
  | uid=UIDENT args=nonempty_list(atomicPat)
      { fun sc ->
          let (sc', rps) =
            List.fold_left (fun (s, acc) a -> let (p, s') = a s in (s', p :: acc))
              (sc, []) args
          in
          (P_cons (lid_of_str uid, List.rev rps), sc') }
  | p=atomicPat { p }

atomicPat:
  | i=INT    { fun sc -> (P_const (C_int i), sc) }
  | f=FLOAT  { fun sc -> (P_const (C_float f), sc) }
  | s=STRING { fun sc -> (P_const (C_string s), sc) }
  | TRUE     { fun sc -> (P_const (C_bool true), sc) }
  | FALSE    { fun sc -> (P_const (C_bool false), sc) }
  | id=IDENT
      { fun sc -> if id = "_" then (P_wild (fresh_var "_"), sc)
                  else let v = fresh_var id in (P_var v, bind_tm sc id v) }
  | uid=UIDENT { fun sc -> (P_cons (lid_of_str uid, []), sc) }
  | LPAREN p=pattern RPAREN { p }
