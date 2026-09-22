(* ast.ml — implementation of the Caml* core AST (see ast.mli for the design). *)

(* ===== Identifiers ===== *)
type var   = { vname : string; vid : int }
type tyvar = { tvname : string; tvid : int }
type lid   = { ns : string list; bname : string }

(* Single global gensym counter shared by term- and type-variables. *)
let gensym_counter = ref 0
let next_id () = let n = !gensym_counter in incr gensym_counter; n

let fresh_var   (name : string) : var   = { vname = name;  vid  = next_id () }
let fresh_tyvar (name : string) : tyvar = { tvname = name; tvid = next_id () }

let lid_of_str  (s : string) : lid = { ns = []; bname = s }
let lid_of_path (ns : string list) (name : string) : lid = { ns; bname = name }

let var_eq   (x : var)   (y : var)   = x.vid = y.vid
let tyvar_eq (x : tyvar) (y : tyvar) = x.tvid = y.tvid
let lid_eq   (x : lid)   (y : lid)   = x.ns = y.ns && x.bname = y.bname

(* ===== Constants ===== *)
type constant =
  | C_unit
  | C_bool   of bool
  | C_int    of int
  | C_float  of float
  | C_string of string

type quantifier = Forall | Exists

(* ===== Core mutually-recursive syntax ===== *)
type base_typ =
  | B_int | B_bool | B_float | B_unit | B_string
  | B_var of tyvar
  | B_app of lid * typ list

and typ =
  | T_refine of refinement
  | T_arrow  of arrow

and refinement = { rv : var; rbase : base_typ; rphi : term }
and arrow      = { abinder : var; adom : typ; acod : typ }

and term =
  | Tm_var      of var
  | Tm_fvar     of lid
  | Tm_const    of constant
  | Tm_abs      of abs
  | Tm_app      of term * term
  | Tm_let      of letbindings * term
  | Tm_match    of term * branch list
  | Tm_ascribed of term * typ
  | Tm_quant    of quant

and abs   = { xbinder : var; xtyp : typ option; xbody : term }
and quant = { qk : quantifier; qv : var; qty : typ option; qbody : term }

and letbindings = { lb_rec : bool; lbs : letbinding list }
and letbinding  = { lb_name : var; lb_scheme : tscheme option; lb_def : term;
                    lb_measure : decreases option }
and decreases = Dec_lex of term list | Dec_wf of term * term

and branch = { br_pat : pat; br_when : term option; br_body : term }
and pat = P_const of constant | P_var of var | P_wild of var | P_cons of lid * pat list

and tscheme = { ts_vars : tyvar list; ts_typ : typ }

(* ===== Top level ===== *)
type range = { file : string; rstart : int * int; rend : int * int }
let dummy_range = { file = ""; rstart = (0, 0); rend = (0, 0) }

type data_con  = { dc_name : lid; dc_typ : tscheme }
type inductive = { ind_name : lid; ind_params : tyvar list; ind_ctors : data_con list }

type qualifier = Q_assumption | Q_private | Q_irreducible | Q_unfold | Q_noeq | Q_logic

type pragma =
  | P_check of term | P_eval of term
  | P_set_options of string | P_push_options of string option | P_pop_options

type sigelt' =
  | Sig_inductive of inductive
  | Sig_let       of letbindings
  | Sig_val       of lid * tscheme
  | Sig_assume    of lid * term
  | Sig_pragma    of pragma
  | Sig_fail      of sigelt list * int list

and sigelt = { sig_el : sigelt'; sig_quals : qualifier list;
               sig_attrs : term list; sig_rng : range }

type modul = { mod_name : lid; mod_decls : sigelt list; mod_is_iface : bool }

(* ===== Well-known symbols ===== *)
let and_lid    = lid_of_str "l_and"
let or_lid     = lid_of_str "l_or"
let imp_lid    = lid_of_str "l_imp"
let iff_lid    = lid_of_str "l_iff"
let not_lid    = lid_of_str "l_not"
let eq_lid     = lid_of_str "eq"
let assert_lid = lid_of_str "assert"
let assume_lid = lid_of_str "assume"
let instantiate_lid = lid_of_str "instantiate!"

(* ===== Smart constructors ===== *)
let mono (t : typ) : tscheme = { ts_vars = []; ts_typ = t }

let mk_true  : term = Tm_const (C_bool true)
let mk_false : term = Tm_const (C_bool false)

(* Any base type B, unrefined, is {v:B | true}. *)
let mk_base (b : base_typ) : typ =
  T_refine { rv = fresh_var "_"; rbase = b; rphi = mk_true }

let t_int    = mk_base B_int
let t_bool   = mk_base B_bool
let t_unit   = mk_base B_unit
let t_float  = mk_base B_float
let t_string = mk_base B_string

let mk_app (hd : term) (args : term list) : term =
  List.fold_left (fun f a -> Tm_app (f, a)) hd args

let mk_and a b = mk_app (Tm_fvar and_lid) [a; b]
let mk_or  a b = mk_app (Tm_fvar or_lid)  [a; b]
let mk_imp a b = mk_app (Tm_fvar imp_lid) [a; b]
let mk_not a   = mk_app (Tm_fvar not_lid) [a]
let mk_eq  a b = mk_app (Tm_fvar eq_lid)  [a; b]

let mk_forall v ty body = Tm_quant { qk = Forall; qv = v; qty = ty; qbody = body }
let mk_exists v ty body = Tm_quant { qk = Exists; qv = v; qty = ty; qbody = body }

let mk_arrow x dom cod = T_arrow { abinder = x; adom = dom; acod = cod }

(* squash phi := {_:unit | phi} *)
let mk_squash phi = T_refine { rv = fresh_var "_"; rbase = B_unit; rphi = phi }

(* ===== Debug printing ===== *)

let string_of_lid (l : lid) : string =
  String.concat "." (l.ns @ [l.bname])

let string_of_const : constant -> string = function
  | C_unit     -> "()"
  | C_bool b   -> string_of_bool b
  | C_int i    -> string_of_int i
  | C_float f  -> string_of_float f
  | C_string s -> "\"" ^ s ^ "\""

let string_of_quant : quantifier -> string = function
  | Forall -> "forall" | Exists -> "exists"

(* Recognize infix operators (logical + arithmetic) for readable output. *)
let infix_symbol (l : lid) : string option =
  if lid_eq l and_lid then Some "/\\"
  else if lid_eq l or_lid  then Some "\\/"
  else if lid_eq l imp_lid then Some "==>"
  else if lid_eq l iff_lid then Some "<==>"
  else if lid_eq l eq_lid  then Some "="
  else if l.ns = [] && List.mem l.bname ["+"; "-"; "*"; "<"; "<="; ">"; ">="]
  then Some l.bname
  else None

(* Flatten a left-nested application spine into (head, args). *)
let rec flatten_app (t : term) (acc : term list) : term * term list =
  match t with
  | Tm_app (f, a) -> flatten_app f (a :: acc)
  | _ -> (t, acc)

let is_true : term -> bool = function
  | Tm_const (C_bool true) -> true
  | _ -> false

(* Types. *)
let rec string_of_typ (t : typ) : string =
  match t with
  | T_arrow { abinder; adom; acod } ->
    Printf.sprintf "%s:%s -> %s" abinder.vname (string_of_typ_atom adom) (string_of_typ acod)
  | T_refine { rv; rbase; rphi } ->
    if is_true rphi then string_of_base rbase
    else if rbase = B_unit then
      Printf.sprintf "squash (%s)" (string_of_term rphi)
    else
      Printf.sprintf "{%s:%s | %s}" rv.vname (string_of_base rbase) (string_of_term rphi)

(* A type used as an argument/atom, parenthesized when it is compound. *)
and string_of_typ_atom (t : typ) : string =
  match t with
  | T_arrow _ -> "(" ^ string_of_typ t ^ ")"
  | T_refine { rphi; rbase = B_app (_, _ :: _); _ } when is_true rphi ->
    "(" ^ string_of_typ t ^ ")"
  | _ -> string_of_typ t

and string_of_base (b : base_typ) : string =
  match b with
  | B_int -> "int" | B_bool -> "bool" | B_float -> "float"
  | B_unit -> "unit" | B_string -> "string"
  | B_var tv -> "'" ^ tv.tvname
  | B_app (l, []) -> string_of_lid l
  | B_app (l, args) ->
    string_of_lid l ^ " " ^ String.concat " " (List.map string_of_typ_atom args)

(* Terms. *)
and string_of_term (t : term) : string =
  match t with
  | Tm_var v   -> v.vname
  | Tm_fvar l  -> string_of_lid l
  | Tm_const c -> string_of_const c
  | Tm_abs { xbinder; xtyp; xbody } ->
    let annot = match xtyp with
      | Some t -> Printf.sprintf "(%s:%s)" xbinder.vname (string_of_typ t)
      | None   -> xbinder.vname
    in
    Printf.sprintf "fun %s -> %s" annot (string_of_term xbody)
  | Tm_app _ ->
    let hd, args = flatten_app t [] in
    (match hd, args with
     | Tm_fvar l, [a; b] when infix_symbol l <> None ->
       let op = match infix_symbol l with Some s -> s | None -> assert false in
       Printf.sprintf "%s %s %s" (string_of_term_atom a) op (string_of_term_atom b)
     | Tm_fvar l, [a] when lid_eq l not_lid ->
       "~" ^ string_of_term_atom a
     | _ ->
       string_of_term_atom hd ^ " " ^ String.concat " " (List.map string_of_term_atom args))
  | Tm_let (lbs, body) ->
    Printf.sprintf "%s in %s" (string_of_letbindings lbs) (string_of_term body)
  | Tm_match (scrut, branches) ->
    Printf.sprintf "match %s with%s"
      (string_of_term scrut)
      (String.concat "" (List.map string_of_branch branches))
  | Tm_ascribed (e, ty) ->
    Printf.sprintf "(%s <: %s)" (string_of_term e) (string_of_typ ty)
  | Tm_quant { qk; qv; qty; qbody } ->
    let binder = match qty with
      | Some ty -> Printf.sprintf "(%s:%s)" qv.vname (string_of_typ ty)
      | None    -> qv.vname
    in
    Printf.sprintf "%s %s. %s"
      (string_of_quant qk) binder (string_of_term qbody)

(* A term used as an argument/operand, parenthesized when it is compound. *)
and string_of_term_atom (t : term) : string =
  match t with
  | Tm_var _ | Tm_fvar _ | Tm_const _ -> string_of_term t
  | _ -> "(" ^ string_of_term t ^ ")"

and string_of_branch (b : branch) : string =
  let guard = match b.br_when with
    | None -> ""
    | Some g -> " when " ^ string_of_term g
  in
  Printf.sprintf "\n  | %s%s -> %s" (string_of_pat b.br_pat) guard (string_of_term b.br_body)

and string_of_pat (p : pat) : string =
  match p with
  | P_const c -> string_of_const c
  | P_var v   -> v.vname
  | P_wild _  -> "_"
  | P_cons (l, []) -> string_of_lid l
  | P_cons (l, ps) ->
    string_of_lid l ^ " " ^ String.concat " " (List.map string_of_pat_atom ps)

and string_of_pat_atom (p : pat) : string =
  match p with
  | P_cons (_, _ :: _) -> "(" ^ string_of_pat p ^ ")"
  | _ -> string_of_pat p

and string_of_tscheme (ts : tscheme) : string =
  match ts.ts_vars with
  | [] -> string_of_typ ts.ts_typ
  | vs ->
    let binders = String.concat " " (List.map (fun tv -> "'" ^ tv.tvname) vs) in
    Printf.sprintf "forall %s. %s" binders (string_of_typ ts.ts_typ)

and string_of_letbinding (lb : letbinding) : string =
  let meas = match lb.lb_measure with
    | None -> ""
    | Some (Dec_lex ts) ->
      " (decreases [" ^ String.concat "; " (List.map string_of_term ts) ^ "])"
    | Some (Dec_wf (rel, m)) ->
      Printf.sprintf " (decreases {%s; %s})" (string_of_term rel) (string_of_term m)
  in
  let sch = match lb.lb_scheme with
    | Some s -> " : " ^ string_of_tscheme s
    | None   -> ""
  in
  Printf.sprintf "%s%s%s = %s"
    lb.lb_name.vname sch meas (string_of_term lb.lb_def)

and string_of_letbindings (lbs : letbindings) : string =
  let kw = if lbs.lb_rec then "let rec " else "let " in
  kw ^ String.concat " and " (List.map string_of_letbinding lbs.lbs)

let string_of_qual : qualifier -> string = function
  | Q_assumption  -> "assume"
  | Q_private     -> "private"
  | Q_irreducible -> "irreducible"
  | Q_unfold      -> "unfold"
  | Q_noeq        -> "noeq"
  | Q_logic       -> "logic"

let string_of_quals (qs : qualifier list) : string =
  match qs with
  | [] -> ""
  | _  -> String.concat " " (List.map string_of_qual qs) ^ " "

let string_of_pragma : pragma -> string = function
  | P_check t          -> "#check " ^ string_of_term t
  | P_eval t           -> "#eval " ^ string_of_term t
  | P_set_options s    -> "#set-options \"" ^ s ^ "\""
  | P_push_options None -> "#push-options"
  | P_push_options (Some s) -> "#push-options \"" ^ s ^ "\""
  | P_pop_options      -> "#pop-options"

let string_of_inductive (ind : inductive) : string =
  let params = match ind.ind_params with
    | [] -> ""
    | ps -> String.concat " " (List.map (fun tv -> "'" ^ tv.tvname) ps) ^ " "
  in
  let ctor dc =
    Printf.sprintf "  | %s : %s" (string_of_lid dc.dc_name) (string_of_tscheme dc.dc_typ)
  in
  Printf.sprintf "type %s%s =\n%s"
    params (string_of_lid ind.ind_name)
    (String.concat "\n" (List.map ctor ind.ind_ctors))

let rec string_of_sigelt (se : sigelt) : string =
  let quals = string_of_quals se.sig_quals in
  match se.sig_el with
  | Sig_inductive ind -> quals ^ string_of_inductive ind
  | Sig_let lbs       -> quals ^ string_of_letbindings lbs
  | Sig_val (l, ts)   ->
    Printf.sprintf "%sval %s : %s" quals (string_of_lid l) (string_of_tscheme ts)
  | Sig_assume (l, phi) ->
    Printf.sprintf "%sassume %s : %s" quals (string_of_lid l) (string_of_term phi)
  | Sig_pragma p      -> quals ^ string_of_pragma p
  | Sig_fail (ses, codes) ->
    let codes_s = String.concat "; " (List.map string_of_int codes) in
    let body = String.concat "\n" (List.map string_of_sigelt ses) in
    Printf.sprintf "%s[@@expect_failure [%s]]\n%s" quals codes_s body
