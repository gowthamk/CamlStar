(* smtlib.ml — see smtlib.mli. *)

open Ast

(* ===== interpreted operators ===== *)

let arith_ops = [ "+"; "-"; "*"; "/"; "%"; "neg" ]
let cmp_ops   = [ "<"; "<="; ">"; ">=" ]
let eq_ops    = [ "eq"; "==" ]
let logic_ops = [ "l_and"; "l_or"; "l_imp"; "l_iff"; "l_not" ]

let is_connective (b : string) : bool = List.mem b logic_ops

let is_interpreted (b : string) : bool =
  List.mem b arith_ops || List.mem b cmp_ops || List.mem b eq_ops
  || b = "<>" || List.mem b logic_ops

let is_relation (b : string) : bool =
  let n = String.length b in n >= 4 && String.sub b (n - 4) 4 = "_rel"

(* SMT builtin for a binary/unary interpreted operator (by base name). *)
let smt_op (b : string) : string =
  match b with
  | "+" -> "+" | "-" -> "-" | "*" -> "*"
  | "/" -> "div" | "%" -> "mod" | "neg" -> "-"
  | "<" -> "<" | "<=" -> "<=" | ">" -> ">" | ">=" -> ">="
  | "eq" | "==" -> "=" | "<>" -> "distinct"
  | "l_and" -> "and" | "l_or" -> "or" | "l_imp" -> "=>" | "l_iff" -> "=" | "l_not" -> "not"
  | other -> other

(* ===== identifiers and sorts ===== *)

let sanitize (s : string) : string =
  String.map (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'
    then c else '_')
    s

(* A per-query map from a variable's unique id to a chosen, human-readable SMT
   symbol. Only the variables placed in the table (a VC's scope constants) get a
   readable name; every other variable falls back to [name_vid] in [smt_var]. *)
type naming = (int, string) Hashtbl.t

let starts_alpha (s : string) : bool =
  String.length s > 0
  && ((s.[0] >= 'a' && s.[0] <= 'z') || (s.[0] >= 'A' && s.[0] <= 'Z'))

(* The default rendering: a stable, globally-unique [name_vid] identifier. *)
let default_var (v : var) : string =
  let nm = if starts_alpha v.vname then sanitize v.vname else "x" in
  Printf.sprintf "%s_%d" nm v.vid

(* Characters allowed (besides letters/digits) in an SMT-LIB simple symbol. *)
let simple_special = "+-/*=%?!.$_~&^<>@"

let is_simple_symbol (s : string) : bool =
  String.length s > 0
  && not (s.[0] >= '0' && s.[0] <= '9')
  && String.for_all
       (fun c ->
         (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
         || String.contains simple_special c)
       s

(* Render [s] as an SMT symbol: bare when it is a valid simple symbol, else as a
   quoted symbol |s| (which admits any char except '|' and '\\'). *)
let emit_symbol (s : string) : string =
  if is_simple_symbol s then s
  else "|" ^ String.map (fun c -> if c = '|' || c = '\\' then '_' else c) s ^ "|"

let smt_var (naming : naming) (v : var) : string =
  match Hashtbl.find_opt naming v.vid with
  | Some s -> s
  | None -> default_var v

(* Build a naming for a set of variables (a VC's scope): a base name used by a
   single variable prints bare (its source spelling, quoted if needed); a base name
   shared by several is disambiguated with the vid. A final guard forces the vid
   suffix on any symbols that still coincide, keeping the map injective. *)
let make_naming (vars : var list) : naming =
  let seen = Hashtbl.create 16 in
  let uniq =
    List.filter
      (fun v -> if Hashtbl.mem seen v.vid then false else (Hashtbl.add seen v.vid (); true))
      vars
  in
  (* "_" is a reserved SMT symbol and "" is illegal, so those never print bare —
     force them onto the vid-suffixed path below *)
  let base (v : var) : string =
    if String.length v.vname > 0 && v.vname <> "_" then v.vname else "x" in
  let count = Hashtbl.create 16 in
  List.iter
    (fun v -> let b = base v in
      Hashtbl.replace count b (1 + (try Hashtbl.find count b with Not_found -> 0)))
    uniq;
  let tbl : naming = Hashtbl.create 16 in
  List.iter
    (fun v ->
      let b = base v in
      let raw = if Hashtbl.find count b = 1 then b else Printf.sprintf "%s_%d" b v.vid in
      Hashtbl.replace tbl v.vid (emit_symbol raw))
    uniq;
  (* injectivity guard: if two distinct vids still map to the same symbol, force the
     vid suffix on all of them *)
  let sym_count = Hashtbl.create 16 in
  Hashtbl.iter
    (fun _ s -> Hashtbl.replace sym_count s (1 + (try Hashtbl.find sym_count s with Not_found -> 0)))
    tbl;
  List.iter
    (fun v ->
      let s = Hashtbl.find tbl v.vid in
      if Hashtbl.find sym_count s > 1 then
        Hashtbl.replace tbl v.vid (emit_symbol (Printf.sprintf "%s_%d" (base v) v.vid)))
    uniq;
  tbl

let sort_of_base (b : base_typ) : string =
  match b with
  | B_int -> "Int" | B_bool -> "Bool" | B_float -> "Real" | B_string -> "String"
  | B_unit -> "Unit"
  | B_app (l, _) -> "UI_" ^ sanitize l.bname
  | B_var tv -> "UI_" ^ sanitize tv.tvname

let is_builtin_sort (b : base_typ) : bool =
  match b with B_int | B_bool | B_float | B_string -> true | _ -> false

(* ===== term rendering ===== *)

let float_lit (f : float) : string =
  let s = string_of_float f in                 (* OCaml prints e.g. "3." or "3.14" *)
  if String.length s > 0 && s.[String.length s - 1] = '.' then s ^ "0"
  else if not (String.contains s '.') then s ^ ".0"
  else s

let const_sexpr (c : constant) : string =
  match c with
  | C_unit -> "unit_val"
  | C_bool b -> if b then "true" else "false"
  | C_int n -> if n < 0 then Printf.sprintf "(- %d)" (-n) else string_of_int n
  | C_float f -> if f < 0.0 then Printf.sprintf "(- %s)" (float_lit (-.f)) else float_lit f
  | C_string s -> Printf.sprintf "\"%s\"" s

let rec head_spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> head_spine f (a :: acc) | _ -> (t, acc)

let rec go (naming : naming) (t : term) : string =
  match t with
  | Tm_const c -> const_sexpr c
  | Tm_var v -> smt_var naming v
  | Tm_fvar l -> sanitize l.bname            (* nullary symbol: constant / 0-ary constructor *)
  | Tm_app _ ->
    let head, args = head_spine t [] in
    (match head with
     | Tm_fvar l when is_interpreted l.bname ->
       Printf.sprintf "(%s %s)" (smt_op l.bname) (String.concat " " (List.map (go naming) args))
     | Tm_fvar l ->
       (* uninterpreted application: user relation (f_rel), constructor, or a bool
          predicate under its source name *)
       Printf.sprintf "(%s %s)" (sanitize l.bname) (String.concat " " (List.map (go naming) args))
     | Tm_var v ->
       (* a bool predicate applied under a Tm_var head (e.g. a recursive self-call):
          use its source name, matching its predicate declaration *)
       Printf.sprintf "(%s %s)" (sanitize v.vname) (String.concat " " (List.map (go naming) args))
     | _ -> failwith "smtlib: application head is not a symbol")
  | Tm_quant { qk; qv; qty; qbody } ->
    let sort = match qty with
      | Some ty -> (match ty with T_refine { rbase; _ } -> sort_of_base rbase
                                | T_arrow _ -> failwith "smtlib: higher-order quantifier")
      | None -> failwith "smtlib: quantifier without a sort"
    in
    let q = match qk with Forall -> "forall" | Exists -> "exists" in
    Printf.sprintf "(%s ((%s %s)) %s)" q (smt_var naming qv) sort (go naming qbody)
  | Tm_ascribed (e, _) -> go naming e
  | Tm_abs _ -> failwith "smtlib: unexpected lambda in formula"
  | Tm_let _ -> failwith "smtlib: unexpected let in formula (should be relabs'd away)"
  | Tm_match _ -> failwith "smtlib: unexpected match in formula"

let term_to_sexpr (naming : naming) (t : term) : string = go naming t

(* ===== the "instantiated terms" ledger ===== *)

(* Every user-function/constructor application appearing in [ts] (inner applications
   first), deduplicated by printed form. Interpreted operators and connectives are
   not themselves recorded, but their arguments are still traversed (so a guard call
   like [le x h] is captured). *)
let collect_apps (ts : term list) : term list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 64 in
  let acc = ref [] in
  let add tm =
    let s = Ast.string_of_term tm in
    if not (Hashtbl.mem seen s) then (Hashtbl.add seen s (); acc := tm :: !acc)
  in
  let rec go t =
    match t with
    | Tm_app _ ->
      let head, args = head_spine t [] in
      List.iter go args;
      (match head with
       | Tm_fvar l when not (is_interpreted l.bname) -> add t
       | Tm_var _ -> add t                         (* recursive/other function reference *)
       | _ -> ())
    | Tm_quant q -> go q.qbody
    | Tm_ascribed (e, _) -> go e
    | _ -> ()
  in
  List.iter go ts; List.rev !acc

(* The ledger grouped by source (goal / hypotheses / instantiate! hints). The
   hypotheses group includes the constructor discriminators (Raven's "from patterns").
   For *data* applications this equals what the backend actually materialises. *)
let ledger_sections (vc : Vc.t) : (string * term list) list =
  [ ("from the goal:", collect_apps [ vc.Vc.goal ]);
    ("from the hypotheses:", collect_apps vc.Vc.hyps);
    ("from the instantiate! hints:", collect_apps vc.Vc.instantiations) ]
