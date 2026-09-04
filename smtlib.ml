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

let smt_var (v : var) : string =
  let nm =
    if String.length v.vname > 0
       && ((v.vname.[0] >= 'a' && v.vname.[0] <= 'z') || (v.vname.[0] >= 'A' && v.vname.[0] <= 'Z'))
    then sanitize v.vname
    else "x"
  in
  Printf.sprintf "%s_%d" nm v.vid

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

let rec go (t : term) : string =
  match t with
  | Tm_const c -> const_sexpr c
  | Tm_var v -> smt_var v
  | Tm_fvar l -> sanitize l.bname            (* nullary symbol: constant / 0-ary constructor *)
  | Tm_app _ ->
    let head, args = head_spine t [] in
    (match head with
     | Tm_fvar l when is_interpreted l.bname ->
       Printf.sprintf "(%s %s)" (smt_op l.bname) (String.concat " " (List.map go args))
     | Tm_fvar l ->
       (* uninterpreted application: user relation (f_rel), or a constructor app *)
       Printf.sprintf "(%s %s)" (sanitize l.bname) (String.concat " " (List.map go args))
     | _ -> failwith "smtlib: application head is not a symbol")
  | Tm_quant { qk; qv; qty; qbody } ->
    let sort = match qty with
      | Some ty -> (match ty with T_refine { rbase; _ } -> sort_of_base rbase
                                | T_arrow _ -> failwith "smtlib: higher-order quantifier")
      | None -> failwith "smtlib: quantifier without a sort"
    in
    let q = match qk with Forall -> "forall" | Exists -> "exists" in
    Printf.sprintf "(%s ((%s %s)) %s)" q (smt_var qv) sort (go qbody)
  | Tm_ascribed (e, _) -> go e
  | Tm_abs _ -> failwith "smtlib: unexpected lambda in formula"
  | Tm_let _ -> failwith "smtlib: unexpected let in formula (should be relabs'd away)"
  | Tm_match _ -> failwith "smtlib: unexpected match in formula"

let term_to_sexpr (t : term) : string = go t
