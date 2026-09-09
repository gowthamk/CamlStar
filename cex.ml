(* cex.ml — see cex.mli. *)

open Ast

module M   = Z3.Model
module FD  = Z3.FuncDecl
module E   = Z3.Expr
module Srt = Z3.Sort
module Sym = Z3.Symbol

type value =
  | Scalar  of string
  | SetOf   of value list
  | Entries of (value list * value) list

type t = (string * value) list

(* ===== small string helpers ===== *)

let starts_with pre s =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

(* SMT quoted symbols come back either as [i'] or [|i'|] depending on Z3; normalise
   so the naming's symbol and the model's symbol compare equal. *)
let unquote (s : string) : string =
  let n = String.length s in
  if n >= 2 && s.[0] = '|' && s.[n - 1] = '|' then String.sub s 1 (n - 2) else s

(* a Z3 universe element name -> a per-sort tag: [UI_nat!val!1] -> [nat!1] *)
let elem_tag (z3name : string) : string =
  let s = if starts_with "UI_" z3name then String.sub z3name 3 (String.length z3name - 3) else z3name in
  match String.split_on_char '!' s with
  | [ name; "val"; idx ] -> name ^ "!" ^ idx
  | _ -> s

(* [(- 2)] -> [-2] for numeric literals; leave everything else as-is *)
let clean_lit (s : string) : string =
  let n = String.length s in
  if n > 4 && String.sub s 0 3 = "(- " && s.[n - 1] = ')'
  then "-" ^ String.trim (String.sub s 3 (n - 4))
  else s

let ends_rel s =
  let n = String.length s in n >= 4 && String.sub s (n - 4) 4 = "_rel"

(* ===== sort classification ===== *)

let is_ui_sort  (s : Srt.sort) : bool = starts_with "UI_" (Srt.to_string s)
let sort_label (s : Srt.sort) : string =        (* "UI_nat" -> "nat" *)
  let s = Srt.to_string s in
  if starts_with "UI_" s then String.sub s 3 (String.length s - 3) else s

let is_builtin_sort_name = function
  | "Int" | "Bool" | "Real" | "String" -> true | _ -> false

(* all combinations picking one element from each list, in order *)
let rec cartesian = function
  | [] -> [ [] ]
  | xs :: rest ->
    let tails = cartesian rest in
    List.concat_map (fun x -> List.map (fun t -> x :: t) tails) xs

(* ===== reconstruction ===== *)

let of_model (m : modul) (vc : Vc.t) (naming : Smtlib.naming) (ctx : Z3.context) (model : M.model) : t =
  (* SMT const name -> source name, for every 0-ary constructor of the module *)
  let nullary : (string, string) Hashtbl.t = Hashtbl.create 16 in
  List.iter
    (fun se -> match se.sig_el with
       | Sig_inductive ind ->
         List.iter
           (fun dc -> match dc.dc_typ.ts_typ with
              | T_refine _ -> Hashtbl.replace nullary (Smtlib.sanitize dc.dc_name.bname) dc.dc_name.bname
              | T_arrow _ -> ())
           ind.ind_ctors
       | _ -> ())
    m.mod_decls;

  (* element display table, keyed by [Expr.to_string] (Z3 prints universe elements
     as stable, unique names). 0-ary constructor elements win their source name; the
     rest get a per-sort tag. *)
  let elem_tbl : (string, string) Hashtbl.t = Hashtbl.create 64 in
  List.iter
    (fun decl ->
       match Hashtbl.find_opt nullary (unquote (Sym.to_string (FD.get_name decl))) with
       | Some src ->
         (match M.get_const_interp model decl with
          | Some e -> Hashtbl.replace elem_tbl (E.to_string e) src
          | None -> ())
       | None -> ())
    (M.get_const_decls model);
  List.iter
    (fun srt ->
       if is_ui_sort srt then
         List.iter
           (fun e ->
              let k = E.to_string e in
              if not (Hashtbl.mem elem_tbl k) then Hashtbl.replace elem_tbl k (elem_tag k))
           (M.sort_universe model srt))
    (M.get_sorts model);

  let render (e : E.expr) : value =
    let sn = Srt.to_string (E.get_sort e) in
    if is_builtin_sort_name sn then Scalar (clean_lit (E.to_string e))
    else if sn = "Unit" then Scalar "()"
    else
      let k = E.to_string e in
      Scalar (match Hashtbl.find_opt elem_tbl k with Some d -> d | None -> elem_tag k)
  in

  (* section 1: sort universes *)
  let universes =
    List.filter_map
      (fun srt ->
         if is_ui_sort srt then Some (sort_label srt, SetOf (List.map render (M.sort_universe model srt)))
         else None)
      (M.get_sorts model)
  in

  (* section 2: source program variables (vc.scope is pre-skolem: program vars only) *)
  let const_val : (string, E.expr) Hashtbl.t = Hashtbl.create 32 in
  List.iter
    (fun decl -> match M.get_const_interp model decl with
       | Some e -> Hashtbl.replace const_val (unquote (Sym.to_string (FD.get_name decl))) e
       | None -> ())
    (M.get_const_decls model);
  let progvars =
    List.filter_map
      (fun (v, b) ->
         if b = B_unit then None
         else match Hashtbl.find_opt const_val (unquote (Smtlib.smt_var naming v)) with
           | Some e -> Some (v.vname, render e)
           | None -> None)
      vc.Vc.scope
  in

  (* section 3: function maps (each f_rel under source name f).
     Z3 may hand back a relation's interpretation as a formula rather than a finite
     entry table, so rather than reading entries we enumerate the (finite) argument
     space over the sort universes and [Model.eval] the relation at each point. This
     is correct regardless of how Z3 chose to present the interpretation, and it
     naturally handles the func_interp else-value. A relation is skipped unless every
     column is a finite uninterpreted sort (so Int-domain or Unit-valued relations,
     whose maps are not finite/informative, are omitted). *)
  let univ_of (srt : Srt.sort) : E.expr list option =
    if is_ui_sort srt then Some (M.sort_universe model srt) else None
  in
  let funcs =
    List.filter_map
      (fun decl ->
         let raw = Sym.to_string (FD.get_name decl) in
         let doms = FD.get_domain decl in
         let col_univs = List.map univ_of doms in
         if not (ends_rel raw) || List.length doms < 2 || List.mem None col_univs then None
         else
           let univs = List.map (function Some u -> u | None -> []) col_univs in
           let entries =
             List.filter_map
               (fun tup ->
                  match M.eval model (E.mk_app ctx decl tup) true with
                  | Some e when E.to_string e = "true" ->
                    (match List.rev tup with
                     | result :: rev_key -> Some (List.rev_map render rev_key, render result)
                     | [] -> None)
                  | _ -> None)
               (cartesian univs)
           in
           if entries = [] then None
           else Some (String.sub raw 0 (String.length raw - 4), Entries entries))
      (M.get_func_decls model)
  in
  universes @ progvars @ funcs

(* ===== JSON ===== *)

let escape (s : string) : string =
  let b = Buffer.create (String.length s + 2) in
  String.iter
    (fun c -> match c with
       | '"' -> Buffer.add_string b "\\\""
       | '\\' -> Buffer.add_string b "\\\\"
       | '\n' -> Buffer.add_string b "\\n"
       | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

(* keys are always scalars; render a tuple as "(a, b)" and a singleton as "a" *)
let key_string (k : value list) : string =
  let part = function Scalar s -> s | _ -> "?" in
  match k with
  | [ x ] -> part x
  | xs -> "(" ^ String.concat ", " (List.map part xs) ^ ")"

let rec json_of_value (indent : int) (v : value) : string =
  let pad n = String.make n ' ' in
  match v with
  | Scalar s -> "\"" ^ escape s ^ "\""
  | SetOf vs -> "[" ^ String.concat ", " (List.map (json_of_value indent) vs) ^ "]"
  | Entries [] -> "{}"
  | Entries es ->
    let items =
      List.map
        (fun (k, v) ->
           Printf.sprintf "%s\"%s\": %s" (pad (indent + 2)) (escape (key_string k)) (json_of_value (indent + 2) v))
        es
    in
    "{\n" ^ String.concat ",\n" items ^ "\n" ^ pad indent ^ "}"

let to_json (c : t) : string =
  if c = [] then "{}"
  else
    let items =
      List.map (fun (label, v) -> Printf.sprintf "  \"%s\": %s" (escape label) (json_of_value 2 v)) c
    in
    "{\n" ^ String.concat ",\n" items ^ "\n}"
