(* shape.ml — see shape.mli. The [Ast.typ] <-> [Unify.ityp] bridge (relocated from
   infer.ml) plus the checker-facing helpers [unify_shape] and [match_typ]. *)

open Unify

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

(* ===== shape consistency and one-sided instantiation ===== *)

let unify_shape (a : Ast.typ) (b : Ast.typ) : unit = unify (erase a) (erase b)

exception Match_error of string

let match_typ (pat : Ast.typ) (concrete : Ast.typ) : (Ast.tyvar * Ast.typ) list =
  let acc : (int * (Ast.tyvar * Ast.typ)) list ref = ref [] in
  let bind (tv : Ast.tyvar) (ty : Ast.typ) =
    match List.assoc_opt tv.Ast.tvid !acc with
    | None -> acc := (tv.Ast.tvid, (tv, ty)) :: !acc
    | Some (_, prev) ->
      if not (Subst.alpha_equal_typ prev ty) then
        raise (Match_error (Printf.sprintf "inconsistent instantiation of '%s" tv.Ast.tvname))
  in
  let rec go (p : Ast.typ) (c : Ast.typ) : unit =
    match p with
    | Ast.T_refine { rbase = Ast.B_var tv; _ } -> bind tv c
    | Ast.T_refine { rbase = pb; _ } ->
      (match c with
       | Ast.T_refine { rbase = cb; _ } -> go_base pb cb
       | Ast.T_arrow _ -> raise (Match_error "expected a base type, got a function"))
    | Ast.T_arrow { adom = pd; acod = pc; _ } ->
      (match c with
       | Ast.T_arrow { adom = cd; acod = cc; _ } -> go pd cd; go pc cc
       | Ast.T_refine _ -> raise (Match_error "expected a function, got a base type"))
  and go_base (pb : Ast.base_typ) (cb : Ast.base_typ) : unit =
    match pb, cb with
    | Ast.B_int, Ast.B_int | Ast.B_bool, Ast.B_bool | Ast.B_float, Ast.B_float
    | Ast.B_unit, Ast.B_unit | Ast.B_string, Ast.B_string -> ()
    | Ast.B_app (l1, a1), Ast.B_app (l2, a2)
      when Ast.lid_eq l1 l2 && List.length a1 = List.length a2 -> List.iter2 go a1 a2
    | _ -> raise (Match_error "base type mismatch")
  in
  go pat concrete;
  List.rev_map (fun (_, b) -> b) !acc
