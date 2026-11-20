(* inline.ml — unfold quantified definitions at their uses.

   A definition whose body is a quantified formula (Axioms.quantified_defs) has no
   equation and no declaration: wherever a spec or proof applies it, the application is
   replaced by the body with the arguments substituted for the parameters. The
   quantifier then sits in the goal or hypothesis, where NNF, Skolemization and
   instantiation already handle it. Substitution is Subst.subst_term, which freshens
   every binder it passes, so two unfoldings of one body in one formula share no
   bound variable.

   A body may apply other quantified definitions, so the pass repeats until nothing
   changes; the definitions are non-recursive, so this terminates, and a bound turns a
   cycle (a `let … and …` group) into an error naming the definition. *)

open Ast

type def = { params : var list; body : term }

let rec peel_all (e : term) : var list * term =
  match e with
  | Tm_abs { xbinder; xbody; _ } -> let ps, b = peel_all xbody in (xbinder :: ps, b)
  | _ -> ([], e)

let table (m : modul) : (string * def) list =
  let names = Axioms.quantified_defs m in
  List.concat_map
    (fun se ->
      match se.sig_el with
      | Sig_let lbs ->
        List.filter_map
          (fun lb ->
            if List.mem lb.lb_name.vname names then
              let params, body = peel_all lb.lb_def in
              Some (lb.lb_name.vname, { params; body })
            else None)
          lbs.lbs
      | _ -> [])
    m.mod_decls

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

let any = List.exists Fun.id

(* one pass over [t]: every saturated application of a table name is replaced by the
   body; returns the new term and whether anything was replaced *)
let rec pass (tbl : (string * def) list) (t : term) : term * bool =
  match t with
  | Tm_var _ | Tm_fvar _ | Tm_const _ -> (t, false)
  | Tm_app _ ->
    let head, args = spine t [] in
    let args', cs = List.split (List.map (pass tbl) args) in
    (match head with
     | Tm_fvar l
       when (match List.assoc_opt l.bname tbl with
             | Some d -> List.length d.params = List.length args'
             | None -> false) ->
       let d = List.assoc l.bname tbl in
       (Subst.subst_term (List.combine d.params args') d.body, true)
     | _ ->
       let head', c = pass tbl head in
       (mk_app head' args', c || any cs))
  | Tm_abs a -> let b, c = pass tbl a.xbody in (Tm_abs { a with xbody = b }, c)
  | Tm_quant q -> let b, c = pass tbl q.qbody in (Tm_quant { q with qbody = b }, c)
  | Tm_let (lbs, body) ->
    let lbs', cs =
      List.split
        (List.map (fun lb -> let d, c = pass tbl lb.lb_def in ({ lb with lb_def = d }, c))
           lbs.lbs)
    in
    let body', c = pass tbl body in
    (Tm_let ({ lbs with lbs = lbs' }, body'), c || any cs)
  | Tm_match (s, brs) ->
    let s', c0 = pass tbl s in
    let brs', cs =
      List.split
        (List.map
           (fun br ->
             let w, cw =
               match br.br_when with
               | Some w -> let w', c = pass tbl w in (Some w', c)
               | None -> (None, false)
             in
             let b, cb = pass tbl br.br_body in
             ({ br with br_when = w; br_body = b }, cw || cb))
           brs)
    in
    (Tm_match (s', brs'), c0 || any cs)
  | Tm_ascribed (e, ty) -> let e', c = pass tbl e in (Tm_ascribed (e', ty), c)

(* the first table name applied anywhere in [t], for the error message *)
let rec first_name (tbl : (string * def) list) (t : term) : string option =
  match t with
  | Tm_var _ | Tm_const _ -> None
  | Tm_fvar l -> if List.mem_assoc l.bname tbl then Some l.bname else None
  | Tm_app (f, a) -> (match first_name tbl f with Some n -> Some n | None -> first_name tbl a)
  | Tm_abs a -> first_name tbl a.xbody
  | Tm_quant q -> first_name tbl q.qbody
  | Tm_let (lbs, body) ->
    List.fold_left
      (fun acc lb -> match acc with Some _ -> acc | None -> first_name tbl lb.lb_def)
      (first_name tbl body) lbs.lbs
  | Tm_match (s, brs) ->
    List.fold_left
      (fun acc br -> match acc with Some _ -> acc | None -> first_name tbl br.br_body)
      (first_name tbl s) brs
  | Tm_ascribed (e, _) -> first_name tbl e

let max_passes = 32

let expand (m : modul) (t : term) : term =
  match table m with
  | [] -> t
  | tbl ->
    let rec go n t =
      let t', changed = pass tbl t in
      if not changed then t'
      else if n >= max_passes then
        failwith
          (Printf.sprintf
             "quantified definition %s unfolds into itself: a quantified predicate cannot be recursive"
             (match first_name tbl t' with Some s -> s | None -> "?"))
      else go (n + 1) t'
    in
    go 0 t
