(* specialize.ml — see specialize.mli. *)

open Ast

(* Apply [g] to each immediate subterm of [t] (not to types: binder annotations and
   ascriptions are kept as they are). The shared descent of the passes below. *)
let map_subterms (g : term -> term) (t : term) : term =
  match t with
  | Tm_var _ | Tm_fvar _ | Tm_const _ -> t
  | Tm_abs a -> Tm_abs { a with xbody = g a.xbody }
  | Tm_app (f, arg) -> Tm_app (g f, g arg)
  | Tm_let (lbs, body) ->
    Tm_let ({ lbs with lbs = List.map (fun lb -> { lb with lb_def = g lb.lb_def }) lbs.lbs },
            g body)
  | Tm_match (s, brs) ->
    Tm_match (g s, List.map (fun br ->
      { br with br_when = Option.map g br.br_when; br_body = g br.br_body }) brs)
  | Tm_ascribed (e, ty) -> Tm_ascribed (g e, ty)
  | Tm_quant q -> Tm_quant { q with qbody = g q.qbody }

(* ===== H3a: β-reduction ===== *)

(* Bottom-up: reduce the head and the argument first, then contract the redex and
   reduce its result again, since substituting a lambda for an applied variable makes
   a new redex. A curried application `(fun x y -> e) a b` is two nested redexes, each
   contracted in turn. Terminates on well-typed input: lambdas are not recursive (a
   recursive function is a `let rec`, never a `Tm_abs`), so the terms are simply typed. *)
let rec beta (t : term) : term =
  match t with
  | Tm_app (f, arg) ->
    (match beta f, beta arg with
     | Tm_abs a, arg -> beta (Subst.subst_term [ (a.xbinder, arg) ] a.xbody)
     | f, arg -> Tm_app (f, arg))
  | _ -> map_subterms beta t

let specialize_module ~(typed : modul) (parsed : modul) : modul =
  ignore typed;
  parsed
