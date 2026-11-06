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

(* ===== H3b: inlining local function lets ===== *)

(* `let h = fun x -> e in b` ~> `b[h := fun x -> e]`, bottom-up (the lambda and [b] are
   inlined first, so nested local functions all go). Every non-recursive single
   binding whose definition is a lambda is inlined, whatever its uses: today the
   pipeline crashes on any local function let (`anf: unexpected node in value
   position`, first-order ones included), and a use specialization cannot handle (a
   function stored in a constructor) is rejected later. A `let rec` and an `and` group
   stay. [Subst.subst_term] inserts the same lambda at every occurrence, so the result
   is freshened: each copy gets its own binders, which the second inference needs
   (it records binder types by id, and a let-bound lambda may be used at two types). *)
let rec inline_local_lambdas (t : term) : term =
  match t with
  | Tm_let ({ lb_rec = false; lbs = [ lb ] }, body) ->
    (match inline_local_lambdas lb.lb_def with
     | Tm_abs _ as def ->
       Subst.freshen_term (Subst.subst_term [ (lb.lb_name, def) ] (inline_local_lambdas body))
     | def -> Tm_let ({ lb_rec = false; lbs = [ { lb with lb_def = def } ] },
                      inline_local_lambdas body))
  | _ -> map_subterms inline_local_lambdas t

(* ===== H3c: a function argument as a lambda ===== *)

exception Specialize_error of string

(* The number of arguments a function of type [ty] takes: its arrows, curried. *)
let rec arity (ty : typ) : int =
  match ty with
  | T_arrow a -> 1 + arity a.acod
  | T_refine _ -> 0

(* A lambda stays. A top-level name (a definition, an `assume val`, a constructor) is
   η-expanded to the arity of the parameter it is passed for, [pty]: `succ` at
   `f:(nat -> nat)` becomes `fun x -> succ x`. Taking the arity from the parameter, not
   from the name's own type, gives the lambda exactly the parameter's shape. Anything
   else has no body to substitute (rejection C1): an application such as `const_fn v`
   (a function computed at run time), a partial application `le v` (plan step H12),
   a variable (a function parameter passed on; a local function let is already gone
   by [inline_local_lambdas]). Terms carry no location, so the caller adds the
   declaration's. *)
let as_lambda ~(template : string) (pty : typ) (arg : term) : term =
  match arg with
  | Tm_abs _ -> arg
  | Tm_fvar _ ->
    let xs = List.init (arity pty) (fun i -> fresh_var (Printf.sprintf "x%d" (i + 1))) in
    List.fold_right (fun x body -> Tm_abs { xbinder = x; xtyp = None; xbody = body })
      xs (mk_app arg (List.map (fun x -> Tm_var x) xs))
  | _ ->
    raise (Specialize_error (Printf.sprintf
      "%s: the function argument `%s` is not a lambda or a definition name"
      template (string_of_term arg)))

(* ===== H3d: captured variables and the clone key ===== *)

(* One clone per key: the template and its function arguments with the captured
   variables abstracted. `find (fun x -> le v x)` and `find (fun x -> le w x)` share the
   key `find, fun c1 -> fun x -> le c1 x`, so one clone `find__0 c1 l` serves both
   sites, called as `find__0 v l` and `find__0 w l`. *)
type key = { k_template : string; k_lams : term list }

(* The lambdas' free local variables (top-level names are `Tm_fvar`, never captured),
   in order of first occurrence across [lams]: the same order for two lambdas of the
   same shape, which the key relies on. *)
let captured (lams : term list) : var list =
  List.fold_left (fun acc x -> if List.exists (var_eq x) acc then acc else acc @ [ x ])
    [] (List.concat_map Subst.free_vars_term lams)

(* The key, and the captured variables (the clone's extra first arguments at this call
   site). Each lambda is closed over the same fresh binders `c1 … ck`, so position j
   stands for the same captured variable in every component. *)
let key_of ~(template : string) (lams : term list) : key * var list =
  let cs = captured lams in
  let cs' = List.mapi (fun i _ -> fresh_var (Printf.sprintf "c%d" (i + 1))) cs in
  let s = List.map2 (fun c c' -> (c, Tm_var c')) cs cs' in
  let close lam =
    List.fold_right (fun c body -> Tm_abs { xbinder = c; xtyp = None; xbody = body })
      cs' (Subst.subst_term s lam) in
  ({ k_template = template; k_lams = List.map close lams }, cs)

let key_equal (a : key) (b : key) : bool =
  String.equal a.k_template b.k_template
  && List.length a.k_lams = List.length b.k_lams
  && List.for_all2 Subst.alpha_equal_term a.k_lams b.k_lams

let specialize_module ~(typed : modul) (parsed : modul) : modul =
  ignore typed;
  parsed
