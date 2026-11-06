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
type key = { k_template : string; k_lams : term list; k_ncaptured : int }

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
  ({ k_template = template; k_lams = List.map close lams; k_ncaptured = List.length cs }, cs)

let key_equal (a : key) (b : key) : bool =
  String.equal a.k_template b.k_template
  && List.length a.k_lams = List.length b.k_lams
  && List.for_all2 Subst.alpha_equal_term a.k_lams b.k_lams

(* ===== H4: templates ===== *)

(* A top-level definition with at least one parameter of function type. [t_lb] is the
   parsed binding (the clone is copied from it), [t_funs] the positions of its function
   parameters (0-based) with their types, [t_scheme] its type from [typed], [t_val]
   the user's `val` from [parsed], refinements included (inference erases a `val` to
   its shape, so [t_scheme] has none). *)
type template = { t_name : string; t_lb : letbinding; t_funs : (int * typ) list;
                  t_scheme : tscheme; t_val : tscheme option }

(* The function-typed parameters of a type: the domains of its arrows that are arrows. *)
let fun_params (ty : typ) : (int * typ) list =
  let rec go i ty = match ty with
    | T_arrow { adom = T_arrow _ as d; acod; _ } -> (i, d) :: go (i + 1) acod
    | T_arrow { acod; _ } -> go (i + 1) acod
    | T_refine _ -> [] in
  go 0 ty

(* Types come from [typed]: every top-level binding there has a scheme, the user's `val`
   or the inferred one, and inference keeps the binders, so a parsed binding is found
   by its variable id. A polymorphic template has no sort to specialize at (no
   polymorphism in the encoding), so it is an error. Top-level `let`s only; those
   inside `expect_failure` are not looked at. *)
let find_templates ~(typed : modul) (parsed : modul) : template list =
  let schemes = Hashtbl.create 16 in
  List.iter (fun se -> match se.sig_el with
    | Sig_let lbs ->
      List.iter (fun lb -> Option.iter (Hashtbl.replace schemes lb.lb_name.vid) lb.lb_scheme)
        lbs.lbs
    | _ -> ()) typed.mod_decls;
  let vals = List.filter_map (fun se -> match se.sig_el with
    | Sig_val (l, sch) -> Some (l.bname, sch) | _ -> None) parsed.mod_decls in
  List.concat_map (fun se -> match se.sig_el with
    | Sig_let lbs ->
      List.filter_map (fun lb ->
        match Hashtbl.find_opt schemes lb.lb_name.vid with
        | None -> None
        | Some sch ->
          (match fun_params sch.ts_typ with
           | [] -> None
           | funs ->
             (* the type's variables, not [ts_vars]: a `'a` written in a binder
                annotation is rigid during inference and is not generalized *)
             (match Subst.free_tyvars_typ sch.ts_typ with
              | tv :: _ ->
                raise (Specialize_error (Printf.sprintf
                  "%s: a polymorphic template (type variable '%s) cannot be specialized; \
                   write a monomorphic copy" lb.lb_name.vname tv.tvname))
              | [] ->
                Some { t_name = lb.lb_name.vname; t_lb = lb; t_funs = funs; t_scheme = sch;
                       t_val = List.assoc_opt lb.lb_name.vname vals })))
        lbs.lbs
    | _ -> []) parsed.mod_decls

(* ===== H5a: the clone's body ===== *)

let spine (t : term) : term * term list =
  let rec go t args = match t with Tm_app (f, a) -> go f (a :: args) | h -> (h, args) in
  go t []

let rec peel_abs (t : term) : abs list * term =
  match t with
  | Tm_abs a -> let ps, b = peel_abs a.xbody in (a :: ps, b)
  | b -> ([], b)

(* The clone of template [t] at key [k], named [name]:
     let [rec] name c1 … ck p̄ = body[f̄ := λ̄]   (β-reduced, self-calls rewritten)
   where p̄ are the template's non-function parameters (annotations kept) and λ̄ the
   key's lambdas opened at the clone's own c1 … ck (k.k_lams are in t.t_funs order).
   Self-calls are rewritten first, while the function parameters are still variables:
   `g … f … ā` becomes `name c1 … ck ā` (the captured values do not change along the
   recursion, since `f` is passed unchanged). A self-call that passes anything other
   than `f` itself for `f` would need a new clone per unfolding (rejection C2). In the
   parsed tree a recursive definition refers to itself as `Tm_var` of its own binding,
   and other declarations refer to it as `Tm_fvar`. The result is freshened, so two
   clones of one template share no binder. *)
let clone_body (t : template) (k : key) ~(name : string) : letbindings =
  let err fmt = Printf.ksprintf (fun s -> raise (Specialize_error s)) fmt in
  let params, body = peel_abs t.t_lb.lb_def in
  let nfun = 1 + List.fold_left (fun m (i, _) -> max m i) 0 t.t_funs in
  if List.length params < nfun then
    err "%s: a function parameter is not written as a parameter of the definition" t.t_name;
  let is_fun i = List.mem_assoc i t.t_funs in
  let fparams = List.map (fun (i, _) -> (List.nth params i).xbinder) t.t_funs in
  let others = List.filteri (fun i _ -> not (is_fun i)) params in
  let self = t.t_lb.lb_name and clone_v = fresh_var name in
  let cs = List.init k.k_ncaptured (fun i -> fresh_var (Printf.sprintf "c%d" (i + 1))) in
  let cargs = List.map (fun c -> Tm_var c) cs in
  let rec rw e =
    match e with
    | Tm_app _ ->
      (match spine e with
       | (Tm_var x, args) when var_eq x self ->
         if List.length args < nfun then
           err "%s: a recursive call without all its function arguments is not supported"
             (self.vname);
         List.iter2 (fun (i, _) f ->
           match List.nth args i with
           | Tm_var y when var_eq y f -> ()
           | a -> err "%s: the recursive call passes `%s` for `%s`, not `%s` itself; \
                       specialization would not terminate"
                    self.vname (string_of_term a) f.vname f.vname)
           t.t_funs fparams;
         mk_app (Tm_var clone_v) (cargs @ List.map rw (List.filteri (fun i _ -> not (is_fun i)) args))
       | (h, args) -> mk_app (rw h) (List.map rw args))
    | Tm_var x when var_eq x self ->
      err "%s: a recursive reference without its function arguments is not supported"
        self.vname
    | _ -> map_subterms rw e
  in
  let lams = List.map (fun l -> beta (mk_app l cargs)) k.k_lams in
  let inner = List.fold_right (fun a b -> Tm_abs { a with xbody = b }) others (rw body) in
  let inner = beta (Subst.subst_term (List.combine fparams lams) inner) in
  let def = List.fold_right (fun c b -> Tm_abs { xbinder = c; xtyp = None; xbody = b }) cs inner in
  let def = Subst.freshen_term def in
  let is_rec = List.exists (var_eq clone_v) (Subst.free_vars_term def) in
  { lb_rec = is_rec;
    lbs = [ { lb_name = clone_v; lb_scheme = None; lb_def = def; lb_measure = None } ] }

(* ===== H5b: the clone's `val` ===== *)

(* β-reduce every refinement formula in a type ([beta] does not enter types). *)
let rec beta_typ (ty : typ) : typ =
  match ty with
  | T_refine r -> T_refine { r with rphi = beta r.rphi }
  | T_arrow a -> T_arrow { a with adom = beta_typ a.adom; acod = beta_typ a.acod }

(* The template's `val` at key [k]: each function binder dropped and its lambda (opened
   at the `val`'s own fresh c1 … ck) substituted in the rest of the type, every
   refinement β-reduced, and arrows `cj : ctypes_j` put first. The binder names of a
   `val` are its own (they need not be the definition's parameter names), and arrow
   position i is parameter position i, as in [t_funs]. [ctypes] are the captured
   variables' types; they are an input because the parsed tree does not have them and
   the typed tree has them only for some binders (a pattern variable gets none), so
   the caller reads them off the clone's inferred parameters. None when the template
   has no `val`. *)
let clone_val (t : template) (k : key) ~(ctypes : typ list) : tscheme option =
  match t.t_val with
  | None -> None
  | Some sch ->
    let cs = List.mapi (fun i _ -> fresh_var (Printf.sprintf "c%d" (i + 1))) ctypes in
    let lams = List.map (fun l -> beta (mk_app l (List.map (fun c -> Tm_var c) cs))) k.k_lams in
    let fun_lam = List.combine (List.map fst t.t_funs) lams in
    let rec drop i ty =
      match ty with
      | T_arrow a ->
        (match List.assoc_opt i fun_lam with
         | Some lam -> drop (i + 1) (Subst.subst_typ [ (a.abinder, lam) ] a.acod)
         | None -> T_arrow { a with acod = drop (i + 1) a.acod })
      | T_refine _ -> ty in
    let body = beta_typ (drop 0 sch.ts_typ) in
    let ty = List.fold_right2 (fun c cty acc -> T_arrow { abinder = c; adom = cty; acod = acc })
        cs ctypes body in
    Some { ts_vars = []; ts_typ = ty }

let specialize_module ~(typed : modul) (parsed : modul) : modul =
  ignore typed;
  parsed
