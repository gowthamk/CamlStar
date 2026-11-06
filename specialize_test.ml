(* specialize_test.ml — unit tests for the helpers of specialize.ml (no solver, no
   parsing: terms are built directly, so each case states its input exactly).

   Usage: specialize_test   (exits nonzero if a test fails) *)

open Ast

let failures = ref 0

(* [got] must be alpha-equal to [want]: β-reduction renames bound variables. *)
let check (name : string) (got : term) (want : term) =
  if Subst.alpha_equal_term got want then Printf.printf "  PASS  %s\n" name
  else begin
    incr failures;
    Printf.printf "  FAIL  %s\n        got:  %s\n        want: %s\n"
      name (string_of_term got) (string_of_term want)
  end

let fv s = Tm_fvar (lid_of_str s)
let v x = Tm_var x
let lam x body = Tm_abs { xbinder = x; xtyp = None; xbody = body }
let app f args = mk_app f args

(* ===== H3a: beta ===== *)

let () =
  print_endline "beta:";
  let x = fresh_var "x" and y = fresh_var "y" and z = fresh_var "z"
  and w = fresh_var "w" and g = fresh_var "g" and a = fresh_var "a"
  and l = fresh_var "l" in

  (* one argument: (fun x -> S x) a  ~>  S a *)
  check "single redex"
    (Specialize.beta (app (lam x (app (fv "S") [ v x ])) [ v a ]))
    (app (fv "S") [ v a ]);

  (* curried, two arguments: (fun x y -> f x y) a z  ~>  f a z *)
  check "two arguments"
    (Specialize.beta (app (lam x (lam y (app (fv "f") [ v x; v y ]))) [ v a; v z ]))
    (app (fv "f") [ v a; v z ]);

  (* the contraction makes a new redex: (fun g -> g a) (fun x -> S x)  ~>  S a *)
  check "created redex (fixpoint)"
    (Specialize.beta (app (lam g (app (v g) [ v a ])) [ lam x (app (fv "S") [ v x ]) ]))
    (app (fv "S") [ v a ]);

  (* a redex inside the argument of a non-lambda head, under a binder (the shape a
     clone's body has after substitution):
     map (fun x -> (fun y -> S y) x) l  ~>  map (fun x -> S x) l *)
  check "redex under a lambda in an argument"
    (Specialize.beta
       (app (fv "map") [ lam x (app (lam y (app (fv "S") [ v y ])) [ v x ]); v l ]))
    (app (fv "map") [ lam x (app (fv "S") [ v x ]); v l ]);

  (* redexes in a match scrutinee and arm:
     match (fun x -> x) z with Z -> (fun y -> y) z | S w -> w
     ~>  match z with Z -> z | S w -> w *)
  let arms s0 s1 =
    [ { br_pat = P_cons (lid_of_str "Z", []); br_when = None; br_body = s0 };
      { br_pat = P_cons (lid_of_str "S", [ P_var w ]); br_when = None; br_body = s1 } ] in
  check "redex in scrutinee and arm"
    (Specialize.beta
       (Tm_match (app (lam x (v x)) [ v z ], arms (app (lam y (v y)) [ v z ]) (v w))))
    (Tm_match (v z, arms (v z) (v w)));

  (* capture: (fun x -> fun y -> f x y) y  ~>  fun y' -> f y y'  (the argument's free
     y is not captured by the inner binder) *)
  let y' = fresh_var "y" in
  check "capture-avoiding"
    (Specialize.beta (app (lam x (lam y (app (fv "f") [ v x; v y ]))) [ v y ]))
    (lam y' (app (fv "f") [ v y; v y' ]));

  (* partial application leaves a lambda: (fun x y -> f x y) a  ~>  fun y -> f a y *)
  check "partial application"
    (Specialize.beta (app (lam x (lam y (app (fv "f") [ v x; v y ]))) [ v a ]))
    (lam y (app (fv "f") [ v a; v y ]));

  (* no redex: unchanged. *)
  let t = app (fv "map") [ v g; app (fv "S") [ v a ] ] in
  check "no redex" (Specialize.beta t) t;

  (* a quantifier body: forall x. (fun y -> p y) x  ~>  forall x. p x *)
  let q body = Tm_quant { qk = Forall; qv = x; qty = None; qbody = body } in
  check "redex under a quantifier"
    (Specialize.beta (q (app (lam y (app (fv "p") [ v y ])) [ v x ])))
    (q (app (fv "p") [ v x ]))

(* ===== H3b: inline_local_lambdas ===== *)

let check_bool (name : string) (ok : bool) (detail : string) =
  if ok then Printf.printf "  PASS  %s\n" name
  else begin incr failures; Printf.printf "  FAIL  %s\n        %s\n" name detail end

let let1 ?(rec_ = false) h def body =
  Tm_let ({ lb_rec = rec_;
            lbs = [ { lb_name = h; lb_scheme = None; lb_def = def; lb_measure = None } ] },
          body)

let () =
  print_endline "inline_local_lambdas:";
  let x = fresh_var "x" and y = fresh_var "y" and z = fresh_var "z"
  and vv = fresh_var "v" and l = fresh_var "l" and g = fresh_var "g"
  and h = fresh_var "h" and ge = fresh_var "ge" in
  let inl = Specialize.inline_local_lambdas in
  let succ_lam () = lam y (app (fv "S") [ v y ]) in

  (* hof_local / OneShotLeader's shape, the local function passed and capturing v:
     let ge = fun x -> le v x in find ge l  ~>  find (fun x -> le v x) l *)
  check "passed, capturing"
    (inl (let1 ge (lam x (app (fv "le") [ v vv; v x ])) (app (fv "find") [ v ge; v l ])))
    (app (fv "find") [ lam x (app (fv "le") [ v vv; v x ]); v l ]);

  (* applied twice: let g = fun y -> S y in g (g x)
     ~>  (fun y -> S y) ((fun y -> S y) x), and with beta  S (S x) *)
  let twice = let1 g (succ_lam ()) (app (v g) [ app (v g) [ v x ] ]) in
  check "applied"
    (inl twice)
    (app (succ_lam ()) [ app (succ_lam ()) [ v x ] ]);
  check "applied, then beta"
    (Specialize.beta (inl twice))
    (app (fv "S") [ app (fv "S") [ v x ] ]);

  (* the two copies above have distinct binders (the second inference keys binder
     types by id) *)
  (match inl twice with
   | Tm_app (Tm_abs a1, Tm_app (Tm_abs a2, _)) ->
     check_bool "copies get fresh binders" (not (var_eq a1.xbinder a2.xbinder))
       (Printf.sprintf "both copies bind %s/%d" a1.xbinder.vname a1.xbinder.vid)
   | t -> check_bool "copies get fresh binders" false ("unexpected: " ^ string_of_term t));

  (* nested: let g = fun y -> S y in let h = fun z -> g z in h x  ~>(beta)  S x *)
  check "nested local functions, then beta"
    (Specialize.beta
       (inl (let1 g (succ_lam ()) (let1 h (lam z (app (v g) [ v z ])) (app (v h) [ v x ])))))
    (app (fv "S") [ v x ]);

  (* a local function inside a lambda argument:
     map (fun x -> let g = fun y -> S y in g x) l  ~>(beta)  map (fun x -> S x) l *)
  check "inside a lambda argument, then beta"
    (Specialize.beta
       (inl (app (fv "map") [ lam x (let1 g (succ_lam ()) (app (v g) [ v x ])); v l ])))
    (app (fv "map") [ lam x (app (fv "S") [ v x ]); v l ]);

  (* stays: a let of a non-function, and a let rec *)
  let plain = let1 z (app (fv "S") [ v x ]) (app (fv "f") [ v z ]) in
  check "non-function let stays" (inl plain) plain;
  let recl = let1 ~rec_:true g (lam y (app (v g) [ v y ])) (app (v g) [ v x ]) in
  check "let rec stays" (inl recl) recl;

  (* on parsed source, the surface form `let g y = … in` (which crashes the pipeline
     today: anf: unexpected node in value position) *)
  let m = Parse.parse_string {|
module LocalFo
type nat = | Z : nat | S : nat -> nat
let plus2 (x:nat) =
  let g y = S y in
  g (g x)
|} in
  let body = List.find_map (fun se -> match se.sig_el with
    | Sig_let { lbs = [ lb ]; _ } when lb.lb_name.vname = "plus2" -> Some lb.lb_def
    | _ -> None) m.mod_decls in
  match body with
  | Some (Tm_abs { xbinder = px; xbody; _ }) ->
    check "parsed `let g y = S y in g (g x)`, then beta"
      (Specialize.beta (inl xbody)) (app (fv "S") [ app (fv "S") [ v px ] ])
  | _ -> check_bool "parsed `let g y = S y in g (g x)`, then beta" false "plus2 not found"

(* ===== H3c: as_lambda ===== *)

let () =
  print_endline "as_lambda:";
  let nat = mk_base (B_app (lid_of_str "nat", [])) in
  let arrow d c = mk_arrow (fresh_var "_") d c in
  let nat_nat = arrow nat nat and nat_nat_bool = arrow nat (arrow nat t_bool) in
  let x = fresh_var "x" and y = fresh_var "y" and a = fresh_var "a"
  and vv = fresh_var "v" and f = fresh_var "f" in
  let asl = Specialize.as_lambda ~template:"map" in

  (* a lambda is returned as is *)
  let lm = lam x (app (fv "S") [ v x ]) in
  check_bool "lambda stays" (asl nat_nat lm == lm) "the lambda was rebuilt";

  (* names, η-expanded to the parameter's arity *)
  check "definition name, arity 1" (asl nat_nat (fv "succ")) (lam x (app (fv "succ") [ v x ]));
  check "definition name, arity 2" (asl nat_nat_bool (fv "le"))
    (lam x (lam y (app (fv "le") [ v x; v y ])));
  check "constructor name" (asl nat_nat (fv "S")) (lam x (app (fv "S") [ v x ]));

  (* composes with beta, as at a clone's `f a`: (as_lambda succ) a ~> succ a *)
  check "expanded name applied, then beta"
    (Specialize.beta (app (asl nat_nat (fv "succ")) [ v a ]))
    (app (fv "succ") [ v a ]);

  (* rejection C1, with the message of tests/hof_reject_returned.cst *)
  let rejects name arg want =
    match asl nat_nat arg with
    | t -> check_bool name false ("accepted as " ^ string_of_term t)
    | exception Specialize.Specialize_error msg ->
      check_bool name (msg = want) (Printf.sprintf "message: %s\n        want:    %s" msg want)
  in
  rejects "C1: an application (a computed function)" (app (fv "const_fn") [ v vv ])
    "map: the function argument `const_fn v` is not a lambda or a definition name";
  rejects "C1: a partial application (H12)" (app (fv "le") [ v vv ])
    "map: the function argument `le v` is not a lambda or a definition name";
  rejects "C1: a variable" (v f)
    "map: the function argument `f` is not a lambda or a definition name"

(* ===== H3d: captured, key_of, key_equal ===== *)

let () =
  print_endline "captured / key:";
  let x = fresh_var "x" and y = fresh_var "y" and vv = fresh_var "v"
  and ww = fresh_var "w" and c = fresh_var "c" in
  let names vs = String.concat ", " (List.map (fun x -> x.vname) vs) in
  let check_vars name got want =
    check_bool name (List.length got = List.length want && List.for_all2 var_eq got want)
      (Printf.sprintf "got [%s], want [%s]" (names got) (names want)) in
  let le_at a = lam x (app (fv "le") [ v a; v x ]) in

  (* captured: free local variables only, first occurrence first *)
  check_vars "captured: v, not the top-level le" (Specialize.captured [ le_at vv ]) [ vv ];
  check_vars "captured: order of first occurrence"
    (Specialize.captured [ lam x (app (fv "f") [ v ww; v vv; v x; v ww ]) ]) [ ww; vv ];
  check_vars "captured: bound variables are not"
    (Specialize.captured [ lam x (app (fv "le") [ v x; v x ]) ]) [];
  check_vars "captured: across two lambdas, shared once"
    (Specialize.captured [ le_at vv; lam y (app (fv "lt") [ v vv; v y ]) ]) [ vv ];

  (* the key's shape: find, fun c1 -> fun x -> le c1 x *)
  let k_v, cs_v = Specialize.key_of ~template:"find" [ le_at vv ] in
  check "key closes over c1" (List.hd k_v.Specialize.k_lams)
    (lam c (lam x (app (fv "le") [ v c; v x ])));
  check_vars "key_of returns the captured v" cs_v [ vv ];

  (* hof_capture: two sites, different captured values, one clone *)
  let k_w, cs_w = Specialize.key_of ~template:"find" [ le_at ww ] in
  check_bool "same shape, different captured value: equal keys"
    (Specialize.key_equal k_v k_w) "keys differ";
  check_vars "  and the second site passes w" cs_w [ ww ];

  let neq name k1 k2 =
    check_bool name (not (Specialize.key_equal k1 k2)) "keys are equal" in
  let key t lams = fst (Specialize.key_of ~template:t lams) in
  neq "different body (le vs lt): different keys" k_v
    (key "find" [ lam x (app (fv "lt") [ v vv; v x ]) ]);
  neq "different template: different keys" k_v (key "filter" [ le_at vv ]);
  neq "different capture pattern (v, w vs v, v): different keys"
    (key "find" [ lam x (app (fv "f") [ v vv; v ww; v x ]) ])
    (key "find" [ lam x (app (fv "f") [ v vv; v vv; v x ]) ]);

  (* no capture: alpha-equal lambdas, and two η-expansions of the same name *)
  check_bool "alpha-equal lambdas: equal keys"
    (Specialize.key_equal (key "map" [ lam x (app (fv "S") [ v x ]) ])
       (key "map" [ lam y (app (fv "S") [ v y ]) ])) "keys differ";
  let nat = mk_base (B_app (lid_of_str "nat", [])) in
  let succ () = Specialize.as_lambda ~template:"map" (mk_arrow (fresh_var "_") nat nat) (fv "succ") in
  check_bool "two expansions of `succ`: equal keys"
    (Specialize.key_equal (key "map" [ succ () ]) (key "map" [ succ () ])) "keys differ"

(* ===== H4: find_templates ===== *)

let () =
  print_endline "find_templates:";
  let templates src =
    let parsed = Parse.parse_string src in
    (parsed, Specialize.find_templates ~typed:(Infer.infer_module parsed) parsed) in
  let parsed, ts = templates {|
module T
type nat = | Z : nat | S : nat -> nat
type nlist = | NNil : nlist | NCons : nat -> nlist -> nlist
let rec len (l:nlist) = match l with | NNil -> Z | NCons x r -> S (len r)
let rec map (f:nat -> nat) (l:nlist) = match l with
  | NNil -> NNil
  | NCons x r -> NCons (f x) (map f r)
let apply_at (d:nat) (f:nat -> nat) = f d
let compose (f:nat -> nat) (g:nat -> nat) (x:nat) = f (g x)
let twice f x = S (f (f x))
val find_or : f:(nat -> bool) -> d:nat -> l:nlist -> nat
let rec find_or f d l = match l with
  | NNil -> d
  | NCons x r -> if f x then x else find_or f d r
|} in
  let show ts = String.concat "; " (List.map (fun t ->
    Printf.sprintf "%s [%s]" t.Specialize.t_name
      (String.concat "," (List.map (fun (i, _) -> string_of_int i) t.Specialize.t_funs))) ts) in
  let want = "map [0]; apply_at [1]; compose [0,1]; twice [0]; find_or [0]" in
  check_bool "templates and function-parameter positions (len is not one)"
    (show ts = want) (Printf.sprintf "got  %s\n        want %s" (show ts) want);
  check_bool "parameter types are arrows"
    (List.for_all (fun t -> List.for_all (fun (_, ty) ->
       match ty with T_arrow _ -> true | _ -> false) t.Specialize.t_funs) ts)
    "a non-arrow type";
  (* the binding is the parsed one: twice's `f` has no annotation there (the type came
     from inference) *)
  let parsed_twice = List.find_map (fun se -> match se.sig_el with
    | Sig_let { lbs = [ lb ]; _ } when lb.lb_name.vname = "twice" -> Some lb
    | _ -> None) parsed.mod_decls in
  (match List.find_opt (fun t -> t.Specialize.t_name = "twice") ts, parsed_twice with
   | Some t, Some lb ->
     check_bool "t_lb is the parsed binding, unannotated" (t.Specialize.t_lb == lb
       && (match lb.lb_def with Tm_abs { xtyp = None; _ } -> true | _ -> false))
       "not the parsed binding"
   | _ -> check_bool "t_lb is the parsed binding, unannotated" false "twice missing");

  (* a polymorphic template is an error (tests/hof_reject_poly.cst) *)
  let poly = {|
module P
type list 'a = | Nil : list 'a | Cons : 'a -> list 'a -> list 'a
let rec map (f:'a -> 'a) (l:list 'a) = match l with
  | Nil -> Nil
  | Cons x r -> Cons (f x) (map f r)
|} in
  let want = "map: a polymorphic template (type variable 'a) cannot be specialized; \
              write a monomorphic copy" in
  (match templates poly with
   | _ -> check_bool "polymorphic template rejected" false "accepted"
   | exception Specialize.Specialize_error msg ->
     check_bool "polymorphic template rejected" (msg = want)
       (Printf.sprintf "message: %s\n        want:    %s" msg want));

  (* the same, unannotated: the type variable is generalized by inference *)
  (match templates "module G\nlet twice f x = f (f x)\n" with
   | _ -> check_bool "polymorphic template rejected (inferred)" false "accepted"
   | exception Specialize.Specialize_error msg ->
     check_bool "polymorphic template rejected (inferred)"
       (String.length msg > 30 && String.sub msg 0 30 = "twice: a polymorphic template ") msg);

  (* a polymorphic first-order definition is not a template (tests/prop_list_append.cst) *)
  let _, ts = templates {|
module A
type list 'a = | Nil : list 'a | Cons : 'a -> list 'a -> list 'a
let rec app x y = match x with | Nil -> y | Cons h t -> Cons h (app t y)
val app_assoc : x:list 'a -> y:list 'a -> z:list 'a ->
        Lemma(ensures app (app x y) z = app x (app y z))
let rec app_assoc x y z = match x with | Nil -> () | Cons h t -> app_assoc t y z
|} in
  check_bool "polymorphic first-order definitions: no template" (ts = []) (show ts)

(* ===== H5a: clone_body ===== *)

(* Templates and, for each, the clone a person would write (named `<template>__0`). *)
let clone_src = {|
module C
type nat = | Z : nat | S : nat -> nat
type nlist = | NNil : nlist | NCons : nat -> nlist -> nlist
let rec le (x:nat) (y:nat) = match x with
  | Z -> true
  | S a -> (match y with | Z -> false | S b -> le a b)

let rec map (f:nat -> nat) (l:nlist) = match l with
  | NNil -> NNil
  | NCons x r -> NCons (f x) (map f r)
let rec map__0 (l:nlist) = match l with
  | NNil -> NNil
  | NCons x r -> NCons (S x) (map__0 r)

let rec filter (f:nat -> bool) (l:nlist) = match l with
  | NNil -> NNil
  | NCons x r -> if f x then NCons x (filter f r) else filter f r
let rec filter__0 c1 (l:nlist) = match l with
  | NNil -> NNil
  | NCons x r -> if le c1 x then NCons x (filter__0 c1 r) else filter__0 c1 r

let apply_at (d:nat) (f:nat -> nat) = f d
let apply_at__0 (d:nat) = S d

val find_or : f:(nat -> bool) -> d:nat -> l:nlist -> nat
let rec find_or f d l = match l with
  | NNil -> d
  | NCons x r -> if f x then x else find_or f d r
let rec find_or__0 c1 d l = match l with
  | NNil -> d
  | NCons x r -> if le c1 x then x else find_or__0 c1 d r

let map_twice (f:nat -> nat) (l:nlist) = map f (map f l)
let map_twice__0 (l:nlist) = map (fun y -> S y) (map (fun y -> S y) l)
|}

let () =
  print_endline "clone_body:";
  let parsed = Parse.parse_string clone_src in
  let ts = Specialize.find_templates ~typed:(Infer.infer_module parsed) parsed in
  let template n = List.find (fun t -> t.Specialize.t_name = n) ts in
  let expected n = List.find_map (fun se -> match se.sig_el with
    | Sig_let { lbs = [ lb ]; lb_rec } when lb.lb_name.vname = n -> Some (lb_rec, lb)
    | _ -> None) parsed.mod_decls |> Option.get in
  let y = fresh_var "y" and x = fresh_var "x" and vv = fresh_var "v" in
  let succ_lam = lam y (app (fv "S") [ v y ]) and le_v = lam x (app (fv "le") [ v vv; v x ]) in
  let clone n lams =
    let k, _ = Specialize.key_of ~template:n lams in
    Specialize.clone_body (template n) k ~name:(n ^ "__0") in
  let check_clone label n lams =
    let got = clone n lams in
    let lb = List.hd got.lbs and erec, elb = expected (n ^ "__0") in
    (* the hand-written clone refers to itself by its own binder; rename it to ours *)
    let want = Subst.subst_term [ (elb.lb_name, Tm_var lb.lb_name) ] elb.lb_def in
    check label lb.lb_def want;
    check_bool (label ^ ": rec flag") (got.lb_rec = erec)
      (Printf.sprintf "rec = %b, want %b" got.lb_rec erec) in

  check_clone "map at fun y -> S y (self-call rewritten)" "map" [ succ_lam ];
  check_clone "filter at fun x -> le v x (captured v first)" "filter" [ le_v ];
  check_clone "apply_at at fun y -> S y (function parameter second, not rec)" "apply_at" [ succ_lam ];
  check_clone "find_or (val-typed, unannotated) at fun x -> le v x" "find_or" [ le_v ];
  check_clone "map_twice: a call of another template stays (H6 specializes it)" "map_twice" [ succ_lam ];

  (* two clones of one template share no binder *)
  let p c = match (List.hd c.lbs).lb_def with Tm_abs a -> a.xbinder | _ -> fresh_var "?" in
  let c1 = clone "map" [ succ_lam ] and c2 = clone "map" [ lam y (v y) ] in
  check_bool "two clones of map: distinct parameter binders" (not (var_eq (p c1) (p c2)))
    "both bind the same l";

  (* rejection C2, with the message of tests/hof_reject_changing.cst *)
  let iter_src = {|
module I
type nat = | Z : nat | S : nat -> nat
let rec iter (f:nat -> nat) (n:nat) (x:nat) = match n with
  | Z -> x
  | S m -> iter (fun y -> f (f y)) m x
|} in
  let ip = Parse.parse_string iter_src in
  let it = List.hd (Specialize.find_templates ~typed:(Infer.infer_module ip) ip) in
  let k, _ = Specialize.key_of ~template:"iter" [ succ_lam ] in
  let want = "iter: the recursive call passes `fun y -> f (f y)` for `f`, not `f` itself; \
              specialization would not terminate" in
  (match Specialize.clone_body it k ~name:"iter__0" with
   | _ -> check_bool "C2: a self-call changing f" false "accepted"
   | exception Specialize.Specialize_error msg ->
     check_bool "C2: a self-call changing f" (msg = want)
       (Printf.sprintf "message: %s\n        want:    %s" msg want))

let () =
  if !failures > 0 then begin
    Printf.printf "%d failure(s)\n" !failures;
    exit 1
  end else print_endline "all passed"
