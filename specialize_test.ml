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

let () =
  if !failures > 0 then begin
    Printf.printf "%d failure(s)\n" !failures;
    exit 1
  end else print_endline "all passed"
