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

let () =
  if !failures > 0 then begin
    Printf.printf "%d failure(s)\n" !failures;
    exit 1
  end else print_endline "all passed"
