(* cegqi_test.ml — unit tests for the CEGQI analysis (no solver involved).

   Each test drives the real pipeline (parse -> infer -> check) to obtain VCs, then asserts
   on [Cegqi.shapes] / [Cegqi.candidates] / [Cegqi.eval_in_cex]. Sources are the bundled
   Examples with their instantiate! hints stripped, so what we assert is exactly the hint a
   human would have had to write. *)

let failures = ref 0

let check (name : string) (ok : bool) (detail : string) =
  if ok then Printf.printf "  PASS  %s\n" name
  else begin
    incr failures;
    Printf.printf "  FAIL  %s\n        %s\n" name detail
  end

let vcs_of (src : string) : Ast.modul * Vc.t list =
  let m = Infer.infer_module (Parse.parse_string src) in
  (m, Check.check_module m)

(* every candidate CEGQI would add, across all VCs of a module, as printed terms *)
let all_candidates (src : string) : string list =
  let m, vcs = vcs_of src in
  List.concat_map (fun vc -> List.map Ast.string_of_term (Cegqi.candidates m vc)) vcs

let all_shapes (src : string) : string list =
  let m, vcs = vcs_of src in
  List.concat_map
    (fun vc ->
      List.map (fun (_, t) -> Ast.string_of_term t) (Cegqi.shapes m vc))
    vcs

(* ===== sources (Examples/*.cst, hints removed) ===== *)

let prop22 = {|
module Prop22
type nat = | Z : nat | S : nat -> nat
let rec max x y = match x with
  | Z -> y
  | S x' -> (match y with
             | Z -> x
             | S y' -> S (max x' y'))
val tip_22 : a:nat -> b:nat -> c:nat -> Lemma(ensures max (max a b) c = max a (max b c))
let rec tip_22 a b c = match a with
  | Z -> ()
  | S a' -> (match b with
             | Z -> ()
             | S b' -> (match c with
                        | Z -> ()
                        | S c' -> tip_22 a' b' c'))
|}

let prop77 = {|
module Prop77
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec le x y = match x with
  | Z -> true
  | S x' -> (match y with
             | Z -> false
             | S y' -> le x' y')
let rec insort x xs = match xs with
  | Nil -> Cons x Nil
  | Cons h t -> let p = le x h in if p then Cons x (Cons h t) else Cons h (insort x t)
let rec sorted xs = match xs with
  | Nil -> true
  | Cons h t -> (match t with
                 | Nil -> true
                 | Cons h2 t2 -> let p = le h h2 in if p then sorted (Cons h2 t2) else false)
val tip_77 : x:nat -> xs:natlist -> Lemma(ensures sorted xs ==> sorted (insort x xs))
let rec tip_77 x xs = match xs with
  | Nil -> ()
  | Cons h t -> (match t with
                 | Nil -> ()
                 | Cons h2 t2 -> tip_77 x t)
|}

(* prop04 without eq_refl: the obligation needs a lemma, so CEGQI must saturate *)
let prop04 = {|
module Prop04
type nat = | Z : nat | S : nat -> nat
type natlist = | Nil : natlist | Cons : nat -> natlist -> natlist
let rec eq_nat x y = match x with
  | Z -> (match y with
          | Z -> true
          | S y' -> false)
  | S x' -> (match y with
             | Z -> false
             | S y' -> eq_nat x' y')
let rec count x xs = match xs with
  | Nil -> Z
  | Cons h t -> let p = eq_nat x h in if p then S (count x t) else count x t
val tip_04 : n:nat -> xs:natlist -> Lemma(ensures S (count n xs) = count n (Cons n xs))
let tip_04 n xs = match xs with
  | Nil -> ()
  | Cons x xs' -> tip_04 n xs'
|}

let () =
  print_endline "cegqi_test";

  (* --- shapes: the arm's discriminators are recovered from the hypotheses --- *)
  let sh22 = all_shapes prop22 in
  check "shapes/prop22 finds S-shapes" (List.exists (fun s -> s = "S a'") sh22)
    (String.concat ", " sh22);
  check "shapes/prop22 finds the nullary Z shape" (List.mem "Z" sh22)
    (String.concat ", " sh22);
  let sh77 = all_shapes prop77 in
  check "shapes/prop77 finds Cons and Nil"
    (List.exists (fun s -> s = "Cons h t") sh77 && List.mem "Nil" sh77)
    (String.concat ", " sh77);

  (* --- unroll/candidates: exactly the hints a human writes --- *)
  let c22 = all_candidates prop22 in
  check "prop22 proposes S (max a' b')" (List.mem "S (max a' b')" c22)
    (String.concat " | " c22);

  let c77 = all_candidates prop77 in
  (* the t = Nil arm: the hand-written hint is [Cons h (insort x t)]; shapes are expanded
     before matching, so the same instance comes out with [t] replaced by [Nil] *)
  check "prop77 proposes the else-branch list (t = Nil arm)"
    (List.mem "Cons h (insort x Nil)" c77) (String.concat " | " c77);
  check "prop77 proposes the then-branch list (t = Nil arm)"
    (List.mem "Cons x (Cons h Nil)" c77) (String.concat " | " c77);
  (* the deeper t = Cons h2 t2 arm reproduces the hand-written hint verbatim *)
  check "prop77 proposes Cons h2 (insort x t2) (deeper arm)"
    (List.mem "Cons h2 (insort x t2)" c77) (String.concat " | " c77);
  check "prop77 proposes the guard call le x h"
    (List.exists (fun s -> s = "le x h") c77) (String.concat " | " c77);
  check "prop77 unfolds the sorted predicate too"
    (List.mem "sorted (Cons h2 t2)" c77) (String.concat " | " c77);

  (* --- saturation: nothing to instantiate when the gap is a lemma --- *)
  let c04 = all_candidates prop04 in
  check "prop04 saturates on the opaque-guard arm"
    (not (List.mem "S (count n (Cons n xs))" c04))
    (String.concat " | " c04);

  (* --- eval_in_cex: a tuple absent from a function's map is undefined --- *)
  let a = Ast.fresh_var "a" and b = Ast.fresh_var "b" in
  let app f args = Ast.mk_app (Ast.Tm_fvar (Ast.lid_of_str f)) args in
  let cex : Cex.t =
    [ ("a", Cex.Scalar "nat!1");
      ("b", Cex.Scalar "nat!3");
      ("max", Cex.Entries [ ([ Cex.Scalar "nat!1"; Cex.Scalar "nat!3" ], Cex.Scalar "nat!6") ]);
      ("le", Cex.Entries [ ([ Cex.Scalar "nat!1"; Cex.Scalar "nat!3" ], Cex.Scalar "false") ]) ]
  in
  check "eval_in_cex reads a defined application"
    (Cegqi.eval_in_cex cex (app "max" [ Ast.Tm_var a; Ast.Tm_var b ]) = Some (Cex.Scalar "nat!6"))
    "expected nat!6";
  check "eval_in_cex reports an absent tuple as undefined"
    (Cegqi.eval_in_cex cex (app "max" [ Ast.Tm_var b; Ast.Tm_var a ]) = None)
    "expected None for (nat!3, nat!1)";
  check "eval_in_cex reads a bool predicate (always total)"
    (Cegqi.eval_in_cex cex (app "le" [ Ast.Tm_var a; Ast.Tm_var b ]) = Some (Cex.Scalar "false"))
    "expected false";
  check "eval_in_cex renders a nullary constructor as itself"
    (Cegqi.eval_in_cex cex (Ast.Tm_fvar (Ast.lid_of_str "Z")) = Some (Cex.Scalar "Z"))
    "expected Z";

  if !failures = 0 then print_endline "all cegqi tests passed"
  else (Printf.printf "%d failure(s)\n" !failures; exit 1)
