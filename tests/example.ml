(* example.ml — verification harness: builds a few Caml* declarations and prints
   them, exercising the stratified type grammar and the smart constructors. *)

open Ast

(* Helper to assemble a sigelt with no quals/attrs. *)
let se ?(quals = []) el =
  { sig_el = el; sig_quals = quals; sig_attrs = []; sig_rng = dummy_range }

(* A shared type variable 'a and the applied constructor `list 'a`. *)
let a       = fresh_tyvar "a"
let ta      = mk_base (B_var a)              (* the type 'a *)
let list_lid = lid_of_str "list"
let list_a  = mk_base (B_app (list_lid, [ta]))

(* Primitive/user function symbols used in refinements. *)
let len_lid  = lid_of_str "len"
let mem_lid  = lid_of_str "mem"
let plus_lid = lid_of_str "+"
let len (x : term) = mk_app (Tm_fvar len_lid) [x]

(* ----- 1. The `list` inductive: type params only, precision via refinements. ----- *)
let nil_lid  = lid_of_str "Nil"
let cons_lid = lid_of_str "Cons"

let nil_scheme  = { ts_vars = [a]; ts_typ = list_a }
let cons_scheme =
  { ts_vars = [a];
    ts_typ  = mk_arrow (fresh_var "hd") ta
                (mk_arrow (fresh_var "tl") list_a list_a) }

let list_inductive =
  Sig_inductive
    { ind_name = list_lid; ind_params = [a];
      ind_ctors = [ { dc_name = nil_lid;  dc_typ = nil_scheme };
                   { dc_name = cons_lid; dc_typ = cons_scheme } ] }

(* ----- 2. append : l1:list 'a -> l2:list 'a -> {r:list 'a | len r = len l1 + len l2} ----- *)
let l1 = fresh_var "l1"
let l2 = fresh_var "l2"
let r  = fresh_var "r"
let append_result =
  T_refine { rv = r; rbase = B_app (list_lid, [ta]);
             rphi = mk_eq (len (Tm_var r))
                          (mk_app (Tm_fvar plus_lid) [len (Tm_var l1); len (Tm_var l2)]) }
let append_scheme =
  { ts_vars = [a];
    ts_typ  = mk_arrow l1 list_a (mk_arrow l2 list_a append_result) }
let append_val = Sig_val (lid_of_str "append", append_scheme)

(* ----- 3. A lemma: forall 'a. x:'a -> l:list 'a -> squash (mem x (Cons x l)) ----- *)
let x = fresh_var "x"
let l = fresh_var "l"
let cons_x_l = mk_app (Tm_fvar cons_lid) [Tm_var x; Tm_var l]
let lemma_body = mk_squash (mk_app (Tm_fvar mem_lid) [Tm_var x; cons_x_l])
let lemma_scheme =
  { ts_vars = [a]; ts_typ = mk_arrow x ta (mk_arrow l list_a lemma_body) }
let mem_lemma = Sig_val (lid_of_str "mem_cons_head", lemma_scheme)

(* ----- 4a. An axiom with an annotated binder: assume refl : forall (n:int). n = n ----- *)
let n = fresh_var "n"
let refl_axiom =
  Sig_assume (lid_of_str "refl", mk_forall n (Some t_int) (mk_eq (Tm_var n) (Tm_var n)))

(* ----- 4b. An axiom with an unannotated binder: assume succ_gt : forall m. exists k. k = m + 1 ----- *)
let m = fresh_var "m"
let k = fresh_var "k"
let succ_gt_axiom =
  Sig_assume
    (lid_of_str "succ_gt",
     mk_forall m None
       (mk_exists k None
          (mk_eq (Tm_var k) (mk_app (Tm_fvar plus_lid) [Tm_var m; Tm_const (C_int 1)]))))

(* ----- 5. An expect_failure wrapping a (bogus) declaration. ----- *)
let bogus = se (Sig_val (lid_of_str "bad", mono t_bool))
let fail_block = Sig_fail ([bogus], [19])

let () =
  let decls =
    [ se list_inductive;
      se append_val;
      se mem_lemma;
      se refl_axiom;
      se succ_gt_axiom;
      se ~quals:[Q_assumption] (Sig_val (lid_of_str "opaque", mono t_int));
      se fail_block ]
  in
  List.iter (fun d -> print_endline (string_of_sigelt d); print_newline ()) decls
