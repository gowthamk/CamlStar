(* smt.ml — see smt.mli. *)

open Ast

type verdict = Verified | Failed | Unknown | Solver_error of string

(* [Failed] = z3 returned sat: a counterexample to the (negated) VC. Under
   relational abstraction the relations *over*approximate the functions (no
   totality is asserted, to stay in EPR), so such a counterexample may be spurious
   rather than a genuine refutation. *)
let string_of_verdict = function
  | Verified -> "verified" | Failed -> "counterexample" | Unknown -> "unknown"
  | Solver_error s -> "solver error: " ^ s

(* ===== the transform pipeline =====
   ANF -> NNF -> relabs, exactly as Raven normalises goals and definitional axioms.
   The relabs binder sorts come from the module's function/constructor return sorts. *)
let make_ret_sort (m : modul) : string -> base_typ =
  let tbl = Axioms.ret_sort_table m in
  fun name -> match Hashtbl.find_opt tbl name with Some b -> b | None -> B_app (lid_of_str name, [])

(* full positive pipeline, for globally-true formulas (definitional equations, assumes) *)
let full_transform (ret_sort : string -> base_typ) (t : term) : term =
  Relabs.transform ret_sort (Nnf.normalize (Anf.normalize t))

(* ===== auto-instantiation (cf. raven/frontend/src/auto_inst.rs) =====
   Collect the ground applied subterms of a VC — the abstract calls ANF hoisted to
   top-level lets, i.e. those NOT under a quantifier — and materialise each as
   [exists v. f_rel(atoms, v)] so the universal axioms have ground terms to fire on. *)

let single_let (x : var) (def : term) (body : term) : term =
  Tm_let ({ lb_rec = false;
            lbs = [ { lb_name = x; lb_scheme = None; lb_def = def; lb_measure = None } ] },
          body)

let rec spine (t : term) (acc : term list) : term * term list =
  match t with Tm_app (f, a) -> spine f (a :: acc) | _ -> (t, acc)

(* the (var, call) bindings ANF produced, in outer-to-inner order, descending
   through lets and connectives but NOT into quantifier bodies (those bind the
   variables the calls would depend on) *)
let ground_lets (anf_f : term) : (var * term) list =
  let rec go acc t =
    match t with
    | Tm_let ({ lbs = [ lb ]; _ }, body) -> go ((lb.lb_name, lb.lb_def) :: acc) body
    | Tm_app _ ->
      let h, args = spine t [] in
      (match h with
       | Tm_fvar l when Smtlib.is_connective l.bname -> List.fold_left go acc args
       | _ -> acc)
    | _ -> acc                                   (* Tm_quant / atom: stop *)
  in
  List.rev (go [] anf_f)

let materialization (ret_sort : string -> base_typ) (anf_f : term) : term option =
  match ground_lets anf_f with
  | [] -> None
  | binds ->
    let chain = List.fold_right (fun (x, def) body -> single_let x def body) binds mk_true in
    Some (Relabs.transform_neg ret_sort chain)

(* Declarations for the module's datatypes + function relations. *)
let global_sort_decls (m : modul) : string list = Axioms.datatype_sort_decls m
let global_rel_decls  (m : modul) : string list = Axioms.constructor_decls m @ Axioms.function_decls m

(* Axioms already in relational EPR form (functionality/injectivity/disjointness +
   function functionality): asserted verbatim, like Raven's axioms.rs pass. *)
let global_final_axioms (m : modul) : term list =
  Axioms.datatype_axioms m @ Axioms.function_axioms m

(* Axioms with bare calls that must go through the ANF/NNF/relabs pipeline: the
   definitional equations of unspecified functions. *)
let global_raw_axioms (m : modul) : term list = Axioms.definitional_axioms m

(* ===== per-VC formula ===== *)

let conj : term list -> term = function
  | [] -> mk_true
  | h :: t -> List.fold_left mk_and h t

(* The refutation formula: (/\ hyps) /\ ~goal. *)
let vc_formula (vc : Vc.t) : term =
  let ng = mk_not vc.Vc.goal in
  match vc.Vc.hyps with [] -> ng | hs -> mk_and (conj hs) ng

(* declare-sort lines for the non-builtin sorts appearing in [scope], plus a
   declare-const for each scoped variable. *)
let scope_decls (scope : (var * base_typ) list) : string list * string list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 8 in
  let sort_lines = ref [] in
  let add_sort (b : base_typ) =
    if (not (Smtlib.is_builtin_sort b)) && b <> B_unit then begin
      let s = Smtlib.sort_of_base b in
      if not (Hashtbl.mem seen s) then begin
        Hashtbl.add seen s ();
        sort_lines := Printf.sprintf "(declare-sort %s 0)" s :: !sort_lines
      end
    end
  in
  let const_lines =
    List.map
      (fun (v, b) -> add_sort b;
        Printf.sprintf "(declare-const %s %s)" (Smtlib.smt_var v) (Smtlib.sort_of_base b))
      scope
  in
  (List.rev !sort_lines, const_lines)

(* ===== z3 invocation ===== *)

let z3_bin () = try Sys.getenv "CAMLSTAR_Z3" with Not_found -> "z3"

let read_file (path : string) : string =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let run_z3 (query : string) : verdict =
  let qf = Filename.temp_file "camlstar" ".smt2" in
  let out = Filename.temp_file "camlstar" ".out" in
  let oc = open_out qf in output_string oc query; close_out oc;
  let cmd = Printf.sprintf "%s -smt2 %s > %s 2>&1" (z3_bin ()) (Filename.quote qf) (Filename.quote out) in
  let _ = Sys.command cmd in
  let output = read_file out in
  (try Sys.remove qf with _ -> ());
  (try Sys.remove out with _ -> ());
  let lines = String.split_on_char '\n' output in
  let verdict = List.fold_left
      (fun acc line ->
        match acc, String.trim line with
        | None, "unsat" -> Some Verified
        | None, "sat" -> Some Failed
        | None, "unknown" -> Some Unknown
        | _ -> acc)
      None lines
  in
  match verdict with Some v -> v | None -> Solver_error (String.trim output)

(* ===== query assembly ===== *)

let dedup (lines : string list) : string list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 32 in
  List.filter (fun l -> if Hashtbl.mem seen l then false else (Hashtbl.add seen l (); true)) lines

let build_query (m : modul) (ret_sort : string -> base_typ) (vc : Vc.t) : string =
  let vc = Skolem.skolemize vc in                    (* hoist ∃-hyps to scope consts *)
  let anf_f = Anf.normalize (vc_formula vc) in
  let f = Relabs.transform ret_sort (Nnf.normalize anf_f) in     (* the negated VC *)
  let mat = materialization ret_sort anf_f in                    (* auto-instantiation *)
  let sort_decls, const_decls = scope_decls vc.Vc.scope in
  let final_axioms = global_final_axioms m in
  let raw_axioms = List.map (full_transform ret_sort) (global_raw_axioms m @ vc.Vc.axioms) in
  let buf = Buffer.create 1024 in
  let line s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  let assert_ a = line (Printf.sprintf "(assert %s)" (Smtlib.term_to_sexpr a)) in
  line "(set-logic ALL)";
  line "(declare-sort Unit 0)";
  line "(declare-const unit_val Unit)";
  List.iter line (dedup (global_sort_decls m @ sort_decls));   (* sorts once *)
  List.iter line (dedup (global_rel_decls m));
  List.iter line const_decls;
  List.iter assert_ final_axioms;
  List.iter assert_ raw_axioms;
  (match mat with Some a -> assert_ a | None -> ());
  assert_ f;
  line "(check-sat)";
  Buffer.contents buf

let sanitize_file (s : string) : string =
  String.map (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_')
    s

let solve_module ?dump_dir (m : modul) (vcs : Vc.t list) : (Vc.t * verdict) list =
  let ret_sort = make_ret_sort m in
  List.mapi
    (fun i vc ->
      let query = build_query m ret_sort vc in
      (match dump_dir with
       | Some dir ->
         let fn = Printf.sprintf "%s/%s_%d.smt2" dir (sanitize_file vc.Vc.reason) (i + 1) in
         let oc = open_out fn in output_string oc query; close_out oc
       | None -> ());
      (vc, run_z3 query))
    vcs
