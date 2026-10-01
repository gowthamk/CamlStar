(* smt.ml — see smt.mli. *)

open Ast

type verdict =
  | Verified
  | Saturated of Cex.t          (* sat, and instantiation is exhausted: needs a lemma *)
  | Fuel_exhausted of Cex.t     (* sat, and we gave up unrolling: verdict is "unknown" *)
  | Unknown
  | Solver_error of string

(* [Failed cex] = z3 returned sat: a counterexample to the (negated) VC, reconstructed
   into a source-level [Cex.t]. Under relational abstraction the relations
   *over*approximate the functions (no totality is asserted, to stay in EPR), so such
   a counterexample may be spurious rather than a genuine refutation. *)
let string_of_verdict = function
  | Verified -> "verified"
  | Saturated _ -> "failed (saturated)"
  | Fuel_exhausted _ -> "failed (fuel exhausted)"
  | Unknown -> "unknown"
  | Solver_error s -> "solver error: " ^ s

(* ===== the transform pipeline =====
   ANF -> NNF -> relabs, exactly as Raven normalises goals and definitional axioms.
   The relabs binder sorts come from the module's function/constructor return sorts. *)
let make_ret_sort (m : modul) : string -> base_typ =
  let tbl = Axioms.ret_sort_table m in
  fun name -> match Hashtbl.find_opt tbl name with Some b -> b | None -> B_app (lid_of_str name, [])

(* full positive pipeline, for globally-true formulas (definitional equations, assumes) *)
let is_pred (ret_sort : string -> base_typ) (n : string) : bool = ret_sort n = B_bool

let full_transform (ret_sort : string -> base_typ) (t : term) : term =
  Relabs.transform ret_sort (Nnf.normalize (Anf.normalize (is_pred ret_sort) t))

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

let materialize_binds (ret_sort : string -> base_typ) (binds : (var * term) list) : term option =
  match binds with
  | [] -> None
  | _ ->
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
let scope_decls (naming : Smtlib.naming) (scope : (var * base_typ) list) : string list * string list =
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
        Printf.sprintf "(declare-const %s %s)" (Smtlib.smt_var naming v) (Smtlib.sort_of_base b))
      scope
  in
  (List.rev !sort_lines, const_lines)

(* ===== z3 invocation (in-process, via the OCaml API) =====
   We keep emitting the query as SMT-LIB2 text (so [--dump-smt] and the whole
   ANF/NNF/relabs pipeline are unchanged) and simply hand that text to Z3 in-process
   with [parse_smtlib2_string], rather than shelling out to the [z3] binary. The
   payoff is that on [sat] we get a [Z3.Model.model] back — the structured
   counterexample — instead of scraping text. Z3 must be 4.13.3, matching the
   [z3.4.13.3] opam bindings and the solver F* itself uses. *)

(* internal: the solver's raw answer, carrying the model on sat (reconstruction into
   the public [verdict] happens in [solve_module], where the module/vc/naming are in
   scope) *)
type raw = R_verified | R_sat of Z3.context * Z3.Model.model | R_unknown | R_error of string

let run_z3 ?(timeout_ms = 10000) (query : string) : raw =
  (* A fresh context per VC: each query redeclares its own sorts/relations/consts, so
     an isolated context avoids cross-VC symbol clashes. The returned [model] keeps
     its context alive (the OCaml bindings hold the reference), so it is safe to use
     it after this returns.

     [timeout] matters because the EPR argument only bounds queries whose sorts are
     uninterpreted: a definitional axiom with no constructor pattern on its argument
     triggers on every term of its sort, so instantiating more terms can make a single
     query blow up in E-matching. Without a timeout the tool would simply hang; with one,
     such a query reports [unknown] and we move on. *)
  let ctx = Z3.mk_context [ ("model", "true"); ("timeout", string_of_int timeout_ms) ] in
  try
    (* [parse_smtlib2_string] processes the declarations and returns the assertions
       as an AST vector; it does not execute [(check-sat)] — we drive that ourselves.
       All symbols are declared inline in [query], so the four decl/sort arrays are
       empty. *)
    let asts = Z3.SMT.parse_smtlib2_string ctx query [] [] [] [] in
    let exprs = Z3.AST.ASTVector.to_expr_list asts in
    let solver = Z3.Solver.mk_solver ctx None in
    Z3.Solver.add solver exprs;
    match Z3.Solver.check solver [] with
    | Z3.Solver.UNSATISFIABLE -> R_verified
    | Z3.Solver.SATISFIABLE ->
      (match Z3.Solver.get_model solver with
       | Some m -> R_sat (ctx, m)
       | None -> R_error "solver returned sat but produced no model")
    | Z3.Solver.UNKNOWN -> R_unknown
  with Z3.Error msg -> R_error msg

(* ===== query assembly ===== *)

let dedup (lines : string list) : string list =
  let seen : (string, unit) Hashtbl.t = Hashtbl.create 32 in
  List.filter (fun l -> if Hashtbl.mem seen l then false else (Hashtbl.add seen l (); true)) lines

let build_query (m : modul) (ret_sort : string -> base_typ) (vc : Vc.t) : string * Smtlib.naming =
  let ledger = Smtlib.ledger_terms vc in             (* from source terms, pre-skolem *)
  let vc = Skolem.skolemize vc in                    (* hoist ∃-hyps to scope consts *)
  let naming = Smtlib.make_naming (List.map fst vc.Vc.scope) in  (* readable model names *)
  let anf_f = Anf.normalize (is_pred ret_sort) (vc_formula vc) in
  let f = Relabs.transform ret_sort (Nnf.normalize anf_f) in     (* the negated VC *)
  (* materialise both the VC's ground applied subterms and each instantiate! hint *)
  let hint_binds = List.concat_map (Anf.hoist (is_pred ret_sort)) vc.Vc.instantiations in
  let mat = materialize_binds ret_sort (ground_lets anf_f @ hint_binds) in
  let sort_decls, const_decls = scope_decls naming vc.Vc.scope in
  let final_axioms = global_final_axioms m in
  let raw_axioms = List.map (full_transform ret_sort) (global_raw_axioms m @ vc.Vc.axioms) in
  let buf = Buffer.create 1024 in
  let line s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  let assert_ a = line (Printf.sprintf "(assert %s)" (Smtlib.term_to_sexpr naming a)) in
  (* Ledger: the applied subterms this query already materialises as witnesses. Mirrors
     the list printed after a counterexample, so a dumped .smt2 records the dedup /
     saturation check for instantiate! hints. *)
  line "; instantiated terms:";
  (match ledger with
   | [] -> line ";   (none)"
   | ts -> List.iter (fun t -> line (Printf.sprintf ";   %s" (Ast.string_of_term t))) ts);
  line "(set-logic ALL)";
  line "(declare-sort Unit 0)";
  line "(declare-const unit_val Unit)";
  line ";; Sorts";
  List.iter line (dedup (global_sort_decls m @ sort_decls));   (* sorts once *)
  line ";; Relations";
  List.iter line (dedup (global_rel_decls m));
  line ";; Constants";
  List.iter line const_decls;
  line ";; Axioms -- Functionality and Injectivity";
  List.iter assert_ final_axioms;
  line ";; Axioms -- Definitional";
  List.iter assert_ raw_axioms;
  (match mat with Some a -> assert_ a | None -> ());
  line ";; Negated goal";
  assert_ f;
  line "(check-sat)";
  (Buffer.contents buf, naming)

let sanitize_file (s : string) : string =
  String.map (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_')
    s

(* how many queries the last [solve_module] sent to z3 (CEGQI sends one per round) *)
let calls = ref 0
let solver_calls () = !calls

(* ===== the CEGQI loop =====
   Solve; on sat, unfold the VC's applications one step and materialise whatever witnesses
   are missing (Cegqi.candidates), then solve again. Stops when the VC is discharged, when
   a round finds no new candidate (SATURATED — what remains needs a lemma, not a witness),
   or when [fuel] rounds have passed. Each round deepens the unfolding by one level, so
   [fuel] is simultaneously the depth and round bound: it is what stops an unbounded
   S(a), S(S(a)), ... tower from a non-structurally-recursive definition, which cannot be
   detected in general. *)
let solve_module ?dump_dir ?(cegqi = true) ?(fuel = 3) ?(trace = false)
    ?(timeout_ms = 10000) (m : modul) (vcs : Vc.t list) : (Vc.t * verdict) list =
  let ret_sort = make_ret_sort m in
  calls := 0;
  List.mapi
    (fun i vc0 ->
      let dump round query =
        match dump_dir with
        | Some dir ->
          let base = Printf.sprintf "%s/%s_%d" dir (sanitize_file vc0.Vc.reason) (i + 1) in
          let fn = if round = 0 then base ^ ".smt2"
                   else Printf.sprintf "%s_r%d.smt2" base round in
          let oc = open_out fn in output_string oc query; close_out oc
        | None -> ()
      in
      let rec go round vc =
        let query, naming = build_query m ret_sort vc in
        dump round query;
        incr calls;
        match run_z3 ~timeout_ms query with
        | R_verified -> (vc, Verified)
        | R_unknown -> (vc, Unknown)
        | R_error s -> (vc, Solver_error s)
        | R_sat (ctx, model) ->
          let cex = Cex.of_model m vc naming ctx model in
          if not cegqi then (vc, Saturated cex)
          else if round >= fuel then (vc, Fuel_exhausted cex)
          else
            let cands = Cegqi.candidates m vc in
            if cands = [] then (vc, Saturated cex)
            else begin
              if trace then begin
                Printf.printf "  · cegqi round %d of %s: +%d instantiation(s)\n"
                  (round + 1) vc0.Vc.reason (List.length cands);
                List.iter
                  (fun t ->
                    let d = match Cegqi.eval_in_cex cex t with
                      | None -> "undefined in model" | Some _ -> "defined in model" in
                    Printf.printf "      %s   (%s)\n" (Ast.string_of_term t) d)
                  cands;
                (* a progress trace is only useful if it appears as it happens *)
                flush stdout
              end;
              go (round + 1) { vc with Vc.instantiations = vc.Vc.instantiations @ cands }
            end
      in
      go 0 vc0)
    vcs
