(* ast.mli — core AST for Caml*, a simplified, stratified, dependently-typed
   clone of F*.

   Design (see plan): types and terms are strictly stratified. Terms are never
   parametric over types (no first-class types, hence no universes); types may be
   parametric over other types and may be refined by first-order propositions over
   well-typed terms.

       T ::= { v:B | phi }            (refined base type)
           | x:T -> T                 (dependent function type)
       B ::= int | bool | float | ... | T .. T TyCon_i
       phi ::= FOL formula over quantifiers + well-typed terms

   Binders are *named* (name + unique id); substitution (later) freshens to avoid
   capture. Inference/unification variables are NOT represented here — they live in
   a later typechecker module. All substitution is eager (no delayed substitutions). *)

(* ===== Identifiers ===== *)
type var   = { vname : string; vid : int }          (* term variable: name + unique id *)
type tyvar = { tvname : string; tvid : int }         (* type variable 'a *)
type lid   = { ns : string list; bname : string }    (* qualified top-level name / ctor / tycon *)

val fresh_var   : string -> var
val fresh_tyvar : string -> tyvar
val lid_of_str  : string -> lid
val lid_of_path : string list -> string -> lid
val var_eq   : var -> var -> bool
val tyvar_eq : tyvar -> tyvar -> bool
val lid_eq   : lid -> lid -> bool

(* ===== Constants ===== *)
type constant =
  | C_unit
  | C_bool   of bool
  | C_int    of int
  | C_float  of float
  | C_string of string

type quantifier = Forall | Exists

(* ===== Core mutually-recursive syntax ===== *)
type base_typ =
  | B_int | B_bool | B_float | B_unit | B_string
  | B_var of tyvar                (* 'a  — rigid, HM-generalized *)
  | B_app of lid * typ list       (* T1 .. Ti  TyCon_i ; arguments are full types *)

and typ =
  | T_refine of refinement        (* { v : B | phi } *)
  | T_arrow  of arrow             (* x:T1 -> T2  (dependent) *)

and refinement = { rv : var; rbase : base_typ; rphi : term }  (* rv bound in rphi *)
and arrow      = { abinder : var; adom : typ; acod : typ }    (* abinder bound in acod *)

and term =
  | Tm_var      of var
  | Tm_fvar     of lid                 (* top-level symbol or data constructor *)
  | Tm_const    of constant
  | Tm_abs      of abs                 (* fun (x:T) -> e *)
  | Tm_app      of term * term
  | Tm_let      of letbindings * term  (* let [rec] .. in .. *)
  | Tm_match    of term * branch list
  | Tm_ascribed of term * typ          (* (e <: T) *)
  | Tm_quant    of quant               (* forall/exists (x:T). phi *)

and abs   = { xbinder : var; xtyp : typ option; xbody : term }
                                                (* xtyp = None when the binder's type is left to inference *)
and quant = { qk : quantifier; qv : var; qty : typ option; qbody : term }
                                                (* qty = None when the bound variable's type is left to inference *)

and letbindings = { lb_rec : bool; lbs : letbinding list }   (* rec + mutual `and` group *)
and letbinding  = { lb_name : var; lb_scheme : tscheme option; lb_def : term;
                    lb_measure : decreases option }          (* lb_scheme = None when unannotated; measure only for rec *)
and decreases = Dec_lex of term list | Dec_wf of term * term

and branch = { br_pat : pat; br_when : term option; br_body : term }
and pat = P_const of constant | P_var of var | P_wild of var | P_cons of lid * pat list

and tscheme = { ts_vars : tyvar list; ts_typ : typ }         (* prenex HM scheme forall 'a... . T *)

(* ===== Top level ===== *)
type range = { file : string; rstart : int * int; rend : int * int }
val dummy_range : range

type data_con  = { dc_name : lid; dc_typ : tscheme }   (* ctor type is an arrow returning B_app(ind, params) *)
type inductive = { ind_name : lid; ind_params : tyvar list; ind_ctors : data_con list }

type qualifier = Q_assumption | Q_private | Q_irreducible | Q_unfold | Q_noeq | Q_logic

type pragma =
  | P_check of term | P_eval of term
  | P_set_options of string | P_push_options of string option | P_pop_options

type sigelt' =
  | Sig_inductive of inductive
  | Sig_let       of letbindings
  | Sig_val       of lid * tscheme            (* val f : sch  (assumed when Q_assumption) *)
  | Sig_assume    of lid * term               (* named logical axiom: assume P *)
  | Sig_pragma    of pragma
  | Sig_fail      of sigelt list * int list   (* expect_failure { ses } with expected codes *)

and sigelt = { sig_el : sigelt'; sig_quals : qualifier list;
               sig_attrs : term list; sig_rng : range }

type modul = { mod_name : lid; mod_decls : sigelt list; mod_is_iface : bool }

(* ===== Well-known symbols (logic + arithmetic), represented as Tm_fvar ===== *)
val and_lid : lid
val or_lid : lid
val imp_lid : lid
val iff_lid : lid
val not_lid : lid
val eq_lid : lid
val assert_lid : lid
val assume_lid : lid
val instantiate_lid : lid

(* ===== Smart constructors ===== *)
val mono    : typ -> tscheme
val mk_base : base_typ -> typ          (* {v:B | true} with fresh v *)
val t_int : typ
val t_bool : typ
val t_unit : typ
val t_float : typ
val t_string : typ
val mk_true : term
val mk_false : term
val mk_app    : term -> term list -> term
val mk_and : term -> term -> term
val mk_or  : term -> term -> term
val mk_imp : term -> term -> term
val mk_not : term -> term
val mk_eq  : term -> term -> term
val mk_forall : var -> typ option -> term -> term
val mk_exists : var -> typ option -> term -> term
val mk_arrow  : var -> typ -> typ -> typ
val mk_squash : term -> typ            (* squash phi := {_:unit | phi} *)

(* ===== Debug printing (resugars {v:B|true} -> B, {_:unit|phi} -> squash phi) ===== *)
val string_of_typ    : typ -> string
val string_of_term   : term -> string
val string_of_sigelt : sigelt -> string
