(* cex.mli — reconstruct a succinct counterexample from a Z3 model.

   A [sat] result means the (negated) VC has a model: a counterexample. We turn the
   raw [Z3.Model.model] into a small, JSON-able tree tied back to the source program.

   Three sections, in order:
   - sort universes: for each uninterpreted sort, the finite set of its elements;
   - program-variable assignments: each source scope variable's value;
   - function maps: each user function/constructor relation [f_rel], shown under its
     source name [f] as a map from argument-tuple to result.

   Datatype elements are kept symbolic (the constructors are only partially defined
   in the model, so they cannot in general be written as constructor applications).
   An element is rendered as its 0-ary constructor when it equals one (e.g. [Z]),
   otherwise as a per-sort tag derived from Z3's own name ([UI_nat!val!1] -> [nat!1]).
   Unit-valued relations and the Unit sort are omitted. *)

type value =
  | Scalar  of string                      (* "Z", "nat!1", "3", "true", "-2" *)
  | SetOf   of value list                  (* a sort universe *)
  | Entries of (value list * value) list   (* function: argument-tuple |-> result *)

type t = (string * value) list             (* top level: label |-> value *)

(* Build the counterexample from the model. Needs the module (to identify 0-ary
   constructors and source names), the VC (its [scope] gives the source program
   variables), the [naming] the query used (to find each variable's model constant),
   and the Z3 context (to evaluate relation applications over the finite universe —
   Z3 often returns a relation's interpretation as a formula rather than an entry
   table, so we enumerate and [Model.eval] instead of reading entries). Relations with
   a non-finite (interpreted) or Unit column are omitted from the function maps. *)
val of_model : Ast.modul -> Vc.t -> Smtlib.naming -> Z3.context -> Z3.Model.model -> t

val to_json : t -> string
