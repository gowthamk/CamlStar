(* vc.ml — see vc.mli. Type definitions plus a debug printer; building and solving
   VCs lives in later modules (the checker and the SMT backend). *)

type decl =
  | Dec_sort of Ast.lid
  | Dec_fun  of Ast.lid * Ast.base_typ list * Ast.base_typ

type t = {
  decls  : decl list;
  axioms : Ast.term list;
  scope  : (Ast.var * Ast.base_typ) list;
  hyps   : Ast.term list;
  goal   : Ast.term;
  instantiations : Ast.term list;
  range  : Ast.range;
  reason : string;
}

let lid_str (l : Ast.lid) = String.concat "." (l.Ast.ns @ [ l.Ast.bname ])

(* Render a sort by reusing the Ast type printer (which resugars {v:B|true} ⇒ B). *)
let sort_str (b : Ast.base_typ) = Ast.string_of_typ (Ast.mk_base b)

let string_of_decl = function
  | Dec_sort l -> Printf.sprintf "sort %s" (lid_str l)
  | Dec_fun (l, args, res) ->
    let dom = match args with
      | [] -> "()"
      | _ -> String.concat " * " (List.map sort_str args)
    in
    Printf.sprintf "fun  %s : %s -> %s" (lid_str l) dom (sort_str res)

let string_of_t (v : t) : string =
  let buf = Buffer.create 256 in
  let line s = Buffer.add_string buf s; Buffer.add_char buf '\n' in
  line (Printf.sprintf "(* VC: %s *)" v.reason);
  List.iter (fun d -> line ("  decl  " ^ string_of_decl d)) v.decls;
  List.iter (fun a -> line ("  axiom " ^ Ast.string_of_term a)) v.axioms;
  List.iter
    (fun (x, s) -> line (Printf.sprintf "  var   %s : %s" x.Ast.vname (sort_str s)))
    v.scope;
  List.iter (fun h -> line ("  hyp   " ^ Ast.string_of_term h)) v.hyps;
  List.iter (fun e -> line ("  inst  " ^ Ast.string_of_term e)) v.instantiations;
  line ("  ⊢     " ^ Ast.string_of_term v.goal);
  Buffer.contents buf
