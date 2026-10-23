(* exhaust.ml — see exhaust.mli *)
open Ast

let expand (ctors : (lid * int) list) (scrut : term) (branches : branch list) : branch list =
  if ctors = [] then branches
  else
    let rec go covered = function
      | [] -> []
      | ({ br_pat = P_cons (l, _); _ } as br) :: rest -> br :: go (l :: covered) rest
      | ({ br_pat = P_const _; _ } as br) :: rest -> br :: go covered rest
      | { br_pat = (P_wild _ | P_var _) as p; br_when; br_body } :: _ ->
        let body = match p with
          | P_var v -> Subst.subst_term [ (v, scrut) ] br_body
          | _ -> br_body
        in
        List.filter_map
          (fun (l, arity) ->
            if List.exists (lid_eq l) covered then None
            else
              let fields = List.init arity (fun _ -> fresh_var "m") in
              Some { br_pat = P_cons (l, List.map (fun v -> P_var v) fields);
                     br_when; br_body = body })
          ctors
    in
    go [] branches
