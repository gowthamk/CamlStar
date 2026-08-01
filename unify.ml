(* unify.ml — see unify.mli. *)

type ityp =
  | I_int | I_bool | I_float | I_unit | I_string
  | I_var   of Ast.tyvar
  | I_app   of Ast.lid * ityp list
  | I_arrow of ityp * ityp
  | I_meta  of meta
and meta = { mid : int; mutable sol : ityp option; mutable numeric : bool }

exception Unify_error of ityp * ityp

let counter = ref 0
let fresh id_numeric =
  incr counter;
  I_meta { mid = !counter; sol = None; numeric = id_numeric }
let fresh_meta () = fresh false
let fresh_numeric_meta () = fresh true

(* Follow the solution chain to the head, compressing along the way. *)
let rec repr (t : ityp) : ityp =
  match t with
  | I_meta ({ sol = Some t'; _ } as m) ->
    let r = repr t' in
    m.sol <- Some r;
    r
  | _ -> t

let rec occurs (m : meta) (t : ityp) : bool =
  match repr t with
  | I_meta m' -> m'.mid = m.mid
  | I_arrow (a, b) -> occurs m a || occurs m b
  | I_app (_, args) -> List.exists (occurs m) args
  | I_int | I_bool | I_float | I_unit | I_string | I_var _ -> false

let rec unify (t1 : ityp) (t2 : ityp) : unit =
  let a = repr t1 and b = repr t2 in
  match a, b with
  | I_int, I_int | I_bool, I_bool | I_float, I_float
  | I_unit, I_unit | I_string, I_string -> ()
  | I_var x, I_var y when Ast.tyvar_eq x y -> ()
  | I_arrow (a1, b1), I_arrow (a2, b2) -> unify a1 a2; unify b1 b2
  | I_app (l1, xs), I_app (l2, ys)
    when Ast.lid_eq l1 l2 && List.length xs = List.length ys ->
    List.iter2 unify xs ys
  | I_meta m1, I_meta m2 when m1.mid = m2.mid -> ()
  | I_meta m1, I_meta m2 ->
    (* link m1 → m2; numericness propagates onto the survivor *)
    m2.numeric <- m2.numeric || m1.numeric;
    m1.sol <- Some (I_meta m2)
  | I_meta m, t | t, I_meta m ->
    if occurs m t then raise (Unify_error (a, b));
    if m.numeric then (match t with
      | I_int | I_float -> ()
      | _ -> raise (Unify_error (a, b)));
    m.sol <- Some t
  | _ -> raise (Unify_error (a, b))

let free_metas (t : ityp) : meta list =
  let rec go acc t =
    match repr t with
    | I_meta m -> if List.exists (fun m' -> m'.mid = m.mid) acc then acc else m :: acc
    | I_arrow (x, y) -> go (go acc x) y
    | I_app (_, args) -> List.fold_left go acc args
    | I_int | I_bool | I_float | I_unit | I_string | I_var _ -> acc
  in
  List.rev (go [] t)

let default_numeric (m : meta) : unit =
  if m.sol = None && m.numeric then m.sol <- Some I_int

let rec zonk (t : ityp) : ityp =
  match repr t with
  | I_meta m -> if m.numeric then (m.sol <- Some I_int; I_int) else I_meta m
  | I_arrow (a, b) -> I_arrow (zonk a, zonk b)
  | I_app (l, args) -> I_app (l, List.map zonk args)
  | (I_int | I_bool | I_float | I_unit | I_string | I_var _) as t -> t

let lid_str (l : Ast.lid) = String.concat "." (l.Ast.ns @ [l.Ast.bname])

let rec string_of_ityp (t : ityp) : string =
  match repr t with
  | I_int -> "int" | I_bool -> "bool" | I_float -> "float"
  | I_unit -> "unit" | I_string -> "string"
  | I_var tv -> "'" ^ tv.Ast.tvname
  | I_app (l, []) -> lid_str l
  | I_app (l, args) ->
    lid_str l ^ " " ^ String.concat " " (List.map string_of_ityp args)
  | I_arrow (a, b) ->
    "(" ^ string_of_ityp a ^ " -> " ^ string_of_ityp b ^ ")"
  | I_meta m -> Printf.sprintf "?%d%s" m.mid (if m.numeric then "num" else "")
