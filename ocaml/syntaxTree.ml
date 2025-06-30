(* An OCaml implementation of higher-rank syntax with de Bruijn indices. *)

type 'a tree =
  | Empty
  | Slot of 'a
  | Oplus of 'a tree * 'a tree

type index =
  | Here
  | Left of index
  | Right of index

type shape = Shape of arity tree

and arity = Arity of arity tree

type expr = Apply of index * expr tree

exception Error of string

let error msg = raise (Error msg)

let rec from_list = function
  | [] -> Empty
  | [x] -> Slot x
  | x :: xs -> Oplus (Slot x, from_list xs)

let from_pair (x, y) = Oplus (Slot x, Slot y)

let rec lookup idx ts =
  match idx, ts with
  | Here, Slot t -> t
  | Left idx, Oplus (ts, _) -> lookup idx ts
  | Right idx, Oplus (_, ts) -> lookup idx ts
  | _, _ -> error "Invalid tree index"

let rec equal_shape t1 t2 =
  match t1, t2 with
  | Empty, Empty -> true
  | Slot _, Slot _ -> true
  | Oplus (t11, t12), Oplus (t21, t22) ->
    equal_shape t11 t21 && equal_shape t12 t22
  | _, _ -> false

let rec tree_iter2 f t1 t2 =
  match t1, t2 with
  | Empty, Empty -> ()
  | Slot x, Slot y -> f x y
  | Oplus (t11, t12), Oplus (t21, t22) ->
    tree_iter2 f t11 t21 ; tree_iter2 f t12 t22
  | _, _ -> error "Mismatching shapes in tree_iter2"

let rec tree_map2 f t1 t2 =
  match t1, t2 with
  | Empty, Empty -> Empty
  | Slot x, Slot y -> Slot (f x y)
  | Oplus (t11, t12), Oplus (t21, t22) ->
    Oplus (tree_map2 f t11 t21, tree_map2 f t12 t22)
  | _, _ -> error "Mismatching shapes in tree_map2"

let rec print_index idx ppf =
  match idx with
  | Here -> Format.fprintf ppf "h"
  | Left idx -> Format.fprintf ppf "l%t" (print_index idx)
  | Right idx -> Format.fprintf ppf "r%t" (print_index idx)

let rec print_tree print_slot ts ppf =
  match ts with
  | Empty -> Format.fprintf ppf ""
  | Slot e -> Format.fprintf ppf "%t" (print_slot e)
  | Oplus (ts1, ts2) ->
    Format.fprintf ppf "(%t ⊕ %t)" (print_tree print_slot ts1) (print_tree print_slot ts2)

let rec print_expr (Apply (k, ts)) ppf =
  match ts with
  | Empty -> Format.fprintf ppf "%t" (print_index k)
  | _ -> Format.fprintf ppf "%t (%t)" (print_index k) (print_tree print_expr ts)

let rec print_shape (Shape ars) ppf =
  Format.fprintf ppf "[%t]" (print_arities ars)

and print_arities ars = print_tree print_arity ars

and print_arity (Arity ars) ppf =
  Format.fprintf ppf "{%t}" (print_arities ars)

let (++) (Shape gamma) (Shape delta) = Shape (Oplus (gamma, delta))

let (+*) (Shape gamma) (Arity ar) = Shape (Oplus (gamma, ar))

let to_shape (Arity ar) = Shape ar

let get idx (Shape ts) = lookup idx ts

(* Raise an error if the given expression is not valid for the given shape. *)
let rec validate gamma (Apply (x, ts)) =
  let Arity ar = get x gamma in
  if not (equal_shape ar ts) then
    begin
      Format.printf "validate fail:@\n @[<h>%t ⊢ %t@]@\n"
        (print_shape gamma)
        (print_expr (Apply (x, ts))) ;
      error ("Wrong number of arguments")
  end
  else
    tree_iter2 (fun a e -> validate (gamma +* a) e) ar ts

(* [shift_var x alpha gamma delta] takes a variable [x] valid in [alpha ++ gamma],
   where [x] comes from [alpha] part, and places it in [alpha ++ delta]. *)
let shift_var x alpha gamma delta =
  match x with
  | Left y -> Left y
  | Here | Right _ -> error "shift_var: invalid variable"
    (* If you are getting strange erorrs here, it may be because of the case gamma = Empty *)

type substitution = {
  pre : shape ; (* the common prefix of dom and cod *)
  dom : shape ;
  cod : shape ;
  sub : expr tree (* for each x of arity ar in dom, an expression in (pre ++ cod) +* ar *)
}

(* Access the x-th item in substitution f, but take into account the fact
   that x got shifted by the bound variables in gamma. *)
let get_subst f x gamma =
  match x with
  | Left (Right y) -> lookup y f.sub
  | _ ->
    Format.printf "get_subst problem: f.sub=%t, x=%t, gamma=%t"
      (print_tree print_expr f.sub) (print_index x) (print_shape gamma) ;
    error "get_subst problem"

(* [subst f gamma e] takes an expression [e] valid in [(f.pre ++ f.dom) ++ gamma]
   and applies [f] to it to obtain an expression in [(f.pre ++ f.cod) ++ gamma] *)
let rec subst f gamma (Apply (x, ts)) : expr =
  validate (f.pre ++ f.dom ++ gamma) (Apply (x, ts)) ;
  let (Arity ar_lst) as ar = get x (f.pre ++ f.dom ++ gamma) in
  match x with
  | Right y (* x is in gamma *) ->
    (* x is in gamma *)
    let ts' = tree_map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_lst ts
    in
    Apply (x, ts')
  | Left (Right y) -> (* x is in f.dom *)
    let e' = get_subst f x gamma in
    (* do we need to shift e' by width gamma here? *)
    validate (f.pre ++ f.cod +* ar) e' ;
    let g = { pre = f.pre ++ f.cod ;
              dom = to_shape ar ;
              cod = gamma ;
              sub =
                tree_map2
                  (fun a t ->
                     validate (f.pre ++ f.dom ++ gamma +* a) t ;
                     let t' = subst f (gamma +* a) t in
                     validate (f.pre ++ f.cod ++ gamma +* a) t' ;
                     t'
                  )
                  ar_lst ts
            } in
    let e'' = subst g (Shape Empty) e' in
    validate (f.pre ++ f.cod ++ gamma) e'' ;
    e''
  | Left (Left y) -> (* x is in f.pre *)
    let y = shift_var x f.pre (f.dom ++ gamma) (f.cod ++ gamma) in
    let ts' = tree_map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_lst ts
    in
    Apply (y, ts')

  | Here -> error "subst: x is here"
  | Left Here -> error "subst: x is left here"

let var = Arity Empty

let bind1_var = Arity (Slot (Arity Empty))

let sym x = Apply (x, Empty)

let app1 x e = Apply (x, Slot e)

let app2 x e1 e2 = Apply (x, from_pair (e1, e2))

module ExampleExpr =
struct
  let _ = Format.printf "============ ExampleExpr:@\n"

  let gamma =
    Shape @@ from_list [
      (Arity Empty) ; (* ℕ = 7 *)
      (Arity (Slot var)) ; (* Vec = 6 *)
      (Arity Empty) ; (* zero = 5*)
      (Arity (Slot var)) ; (* succ = 4 *)
      (Arity (from_pair (var, var))) ; (* plus = 3*)
      (Arity (Slot bind1_var)) ; (* untyped lambda = 2 *)
      (Arity (from_pair (var, bind1_var))) ; (* ∏ = 1 *)
      (Arity Empty) (* x = 0 *)
    ]

  (* succ (succ zero) *)
  let e1 = app1 4 (app1 4 (sym 5))
  let _ = Format.printf "@[<h>%t@]@\n" (print_expr e1)
  let _ = validate gamma e1

  (* plus zero x *)
  let e2 = app2 3 (sym 5) (sym 0)
  let _ = Format.printf "@[<h>%t@]@\n" (print_expr e2)
  let _ = validate gamma e2

  (* lambda (y . y) *)
  let e3 = app1 2 (sym 0)
  let _ = Format.printf "@[<h>%t@]@\n" (print_expr e3)
  let _ = validate gamma e3

  (* lambda (y . plus x y) *)
  let e4 = app1 2 (app2 (3 + 1) (sym (0 + 1)) (sym 0))
  let _ = Format.printf "@[<h>%t@]@\n" (print_expr e4)
  let _ = validate gamma e4

  (* ∏ ℕ (n . Vec n) *)
  let e5 = app2 1 (sym 7) (app1 (6+1) (sym 0))
  let _ = Format.printf "@[<h>%t@]@\n" (print_expr e5)
  let _ = validate gamma e5
end

module ExampleSubst1 =
struct
  let _ = Format.printf "============ ExampleSubst1:@\n"

  let pre = Shape [ (Arity [bind1_var]) ] (* untyped lambda *)
  let dom = Shape [Arity Empty] (* x *)
  let cod = Shape [Arity [] ; Arity [] ; Arity []] (* y, z, w *)

  let e = app1 1 (sym (0 + 1))  (* λ, x ⊢ λ _ . x *)
  let _ = validate (pre ++ dom) e
  let _ = Format.printf "Before: @[<h>%t ⊢ %t@]@\n"
      (print_shape (pre ++ dom))
      (print_expr e)

  let f = { pre ; dom ; cod ;
            sub = [sym 2] ; (* λ, y, z, w ⊢ y *)
          }

  let e' = subst f (Shape []) e
  let _ = validate (pre ++ cod) e'
  let _ = Format.printf "After: @[<h>%t ⊢ %t@]@\n"
      (print_shape (pre ++ cod))
      (print_expr e')
end


module ExampleSubst2 =
struct
  let _ = Format.printf "============ ExampleSubst2:@\n"

  let pre = Shape [ (Arity [bind1_var]) ] (* untyped lambda *)
  let dom = Shape [Arity []] (* x *)
  let cod = Shape [Arity [] ; Arity [] ; Arity []] (* y, z, w *)

  let e = app1 1 (app1 (1+1) (sym (0+2)))  (* λ, x ⊢ λ _ . λ _ . x *)
  let _ = validate (pre ++ dom) e
  let _ = Format.printf "Before: @[<h>%t ⊢ %t@]@\n"
      (print_shape (pre ++ dom))
      (print_expr e)

  let f = { pre ; dom ; cod ;
            sub = [sym 2] ; (* λ, y, z, w ⊢ y *)
          }

  let e' = subst f (Shape []) e
  let _ = validate (pre ++ cod) e'
  let _ = Format.printf "After: @[<h>%t ⊢ %t@]@\n"
      (print_shape (pre ++ cod))
      (print_expr e')
end
