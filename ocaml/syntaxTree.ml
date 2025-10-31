(* An OCaml implementation of higher-rank syntax with de Bruijn indices. *)

(* We use binary trees to represent shapes and arities. It might be smarter to use lists. *)
type 'a tree =
  | Empty
  | Slot of 'a
  | Oplus of 'a tree * 'a tree

(* A position pointing to a leaf in a binary tree. *)
type index =
  | Here
  | Left of index
  | Right of index

type arity = Arity of arity tree

type shape = Shape of arity tree

(* An expression is an index applied to an expression tree.
   As OCaml does not have dependent types, this is the best we can.
   We will have to manually verify validity of expressions. *)
type expr = Apply of index * expr tree

(* See examples at the end of the file. *)

exception Error of string

(* Report an error *)
let error msg = raise (Error msg)

(* Convert a list to a right-leaning tree (which can be either a shape or an arity).
   This is a convenience function that eases writing down examples. *)
let rec from_list = function
  | [] -> Empty
  | [x] -> Slot x
  | x :: xs -> Oplus (Slot x, from_list xs)

(* Convert a pair to a shape, also convenience. Note that from_pair (x,y) is not
   the same as from_list [x;y]. *)
let from_pair (x, y) = Oplus (Slot x, Slot y)

(* Lookup an item in the tree by its index *)
let rec lookup idx ts =
  match idx, ts with
  | Here, Slot t -> t
  | Left idx, Oplus (ts, _) -> lookup idx ts
  | Right idx, Oplus (_, ts) -> lookup idx ts
  | _, _ -> error "Invalid tree index"

(* Do the given trees have the same shape? *)
let rec equal_shape t1 t2 =
  match t1, t2 with
  | Empty, Empty -> true
  | Slot _, Slot _ -> true
  | Oplus (t11, t12), Oplus (t21, t22) ->
    equal_shape t11 t21 && equal_shape t12 t22
  | _, _ -> false

(* Iterate a binary function f on two trees of the same shape. *)
let rec tree_iter2 f t1 t2 =
  match t1, t2 with
  | Empty, Empty -> ()
  | Slot x, Slot y -> f x y
  | Oplus (t11, t12), Oplus (t21, t22) ->
    tree_iter2 f t11 t21 ; tree_iter2 f t12 t22
  | _, _ -> error "Mismatching shapes in tree_iter2"

(* Map a binary function f on two trees of the same shape. *)
let rec tree_map2 f t1 t2 =
  match t1, t2 with
  | Empty, Empty -> Empty
  | Slot x, Slot y -> Slot (f x y)
  | Oplus (t11, t12), Oplus (t21, t22) ->
    Oplus (tree_map2 f t11 t21, tree_map2 f t12 t22)
  | _, _ -> error "Mismatching shapes in tree_map2"

(* Print an index as a sequence of h, l, r *)
let rec print_index idx ppf =
  match idx with
  | Here -> Format.fprintf ppf "h"
  | Left idx -> Format.fprintf ppf "l%t" (print_index idx)
  | Right idx -> Format.fprintf ppf "r%t" (print_index idx)

(* Print a tree *)
let rec print_tree print_slot ts ppf =
  match ts with
  | Empty -> Format.fprintf ppf ""
  | Slot e -> Format.fprintf ppf "%t" (print_slot e)
  | Oplus (ts1, ts2) ->
    Format.fprintf ppf "(%t ⊕ %t)" (print_tree print_slot ts1) (print_tree print_slot ts2)

(* Print an expression *)
let rec print_expr (Apply (k, ts)) ppf =
  match ts with
  | Empty -> Format.fprintf ppf "%t" (print_index k)
  | _ -> Format.fprintf ppf "%t (%t)" (print_index k) (print_tree print_expr ts)

(* Print a shape *)
let rec print_shape (Shape ars) ppf =
  Format.fprintf ppf "[%t]" (print_arities ars)

(* Print a tree of arities *)
and print_arities ars = print_tree print_arity ars

(* Print an arity *)
and print_arity (Arity ars) ppf =
  Format.fprintf ppf "{%t}" (print_arities ars)

(* Concatenate shapes *)
let (++) (Shape gamma) (Shape delta) = Shape (Oplus (gamma, delta))

(* Concatenate a shape and an arity *)
let (+*) (Shape gamma) (Arity ar) = Shape (Oplus (gamma, ar))

(* Convert an arity to a shape *)
let to_shape (Arity ar) = Shape ar

(* Lookup the arity of an index in a shape *)
let get idx (Shape ts) = lookup idx ts

(* Shape-check an expressions with respect to the given shape gamma. *)
let rec validate gamma (Apply (x, ts)) =
  let Arity ar = get x gamma in
  if not (equal_shape ar ts) then
    begin
      Format.printf "debug: validate fail in@\n @[<h>%t ⊢ %t@]@\n"
        (print_shape gamma)
        (print_expr (Apply (x, ts))) ;
      error ("invalid expressions (wrong number of arguments)")
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

(* A substitution sub : pre ++ dom → pre ++ cod.
   It acts trivially on pre and maps variables in dom to expressions in pre ++ cod. *)
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
  (* sanity check: validate the input *)
  validate (f.pre ++ f.dom ++ gamma) (Apply (x, ts)) ;
  (* let ar be the arity of x, and ar_tree its underlying tree *)
  let (Arity ar_tree) as ar = get x (f.pre ++ f.dom ++ gamma) in
  match x with

  | Right y -> (* x is in gamma *)
    (* apply the substution to the arguments ts *)
    let ts' = tree_map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_tree ts
    in
    Apply (x, ts')

  | Left (Right y) -> (* x is in f.dom *)

    (* do we need to shift e' by width gamma here? *)
    let e' = get_subst f x gamma in

    (* sanity check: validate output of recursive call *)
    validate (f.pre ++ f.cod +* ar) e' ;

    (* build an auxiliary substution that we will apply to e' *)
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
                  ar_tree ts
            } in

    let e'' = subst g (Shape Empty) e' in

    validate (f.pre ++ f.cod ++ gamma) e'' ;
    e''

  | Left (Left y) -> (* x is in f.pre *)

    (* We just re-index x to the output shape *)
    let y = shift_var x f.pre (f.dom ++ gamma) (f.cod ++ gamma) in

    (* Apply the substutition to the arguments *)
    let ts' = tree_map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_tree ts
    in
    Apply (y, ts')

  (* The remaining cases are not possible since by convention we must act on a
     an expression valid in the shape (f.pre ++ f.dom) ++ gamma. *)
  | Here ->
     error "subst: impossible, x is here"

  | Left Here ->
     error "subst: impossible, x is left here"

(* We now build some examples. *)

(* the arity of an ordinary variable *)
let var = Arity Empty

(* the arity of an operation that binds one variable, such as λ x. ⋯ *)
let bind1_var = Arity (Slot (Arity Empty))

(* convert an index of an ordinary variable into an expression *)
let sym x = Apply (x, Empty)

(* apply a unary variable x *)
let app1 x e = Apply (x, Slot e)

(* apply a binary vaiable x *)
let app2 x e1 e2 = Apply (x, from_pair (e1, e2))

module ExampleExpr =
struct
  let _ = Format.printf "============ ExampleExpr:@\n"

  (* We set up a shape that has a good supply of symbols.
     The comments give an example from real life and the de Bruijn index *)
  let gamma =
    Shape (from_list [
      (Arity Empty) ; (* ℕ = 7 *)
      (Arity (Slot var)) ; (* Vec = 6 *)
      (Arity Empty) ; (* zero = 5*)
      (Arity (Slot var)) ; (* succ = 4 *)
      (Arity (from_pair (var, var))) ; (* plus = 3*)
      (Arity (Slot bind1_var)) ; (* untyped lambda = 2 *)
      (Arity (from_pair (var, bind1_var))) ; (* ∏ = 1 *)
      (Arity Empty) (* x = 0 *)
    ])

  (* The examples have not been fixed below here because the indices are
     still integers, but they're supposed to be tree indices. *)

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
