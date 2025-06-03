(* An OCaml implementation of higher-rank syntax with de Bruijn indices. *)

type index = int

type shape = Shape of arity list

and arity = Arity of arity list

type expr = Apply of index * expr list

let rec print_expr (Apply (k, ts)) ppf =
  match ts with
  | [] -> Format.fprintf ppf "%d" k
  | _ -> Format.fprintf ppf "%d (%t)" k (print_args ts)

and print_args ts ppf =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
    (fun ppf t -> print_expr t ppf) ppf ts

let rec print_shape (Shape ars) ppf =
  Format.fprintf ppf "[%t]" (print_arities ars)

and print_arities ars ppf =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
    (fun ppf t -> print_arity t ppf) ppf ars

and print_arity (Arity ars) ppf =
  Format.fprintf ppf "{%t}" (print_arities ars)

exception Error of string

let error msg = raise (Error msg)

let (++) (Shape gamma) (Shape delta) = Shape (gamma @ delta)

let (+*) (Shape gamma) (Arity ar) = Shape (gamma @ ar)

let width (Shape gamma) = List.length gamma

let to_shape (Arity ar) = Shape ar

let get i (Shape lst) =
  try
    List.nth lst (List.length lst - i - 1)
  with
  | Invalid_argument _ -> error "Invalid de Bruijn index"

(* Raise an error if the given expression is not valid
   for the given shape. *)
let rec validate gamma (Apply (x, ts)) =
  let Arity ar = get x gamma in
  if List.length ar <> List.length ts then
    begin
      Format.printf "validate fail:@\n @[<h>%t ⊢ %t@]@\n"
        (print_shape gamma)
        (print_expr (Apply (x, ts))) ;
      error ("Wrong number of arguments")
  end
  else
    List.iter2 (fun a e -> validate (gamma +* a) e) ar ts

(* (\* [shift gamma delta theta e] takes an expression [e] in shape [gamma ++ theta] and *)
(*    converts it to a valid expression in [gamma ++ delta ++ delta]. *)

(*    This is probably not correct. The idea is that this will be used as *)
(*    necessary to insert e into a wider context. *)
(* *\) *)
(* let rec shift gamma delta theta (Apply (x, ts)) : expr = *)
(*   let y = if x < width theta then x else x + width delta in *)
(*   let Arity ar = get x gamma in *)
(*   let ts = List.map2 *)
(*       (fun eta t -> shift gamma delta (theta +* eta) t) *)
(*       ar ts *)
(*   in *)
(*   Apply (y, ts) *)

(* [shift_var x alpha gamma delta] takes a variable [x] valid in [alpha ++ gamma],
   where [x] comes from [alpha] part, and places it in [alpha ++ delta]. *)
let shift_var x alpha gamma delta =
  assert (x >= width gamma) ;
  let d = width delta - width gamma in
  x + d

type substitution = {
  pre : shape ; (* the common prefix of dom and cod *)
  dom : shape ;
  cod : shape ;
  sub : expr list (* for each x of arity ar in dom, an expression in pre ++ cod +* ar *)
}

(* Access the x-th item in substitution f, but take into account the fact
   that x got shifted by the bound variables in gamma. *)
let get_subst f x gamma =
  try
    List.nth f.sub (List.length f.sub - 1 - x + width gamma)
  with
  | Invalid_argument _ ->
    Format.printf "get_subst problem: f.sub=%d, x=%d, gamma=%t"
      (List.length f.sub) x (print_shape gamma) ;
    error "get_subst problem"

(* [subst f gamma e] takes an expression [e] valid in [f.pre ++ f.dom ++ gamma]
   and applies [f] to it to obtain an expression in [f.pre + f.cod ++ gamma] *)
let rec subst f gamma (Apply (x, ts)) : expr =
  validate (f.pre ++ f.dom ++ gamma) (Apply (x, ts)) ;
  let (Arity ar_lst) as ar = get x (f.pre ++ f.dom ++ gamma) in
  if x < width gamma then
    (* x is in gamma *)
    let ts' = List.map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_lst ts
    in
    Apply (x, ts')
  else if x < width f.dom + width gamma then
   (* x is in f.dom *)
    let e' = get_subst f x gamma in
    (* do we need to shift e' by width gamma here? *)
    validate (f.pre ++ f.cod +* ar) e' ;
    let g = { pre = f.pre ++ f.cod ;
              dom = to_shape ar ;
              cod = gamma ;
              sub =
                List.map2
                  (fun a t ->
                     validate (f.pre ++ f.dom ++ gamma +* a) t ;
                     let t' = subst f (gamma +* a) t in
                     validate (f.pre ++ f.cod ++ gamma +* a) t' ;
                     t'
                  )
                  ar_lst ts
            } in
    let e'' = subst g (Shape []) e' in
    validate (f.pre ++ f.cod ++ gamma) e'' ;
    e''
  else
    (* x is in f.pre *)
    let y = shift_var x f.pre (f.dom ++ gamma) (f.cod ++ gamma) in
    let ts' = List.map2
       (fun a t ->
          validate (f.pre ++ f.dom ++ gamma +* a) t ;
          subst f (gamma +* a) t)
       ar_lst ts
    in
    Apply (y, ts')

let var = Arity []

let bind1_var = Arity [Arity []]

let sym x = Apply (x, [])

let app1 x e = Apply (x, [e])

let app2 x e1 e2 = Apply (x, [e1; e2])

module ExampleExpr =
struct
  let _ = Format.printf "============ ExampleExpr:@\n"

  let gamma =
    Shape [
      (Arity []) ; (* ℕ = 7 *)
      (Arity [var]) ; (* Vec = 6 *)
      (Arity []) ; (* zero = 5*)
      (Arity [var]) ; (* succ = 4 *)
      (Arity [var; var]) ; (* plus = 3*)
      (Arity [bind1_var]) ; (* untyped lambda = 2 *)
      (Arity [var; bind1_var]) ; (* ∏ = 1 *)
      (Arity []) (* x = 0 *)
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
  let dom = Shape [Arity []] (* x *)
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
