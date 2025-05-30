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

exception Error of string

let error msg = raise (Error msg)

let (++) (Shape gamma) (Shape delta) = Shape (gamma @ delta)

let (+*) (Shape gamma) (Arity ar) = Shape (gamma @ ar)

let width (Shape gamma) = List.length gamma

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
    error "Wrong number of arguments"
  else
    List.iter2 (fun a e -> validate (gamma +* a) e) ar ts

let var = Arity []

let bind1_var = Arity [Arity []]

let sym x = Apply (x, [])

let app1 x e = Apply (x, [e])

let app2 x e1 e2 = Apply (x, [e1; e2])

module Example =
struct
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

(* [shift gamma delta theta e] takes an expression [e] in shape [gamma ++ theta] and
   converts it to a valid expression in [gamma ++ delta ++ delta].

   This is probably not correct. The idea is that this will be used as
   necessary to insert e into a wider context.
*)
let rec shift gamma delta theta (Apply (x, ts)) : expr =
  let y = if x < width theta then x else x + width delta in
  let Arity ar = get x gamma in
  let ts = List.map2
      (fun eta t -> shift gamma delta (theta +* eta) t)
      ar ts
  in
  Apply (y, ts)

type substitution = {
  dom : shape ;
  cod : shape ;
  sub : expr list (* for each x of arity ar in dom, an expression in cod +* ar *)
}

(* Access the x-th item in substitution f, but take into account the fact
   that x got shifted by the bound variables in gamma. *)
let get_subst f x gamma =
  List.nth f.sub (List.length f.sub - x - width gamma - 1)

(* [subst alpha f gamma e] takes an expression [e] valid in [alpha ++ f.dom ++ gamma]
   and applies [f] to it to obtain an expression in [alpha + f.cod ++ gamma] *)
let rec subst alpha f gamma (Apply (x, ts)) : expr =
  validate (alpha ++ f.dom ++ gamma) (Apply (x, ts)) ;
  let Arity ar = get x (alpha ++ f.dom ++ gamma) in
  if width gamma < x && x < width f.dom + width gamma then
   (* x is in f.dom *)
    let e = get_subst f x gamma (* in f.cod +* αr *) in
    (* we might have to bring e into correct context using shift,
       construct a substitution from ts, and apply it to e with
       correct focus *)
    failwith "not implemented"
  else
    (* x is in alpha or gamma *)
    let ts' = List.map2 (fun a e -> subst alpha f (gamma +* a) e) ar ts in
    Apply (x, ts')
