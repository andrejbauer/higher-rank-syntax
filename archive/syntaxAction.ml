(* Higher-rank syntax with substitution as a right action of arities on shapes.

   A CARRIER specifies a representation of shapes, arities, and slots, together
   with the action [( ** )] and the slot algebra (entries, lookup, shifts,
   sorts).  Make(C) then defines [expr], [validate], and [subst] uniformly. *)

module type CARRIER = sig
  type shape
  type arity
  type slot

  val ( ** ) : shape -> arity -> shape

  type 'a slot_map = (slot * 'a) list

  val shape_entries : shape -> arity slot_map
  val arity_entries : arity -> arity slot_map

  val shape_lookup : shape -> slot -> arity
  val arity_lookup : arity -> slot -> arity

  val shape_shift : shape -> arity -> slot -> slot
  val arity_shift : shape -> arity -> slot -> slot

  type slot_sort = Left of slot | Right of slot
  val slot_sort : shape -> arity -> slot -> slot_sort

  val empty_arity : arity
end

module Make (C : CARRIER) = struct
  open C

  type expr = Apply of slot * expr slot_map

  exception Invalid of string

  (* (γ *** δ) extends γ by the arities in the list δ.  The head of δ is the
     OUTERMOST extension applied; equivalently, γ *** (α :: δ') = (γ *** δ') ** α.
     This is the cons-as-snoc convention: consing onto δ adds a new outermost
     extension, so the recursive call in [subst] uses [β :: τ] and the equation
     [γ ** β = (γ_base *** τ) ** β = γ_base *** (β :: τ)] holds definitionally. *)
  let rec ( *** ) gamma = function
    | [] -> gamma
    | alpha :: rest -> (gamma *** rest) ** alpha

  let rec validate gamma (Apply (x, args)) =
    let alpha =
      try shape_lookup gamma x
      with _ -> raise (Invalid "head is not a slot of the shape")
    in
    let entries = arity_entries alpha in
    if List.length entries <> List.length args then
      raise (Invalid "wrong number of children")
    else
      List.iter
        (fun (y, beta) ->
          match List.assoc_opt y args with
          | None -> raise (Invalid "missing child for slot")
          | Some child -> validate (gamma ** beta) child)
        entries

  type substitution = {
    pre : shape ;
    dom : arity list ;
    cod : arity list ;
    sub : expr slot_map list ;
  }

  type loc =
    | In_pre of slot
    | In_tau of slot
    | In_dom of expr slot_map * slot

  (* Lift a slot from [base] to [base *** lst] for a cons-convention [lst]
     (head = outermost).  [List.fold_right] visits the innermost extension
     first, which is the order [shape_shift] needs. *)
  let shift_through base lst slot =
    fst (List.fold_right
           (fun alpha (sl, shape) ->
             (shape_shift shape alpha sl, shape ** alpha))
           lst
           (slot, base))

  (* Classify [x] in [(σ.pre *** σ.dom) *** τ], lifting the resulting slot
     through every layer "above" the match site as the recursion unwinds.
     For [In_pre]/[In_tau] the returned slot is already in
     [(σ.pre *** σ.cod) *** τ]; [In_dom] is forwarded unchanged because
     its lifting happens via the auxiliary substitution in [subst]. *)
  let classify sigma tau x =
    let rec walk_dom dom_left sub_left x =
      match dom_left, sub_left with
      | [], [] ->
          In_pre (shift_through sigma.pre sigma.cod x)
      | alpha :: dom_rest, sm :: sub_rest ->
          let inner = sigma.pre *** dom_rest in
          (match slot_sort inner alpha x with
           | Right z -> In_dom (sm, z)
           | Left y -> walk_dom dom_rest sub_rest y)
      | _ -> failwith "classify: σ.dom and σ.sub have different lengths"
    in
    let rec walk_tau tau_left x =
      match tau_left with
      | [] -> walk_dom sigma.dom sigma.sub x
      | beta :: rest ->
          let inner_dom = (sigma.pre *** sigma.dom) *** rest in
          let inner_cod = (sigma.pre *** sigma.cod) *** rest in
          (match slot_sort inner_dom beta x with
           | Right z -> In_tau (arity_shift inner_cod beta z)
           | Left y ->
               (match walk_tau rest y with
                | In_pre s -> In_pre (shape_shift inner_cod beta s)
                | In_tau s -> In_tau (shape_shift inner_cod beta s)
                | In_dom (sm, z) -> In_dom (sm, z)))
    in
    walk_tau tau x

  let rec subst sigma tau (Apply (x, args)) =
    let gamma = (sigma.pre *** sigma.dom) *** tau in
    let head_arity = shape_lookup gamma x in
    let new_args =
      List.map
        (fun (y, child) ->
          let child_binder = arity_lookup head_arity y in
          (* β :: τ adds β as the new outermost extension; γ ** β = γ_base *** (β :: τ). *)
          (y, subst sigma (child_binder :: tau) child))
        args
    in
    match classify sigma tau x with
    | In_pre s | In_tau s -> Apply (s, new_args)
    | In_dom (sm, z) ->
        let e = List.assoc z sm in
        let aux_sigma =
          { pre = sigma.pre *** sigma.cod ;
            dom = [head_arity] ;
            cod = tau ;
            sub = [new_args] }
        in
        subst aux_sigma [] e
end

(* --- List-based carrier: shape = arity, slot = int (de Bruijn from right). --- *)

module ListCarrier = struct
  type arity = Ar of arity list
  type shape = Sh of arity list
  type slot = int

  let ( ** ) (Sh gs : shape) (Ar a : arity) : shape = Sh (gs @ a)

  type 'a slot_map = (slot * 'a) list

  let entries_of_list xs =
    let n = List.length xs in
    List.mapi (fun i a -> (n - 1 - i, a)) xs

  let shape_entries (Sh xs) = entries_of_list xs
  let arity_entries (Ar xs) = entries_of_list xs

  let lookup_in_list xs x =
    try List.nth xs (List.length xs - 1 - x)
    with _ -> failwith "lookup: slot out of range"

  let shape_lookup (Sh xs) x = lookup_in_list xs x
  let arity_lookup (Ar xs) x = lookup_in_list xs x

  let shape_shift _gamma (Ar a) x = x + List.length a
  let arity_shift _gamma _alpha z = z

  type slot_sort = Left of slot | Right of slot

  let slot_sort _gamma (Ar a) x =
    let n_alpha = List.length a in
    if x < n_alpha then Right x else Left (x - n_alpha)

  let empty_arity = Ar []
end

(* --- Tests on ListCarrier --- *)

module M = Make (ListCarrier)
open ListCarrier
open M

let rec pp_expr ppf (Apply (k, args)) =
  match args with
  | [] -> Format.fprintf ppf "%d" k
  | _ ->
      let pp_pair ppf (s, e) = Format.fprintf ppf "%d↦%a" s pp_expr e in
      Format.fprintf ppf "%d(%a)" k
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
           pp_pair)
        args

let try_validate name shape e =
  try
    validate shape e ;
    Format.printf "%-32s OK  %a@\n" name pp_expr e
  with Invalid m -> Format.printf "%-32s FAIL %s@\n" name m

let try_subst name shape sigma tau e =
  try
    let e' = subst sigma tau e in
    validate shape e' ;
    Format.printf "%-32s OK  %a@\n" name pp_expr e' ;
    e'
  with
  | Invalid m ->
      Format.printf "%-32s FAIL %s@\n" name m ;
      Apply (0, [])
  | exn ->
      Format.printf "%-32s EXN  %s@\n" name (Printexc.to_string exn) ;
      Apply (0, [])

(* The eight-symbol gamma from syntax.ml's ExampleExpr. *)
let gamma_expr =
  Sh [
    Ar [] ;                            (* slot 7: ℕ *)
    Ar [Ar []] ;                       (* slot 6: Vec *)
    Ar [] ;                            (* slot 5: zero *)
    Ar [Ar []] ;                       (* slot 4: succ *)
    Ar [Ar []; Ar []] ;                (* slot 3: plus *)
    Ar [Ar [Ar []]] ;                  (* slot 2: λ *)
    Ar [Ar []; Ar [Ar []]] ;           (* slot 1: Π *)
    Ar [] ;                            (* slot 0: x *)
  ]

let () = Format.printf "============ ExampleExpr ============@\n"

(* succ (succ zero) *)
let e_succ_succ_zero =
  Apply (4, [(0, Apply (4, [(0, Apply (5, []))]))])
let _ = try_validate "succ (succ zero)" gamma_expr e_succ_succ_zero

(* plus zero x : plus has arity Ar [Ar []; Ar []], slots [(1, Ar []); (0, Ar [])] *)
let e_plus_zero_x =
  Apply (3, [(1, Apply (5, [])); (0, Apply (0, []))])
let _ = try_validate "plus zero x" gamma_expr e_plus_zero_x

(* λ _ . x  in gamma : λ at slot 2, x at slot 0 in gamma; under λ's binder
   (one slot), x shifts to slot 1. *)
let e_lam_x =
  Apply (2, [(0, Apply (1, []))])
let _ = try_validate "λ _ . x" gamma_expr e_lam_x

(* Π ℕ (n . Vec n) : Π at slot 1, ℕ at slot 7, Vec at slot 6.
   Π's arity is Ar [Ar []; Ar [Ar []]], entries [(1, Ar []); (0, Ar [Ar []])].
   First arg (slot 1 in args) is in gamma; second arg (slot 0 in args)
   is in gamma ** Ar [Ar []] (one new binder, slot 0 there is the bound n,
   gamma's slots shift up by 1). *)
let e_pi =
  Apply (1, [
    (1, Apply (7, [])) ;
    (0, Apply (7 (* Vec was at 6, shifted up by 1 *), [(0, Apply (0, []))])) ;
  ])
let _ = try_validate "Π ℕ (n . Vec n)" gamma_expr e_pi

(* --- Substitution examples mirroring syntax.ml's ExampleSubst{1,2}. --- *)

let () = Format.printf "============ ExampleSubst1 ============@\n"

(* pre : a one-slot shape, that slot's arity is λ-arity = Ar [Ar [Ar []]] *)
let pre1 : shape = Sh [Ar [Ar [Ar []]]]

(* dom : one extension that adds one slot of arity Ar [] (an ordinary variable x) *)
let dom1 : arity list = [Ar [Ar []]]

(* cod : one extension that adds three slots, each of arity Ar [] (y, z, w) *)
let cod1 : arity list = [Ar [Ar []; Ar []; Ar []]]

let pre1_dom1 = pre1 *** dom1
let pre1_cod1 = pre1 *** cod1

(* e = λ _ . x  in pre *** dom *)
let e_subst1 = Apply (1, [(0, Apply (1, []))])
let _ = try_validate "λ _ . x  in pre*dom" pre1_dom1 e_subst1

(* sub : list mirroring dom; one slot_map with one entry mapping slot 0
   to "y" (slot 2 in pre *** cod, since pre*cod has 4 slots: λ=3, y=2, z=1, w=0). *)
let sub_y = Apply (2, [])
let _ = try_validate "y  in pre*cod" pre1_cod1 sub_y

let sigma1 = { pre = pre1 ; dom = dom1 ; cod = cod1 ; sub = [[(0, sub_y)]] }

let _ = try_subst "subst λ_.x ↦ λ_.y" pre1_cod1 sigma1 [] e_subst1

let () = Format.printf "============ ExampleSubst2 ============@\n"

(* e2 = λ _ . λ _ . x  in pre *** dom.
   Outer λ at slot 1.  Inner λ in (pre*dom)**Ar[Ar[]] (3 slots: λ=2, x=1, bound₁=0)
     uses slot 2 for λ.
   Innermost x in ((pre*dom)**Ar[Ar[]])**Ar[Ar[]] (4 slots: λ=3, x=2, bound₁=1, bound₂=0)
     uses slot 2 for x. *)
let e_subst2 =
  Apply (1, [(0, Apply (2, [(0, Apply (2, []))]))])
let _ = try_validate "λ _ . λ _ . x  in pre*dom" pre1_dom1 e_subst2

let _ = try_subst "subst λ_λ_.x ↦ λ_λ_.y" pre1_cod1 sigma1 [] e_subst2

let () = Format.printf "============ Identity test (In_tau) ============@\n"

(* λ y . y  in gamma_expr.  Body refers to the bound y, so the head of the body
   classifies as In_tau under the recursive descent. *)
let e_id = Apply (2, [(0, Apply (0, []))])
let _ = try_validate "λ y . y" gamma_expr e_id

let sigma_id = { pre = gamma_expr ; dom = [] ; cod = [] ; sub = [] }
let _ = try_subst "subst id (λ y . y)" gamma_expr sigma_id [] e_id
