(* syntaxAction2.ml — refinement of syntaxAction.ml.

   The substitution record carries a single arity in [dom] and a single
   slot_map in [sub] (no list wrapping).  [cod] stays a list because the
   auxiliary recursion sets [aux.cod = τ] and τ is genuinely a list; the
   empty list [] is a strict definitional unit by the cons-as-snoc
   definition of [***], so no carrier obligation about γ ** empty_arity = γ
   arises.

   The CARRIER signature is unchanged from syntaxAction.ml. *)

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
    dom : arity ;
    cod : arity list ;
    sub : expr slot_map ;
  }

  type loc =
    | In_pre of slot
    | In_tau of slot
    | In_dom of slot

  let shift_through base lst slot =
    fst (List.fold_right
           (fun alpha (sl, shape) ->
             (shape_shift shape alpha sl, shape ** alpha))
           lst
           (slot, base))

  let classify sigma tau x =
    let walk_dom x =
      match slot_sort sigma.pre sigma.dom x with
      | Right z -> In_dom z
      | Left p -> In_pre (shift_through sigma.pre sigma.cod p)
    in
    let rec walk_tau tau_left x =
      match tau_left with
      | [] -> walk_dom x
      | beta :: rest ->
          let inner_dom = (sigma.pre ** sigma.dom) *** rest in
          let inner_cod = (sigma.pre *** sigma.cod) *** rest in
          (match slot_sort inner_dom beta x with
           | Right z -> In_tau (arity_shift inner_cod beta z)
           | Left y ->
               (match walk_tau rest y with
                | In_pre s -> In_pre (shape_shift inner_cod beta s)
                | In_tau s -> In_tau (shape_shift inner_cod beta s)
                | In_dom z -> In_dom z))
    in
    walk_tau tau x

  let rec subst sigma tau (Apply (x, args)) =
    let gamma = (sigma.pre ** sigma.dom) *** tau in
    let head_arity = shape_lookup gamma x in
    let new_args =
      List.map
        (fun (y, child) ->
          let child_position = arity_lookup head_arity y in
          (y, subst sigma (child_position :: tau) child))
        args
    in
    match classify sigma tau x with
    | In_pre s | In_tau s -> Apply (s, new_args)
    | In_dom z ->
        let e = List.assoc z sigma.sub in
        let aux_sigma =
          { pre = sigma.pre *** sigma.cod ;
            dom = head_arity ;
            cod = tau ;
            sub = new_args }
        in
        subst aux_sigma [] e
end

(* --- List carrier: shape = arity list with Sh tag; slot = int (de Bruijn from right). --- *)

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

(* --- Tree carrier: shape/arity = binary tree of arities; slot = path. --- *)

module TreeCarrier = struct
  type 'a tree = TEmpty | TSlot of 'a | TOplus of 'a tree * 'a tree
  type arity = Arity of arity tree
  type shape = Shape of arity tree
  type slot = Here | L of slot | R of slot

  let ( ** ) (Shape t : shape) (Arity a : arity) : shape =
    Shape (TOplus (t, a))

  type 'a slot_map = (slot * 'a) list

  let rec entries_of_tree path = function
    | TEmpty -> []
    | TSlot a -> [(path Here, a)]
    | TOplus (l, r) ->
        entries_of_tree (fun p -> path (L p)) l
        @ entries_of_tree (fun p -> path (R p)) r

  let shape_entries (Shape t) = entries_of_tree (fun p -> p) t
  let arity_entries (Arity t) = entries_of_tree (fun p -> p) t

  let rec lookup_in_tree t = function
    | Here -> (match t with TSlot a -> a | _ -> failwith "lookup: Here on non-Slot")
    | L p -> (match t with TOplus (l, _) -> lookup_in_tree l p | _ -> failwith "lookup: L on non-Oplus")
    | R p -> (match t with TOplus (_, r) -> lookup_in_tree r p | _ -> failwith "lookup: R on non-Oplus")

  let shape_lookup (Shape t) x = lookup_in_tree t x
  let arity_lookup (Arity t) x = lookup_in_tree t x

  let shape_shift _gamma _alpha x = L x
  let arity_shift _gamma _alpha z = R z

  type slot_sort = Left of slot | Right of slot

  let slot_sort _gamma _alpha = function
    | L p -> Left p
    | R p -> Right p
    | Here -> failwith "slot_sort: Here at γ ** α (impossible)"

  let empty_arity = Arity TEmpty
end

(* --- Tests --- *)

let () = Format.printf "\n############ ListCarrier ############\n@\n"

module ML = Make (ListCarrier)

let test_list () =
  let open ListCarrier in
  let open ML in

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
  in

  let try_validate name shape e =
    try validate shape e ; Format.printf "%-32s OK  %a@\n" name pp_expr e
    with Invalid m -> Format.printf "%-32s FAIL %s@\n" name m
  in
  let try_subst name shape sigma tau e =
    try
      let e' = subst sigma tau e in
      validate shape e' ;
      Format.printf "%-32s OK  %a@\n" name pp_expr e' ;
      e'
    with
    | Invalid m -> Format.printf "%-32s FAIL %s@\n" name m ; Apply (0, [])
    | exn -> Format.printf "%-32s EXN  %s@\n" name (Printexc.to_string exn) ; Apply (0, [])
  in

  let gamma_expr =
    Sh [
      Ar [] ;                           (* 7: ℕ *)
      Ar [Ar []] ;                      (* 6: Vec *)
      Ar [] ;                           (* 5: zero *)
      Ar [Ar []] ;                      (* 4: succ *)
      Ar [Ar []; Ar []] ;               (* 3: plus *)
      Ar [Ar [Ar []]] ;                 (* 2: λ *)
      Ar [Ar []; Ar [Ar []]] ;          (* 1: Π *)
      Ar [] ;                           (* 0: x *)
    ]
  in

  Format.printf "------ ExampleExpr ------@\n" ;
  let e1 = Apply (4, [(0, Apply (4, [(0, Apply (5, []))]))]) in
  ignore (try_validate "succ (succ zero)" gamma_expr e1) ;
  let e2 = Apply (3, [(1, Apply (5, [])); (0, Apply (0, []))]) in
  ignore (try_validate "plus zero x" gamma_expr e2) ;
  let e_lam = Apply (2, [(0, Apply (1, []))]) in
  ignore (try_validate "λ _ . x" gamma_expr e_lam) ;

  Format.printf "------ ExampleSubst1 ------@\n" ;
  let pre1 = Sh [Ar [Ar [Ar []]]] in
  let dom1 = Ar [Ar []] in
  let cod1 = [Ar [Ar []; Ar []; Ar []]] in
  let pre_dom1 = pre1 ** dom1 in
  let pre_cod1 = pre1 *** cod1 in
  let e_subst1 = Apply (1, [(0, Apply (1, []))]) in
  ignore (try_validate "λ _ . x in pre*dom" pre_dom1 e_subst1) ;
  let sub_y = Apply (2, []) in
  let pre_cod1_ext = pre_cod1 ** Ar [] in
  ignore (try_validate "y in pre*cod ** Ar []" pre_cod1_ext sub_y) ;
  let sigma1 = { pre = pre1 ; dom = dom1 ; cod = cod1 ; sub = [(0, sub_y)] } in
  ignore (try_subst "subst λ_.x ↦ λ_.y" pre_cod1 sigma1 [] e_subst1) ;

  Format.printf "------ ExampleSubst2 ------@\n" ;
  let e_subst2 = Apply (1, [(0, Apply (2, [(0, Apply (2, []))]))]) in
  ignore (try_validate "λ _ . λ _ . x in pre*dom" pre_dom1 e_subst2) ;
  ignore (try_subst "subst λ_λ_.x ↦ λ_λ_.y" pre_cod1 sigma1 [] e_subst2) ;

  Format.printf "------ Identity test (In_tau) ------@\n" ;
  (* For this test in the new design, σ.dom = empty_arity (Ar []) so it adds no slots.
     σ.pre ** empty_arity = σ.pre in ListCarrier (definitionally). *)
  let e_id = Apply (2, [(0, Apply (0, []))]) in
  ignore (try_validate "λ y . y" gamma_expr e_id) ;
  let sigma_id = { pre = gamma_expr ; dom = empty_arity ; cod = [] ; sub = [] } in
  ignore (try_subst "subst id (λ y . y)" gamma_expr sigma_id [] e_id)

let () = test_list ()

let () = Format.printf "\n############ TreeCarrier ############\n@\n"

module MT = Make (TreeCarrier)

let test_tree () =
  let open TreeCarrier in
  let open MT in

  let rec pp_slot ppf = function
    | Here -> Format.fprintf ppf "h"
    | L p -> Format.fprintf ppf "l%a" pp_slot p
    | R p -> Format.fprintf ppf "r%a" pp_slot p
  in

  let rec pp_expr ppf (Apply (s, args)) =
    match args with
    | [] -> pp_slot ppf s
    | _ ->
        let pp_pair ppf (s, e) = Format.fprintf ppf "%a↦%a" pp_slot s pp_expr e in
        Format.fprintf ppf "%a(%a)" pp_slot s
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
             pp_pair)
          args
  in

  let try_validate name shape e =
    try validate shape e ; Format.printf "%-36s OK  %a@\n" name pp_expr e
    with Invalid m -> Format.printf "%-36s FAIL %s@\n" name m
  in
  let try_subst name shape sigma tau e =
    try
      let e' = subst sigma tau e in
      validate shape e' ;
      Format.printf "%-36s OK  %a@\n" name pp_expr e' ;
      e'
    with
    | Invalid m -> Format.printf "%-36s FAIL %s@\n" name m ; Apply (Here, [])
    | exn -> Format.printf "%-36s EXN  %s@\n" name (Printexc.to_string exn) ; Apply (Here, [])
  in

  (* Convenience: build a right-leaning arity tree from a list of arities. *)
  let rec from_list = function
    | [] -> TEmpty
    | [x] -> TSlot x
    | x :: xs -> TOplus (TSlot x, from_list xs)
  in
  let ar_list xs = Arity (from_list xs) in
  let sh_list xs = Shape (from_list xs) in

  (* The same 8-symbol context, expressed as a tree. *)
  let var = Arity TEmpty in
  let succ_arity = ar_list [var] in
  let plus_arity = ar_list [var; var] in
  let bind1_arity = ar_list [var] in
  let lam_arity = ar_list [bind1_arity] in
  let pi_arity = ar_list [var; bind1_arity] in
  let vec_arity = ar_list [var] in
  let gamma_expr =
    sh_list [
      var ;         (* ℕ *)
      vec_arity ;   (* Vec *)
      var ;         (* zero *)
      succ_arity ;  (* succ *)
      plus_arity ;  (* plus *)
      lam_arity ;   (* λ *)
      pi_arity ;    (* Π *)
      var ;         (* x *)
    ]
  in

  Format.printf "------ ExampleExpr ------@\n" ;
  (* Slot of "succ" in gamma_expr: position 3 in the from_list of 8 elements.
     from_list [a₀; …; a₇] = TOplus (TSlot a₀, TOplus(TSlot a₁, ..., TSlot a₇)).
     Path of position i (0-indexed) for i < n-1: R^i (L Here); for i = n-1: R^(n-1) Here. *)
  let rec rights k inner = if k = 0 then inner else R (rights (k - 1) inner) in
  let pos n i = if i = n - 1 then rights (n - 1) Here else rights i (L Here) in
  let p8 = pos 8 in
  let p_zero = p8 2 in
  let p_succ = p8 3 in
  let p_plus = p8 4 in
  let p_lam = p8 5 in
  let p_pi = p8 6 in
  let p_x = p8 7 in
  let p_nat = p8 0 in
  let p_vec = p8 1 in

  let e1 = Apply (p_succ, [(Here, Apply (L p_succ, [(Here, Apply (L (L p_zero), []))]))]) in
  ignore (try_validate "succ (succ zero)" gamma_expr e1) ;

  (* plus zero x: plus is a 2-arg operation.  Its arity is TOplus(TSlot var, TSlot var)
     so arity_entries are [(L Here, var); (R Here, var)].  Args keyed by L Here (first arg)
     and R Here (second arg). *)
  let e2 = Apply (p_plus, [(L Here, Apply (L p_zero, [])); (R Here, Apply (L p_x, []))]) in
  ignore (try_validate "plus zero x" gamma_expr e2) ;

  (* λ y . y: head λ; body in gamma_expr ** bind1_arity (one new slot at R Here = the bound y).
     Body is just sym (R Here). *)
  let e_lam = Apply (p_lam, [(Here, Apply (R Here, []))]) in
  ignore (try_validate "λ y . y" gamma_expr e_lam) ;

  (* Π ℕ (n . Vec n): Π's arity is TOplus(TSlot var, TSlot bind1_arity).
     First arg ℕ lives in gamma_expr ** Arity TEmpty (the var position, contributes
     no slots but still wraps the tree); ℕ is therefore at L p_nat there.
     Second arg lives in gamma_expr ** bind1_arity: Vec at L p_vec, bound n at R Here.
     Vec's own child (the "n") lives in (gamma_expr ** bind1_arity) ** Arity TEmpty
     (the var position of Vec's slot), which wraps once more — so n is at L (R Here). *)
  let e_pi =
    Apply (p_pi, [
      (L Here, Apply (L p_nat, [])) ;
      (R Here, Apply (L p_vec, [(Here, Apply (L (R Here), []))])) ;
    ])
  in
  ignore (try_validate "Π ℕ (n . Vec n)" gamma_expr e_pi) ;

  Format.printf "------ ExampleSubst1 ------@\n" ;
  (* pre : single-slot shape, slot's arity = λ_arity. *)
  let pre1 = sh_list [lam_arity] in
  (* dom : single arity for the position of x. *)
  let dom1 = ar_list [var] in  (* = bind1_arity, but explicit *)
  (* cod : single arity with three sub-positions (y, z, w as positions). *)
  let cod1 = [ar_list [var; var; var]] in
  let pre_dom1 = pre1 ** dom1 in
  let pre_cod1 = pre1 *** cod1 in
  (* e = λ _. x in pre ** dom.  pre ** dom has slots:
     pre = Shape(TSlot lam_arity), so its slot is Here in the pre_tree.
     ** dom adds dom's slots: dom = TSlot var, so contributes one slot.
     pre ** dom = Shape(TOplus(TSlot lam_arity, TSlot var)).
     λ at L Here, x at R Here. *)
  let e_subst1 = Apply (L Here, [(Here, Apply (L (R Here), []))]) in
  ignore (try_validate "λ _ . x in pre*dom" pre_dom1 e_subst1) ;
  (* sub_y : "y" in pre *** cod ** Arity TEmpty (the arity of dom's only slot).
     pre *** cod = pre ** Arity (TOplus(TSlot var, TOplus(TSlot var, TSlot var))) (single arity, 3 inner slots).
     Slots of pre *** cod: L Here = λ, R (L Here) = y, R (R (L Here)) = z, R (R (R Here)) = w.
     ** Arity TEmpty wraps in TOplus(_, TEmpty); y becomes L (R (L Here)). *)
  let sub_y = Apply (L (R (L Here)), []) in
  let pre_cod1_ext = pre_cod1 ** Arity TEmpty in
  ignore (try_validate "y in pre*cod ** Ar[]" pre_cod1_ext sub_y) ;
  let sigma1 = { pre = pre1 ; dom = dom1 ; cod = cod1 ; sub = [(Here, sub_y)] } in
  ignore (try_subst "subst λ_.x ↦ λ_.y" pre_cod1 sigma1 [] e_subst1)

let () = test_tree ()
