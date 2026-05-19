import HigherRankSyntax.Action.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

Each head slot is classified by `classify` into either a Γ-slot (`XPos.base`, the
weakening of some `p : Slot Γ` through τ) or a τ-binder (`XPos.ext`, identified by a
split of τ as `τ_above ++ β :: τ_below` with a binder `i` of `β`).  The
slot-correspondence witness lives in the inductive's index, so pattern matching on
`classify`'s result yields it definitionally — no `Eq.rec`.

`lift.aux` walks `Expr (Γ ⋈* τ)`; the Γ-slot case substitutes via σ and uses
`inst.aux` directly on σ's image, threading the target weakening as a renaming.
`inst.aux` walks `Expr ((Δ ⋈ α) ⋈* τ)`, carries a renaming `ρ : Δ →ʳ Ξ`, and
maps Δ-slots through `ρ` during traversal.
-/

namespace Action

/-! ## Substitutions and instantiations -/

/-- A substitution from `Γ` to `Δ`. -/
abbrev Subst {C : Carrier} (Γ Δ : Shape C) : Type :=
  (p : Slot Γ) → Expr (Δ ⋈ p.arity)

/-- An instantiation of an α-binder above `Γ`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (Γ : Shape C) : Type :=
  (i : C.Binder α) → Expr (Γ ⋈ i.arity)

/-! ## Slot classification -/

/-- The slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)` corresponding to
binder `i` of `β`.  Iterates `.there` over `τ_above` from `.here i`. -/
private def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → Slot (Γ ⋈* (τ_above ++ β :: τ_below))
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- A `tauSlot`'s arity is the binder's sub-arity. -/
private theorem tauSlot_arity {C : Carrier} (Γ : Shape C)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) : (tauSlot Γ τ_above β τ_below i).arity = i.arity := by
  induction τ_above with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Position of a slot in `Γ ⋈* τ`: a Γ-slot weakened through τ, or a τ-binder. -/
private inductive XPos {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Slot (Γ ⋈* τ) → Type where
  | base : ∀ {τ : List C.Arity}, (p : Slot Γ) →
           XPos Γ τ (Renaming.weakenList Γ τ p)
  | ext  : ∀ {τ_above : List C.Arity} {β : C.Arity} {τ_below : List C.Arity},
           (i : C.Binder β) →
           XPos Γ (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)

/-- Classify a slot in an iterated extension. -/
private def classify {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → (p : Slot (Γ ⋈* τ)) → XPos Γ τ p
  | [],       p        => XPos.base p
  | _ :: _,   .here i  => XPos.ext (τ_above := []) i
  | β :: τ',  .there p =>
      match classify τ' p with
      | XPos.base q => XPos.base q
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) j =>
          XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) j

/-- Classifying a Γ-slot weakened through τ recovers the original Γ-slot. -/
@[simp] private theorem classify_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) (p : Slot Γ) :
    classify τ ((Renaming.weakenList Γ τ).toFun p) = XPos.base p := by
  induction τ with
  | nil => rfl
  | cons β rest ih =>
    show classify (β :: rest)
           (.there ((Renaming.weakenList Γ rest).toFun p)) = XPos.base p
    simp [classify, ih]

/-- Classifying a `tauSlot` recovers the corresponding `XPos.ext`. -/
@[simp] private theorem classify_tauSlot {C : Carrier} {Γ : Shape C}
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) :
    classify (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)
      = XPos.ext (τ_above := τ_above) (β := β) (τ_below := τ_below) i := by
  induction τ_above with
  | nil => rfl
  | cons a rest ih =>
    show classify (a :: (rest ++ β :: τ_below))
           (.there (tauSlot Γ rest β τ_below i))
         = XPos.ext (τ_above := a :: rest) (β := β) (τ_below := τ_below) i
    simp [classify, ih]

/-! ## Walkers -/

/-- α-instantiation walker.  Walks `e : Expr ((Δ ⋈ α) ⋈* τ)` by classifying each head:
τ-binder rebuilds the same `tauSlot` at the Ξ-side; Δ-slots are mapped through `ρ` and
then weakened through τ; α-binders plug `ι j` and recurse at smaller arity. -/
private def inst.aux {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) : Expr (Ξ ⋈* τ) :=
  match e with
  | .apply' p α_h h_α_h args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          let new_args : (i : C.Binder α_h) →
              Expr ((Ξ ⋈* (ta ++ b :: tb)) ⋈ i.arity) :=
            fun i => inst.aux α ρ ι (i.arity :: (ta ++ b :: tb)) (args i)
          have new_h : (tauSlot Ξ ta b tb i).arity = α_h :=
            (tauSlot_arity Ξ ta b tb i).trans
              ((tauSlot_arity (Δ ⋈ α) ta b tb i).symm.trans h_α_h)
          Expr.apply' (tauSlot Ξ ta b tb i) α_h new_h new_args
      | XPos.base q =>
          match q with
          | .there r =>
              let new_args : (i : C.Binder α_h) →
                  Expr ((Ξ ⋈* τ) ⋈ i.arity) :=
                fun i => inst.aux α ρ ι (i.arity :: τ) (args i)
              have new_h : ((Renaming.weakenList Ξ τ).toFun (ρ r)).arity = α_h :=
                ((Renaming.weakenList Ξ τ).arity (ρ r)).trans
                  ((ρ.arity r).trans
                    (((Renaming.weakenList (Δ ⋈ α) τ).arity (.there r)).symm.trans h_α_h))
              Expr.apply' ((Renaming.weakenList Ξ τ).toFun (ρ r)) α_h new_h new_args
          | .here j =>
              have hs : j.arity = α_h :=
                ((Renaming.weakenList (Δ ⋈ α) τ).arity (.here j)).symm.trans h_α_h
              match hs with
              | rfl =>
                  let new_args : (i : C.Binder j.arity) →
                      Expr ((Ξ ⋈* τ) ⋈ i.arity) :=
                    fun i => inst.aux α ρ ι (i.arity :: τ) (args i)
                  inst.aux j.arity (Renaming.weakenList Ξ τ) new_args [] (ι j)
termination_by (⟨α, _, e⟩ : (_ : C.Arity) ×' Σ Γ : Shape C, Expr Γ)
decreasing_by
  -- ext args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- .there args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- .here args descent
  · exact PSigma.Lex.right _ (Expr.Subterm.of_arg _ _ _ _ _)
  -- α decreases (j.arity ≺ α)
  · exact PSigma.Lex.left _ _ ⟨j, rfl⟩

/-! ## η-fillers and instantiation η-laws -/

/-- Canonical η-fillers for an α-binder over a shape with α at the top.
At each binder position `i`, returns the η-expansion of the bound variable `.here i`. -/
private def η_fillers {C : Carrier} (Δ : Shape C) (α : C.Arity) : Inst α (Δ ⋈ α) :=
  fun i => Expr.η ⟨.here i, rfl⟩

@[simp] private theorem inst_aux_ext_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) (α_h : C.Arity)
    (h : (tauSlot (Δ ⋈ α) τ_above β τ_below i).arity = α_h)
    (args : (j : C.Binder α_h) →
      Expr ((Δ ⋈ α) ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    inst.aux α ρ ι (τ_above ++ β :: τ_below)
      (Expr.apply' (tauSlot (Δ ⋈ α) τ_above β τ_below i)
        α_h h args)
      =
    Expr.apply' (tauSlot Ξ τ_above β τ_below i)
      α_h
      ((tauSlot_arity Ξ τ_above β τ_below i).trans
        ((tauSlot_arity (Δ ⋈ α) τ_above β τ_below i).symm.trans h))
      (fun j => inst.aux α ρ ι (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ_above ++ β :: τ_below,
        Expr.apply' (tauSlot (Δ ⋈ α) τ_above β τ_below i)
          α_h h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] private theorem inst_aux_base_there_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (r : Slot Δ) (α_h : C.Arity)
    (h : ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.there r)).arity = α_h)
    (args : (j : C.Binder α_h) → Expr ((Δ ⋈ α) ⋈* τ ⋈ j.arity)) :
    inst.aux α ρ ι τ
      (Expr.apply' ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.there r))
        α_h h args)
      =
    Expr.apply' ((Renaming.weakenList Ξ τ).toFun (ρ r)) α_h
      (((Renaming.weakenList Ξ τ).arity (ρ r)).trans
        ((ρ.arity r).trans
          (((Renaming.weakenList (Δ ⋈ α) τ).arity (.there r)).symm.trans h)))
      (fun j => inst.aux α ρ ι (j.arity :: τ) (args j)) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply' ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.there r))
          α_h h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

@[simp] private theorem inst_aux_base_here_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
    (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (τ : List C.Arity) (j : C.Binder α)
    (h : ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.here j)).arity = j.arity)
    (args : (k : C.Binder j.arity) → Expr ((Δ ⋈ α) ⋈* τ ⋈ k.arity)) :
    inst.aux α ρ ι τ
      (Expr.apply' ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.here j))
        j.arity h args)
      =
    inst.aux j.arity (Renaming.weakenList Ξ τ)
      (fun k => inst.aux α ρ ι (k.arity :: τ) (args k)) [] (ι j) := by
  delta inst.aux
  change inst.aux._unary (C := C)
      ⟨Δ, ⟨Ξ, ⟨α, ⟨ρ, ⟨ι, ⟨τ,
        Expr.apply' ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.here j))
          j.arity h args⟩⟩⟩⟩⟩⟩ = _
  rw [inst.aux._unary.eq_1]
  simp [classify_weakenList]

private theorem inst_aux_η_tauSlot {C : Carrier} :
    ∀ {Δ Ξ : Shape C} (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      inst.aux α ρ ι (i.arity :: (τ_above ++ β :: τ_below))
        (Expr.η ⟨tauSlot (Δ ⋈ α) τ_above β τ_below i, tauSlot_arity (Δ ⋈ α) τ_above β τ_below i⟩)
        =
      Expr.η ⟨tauSlot Ξ τ_above β τ_below i, tauSlot_arity Ξ τ_above β τ_below i⟩
  | Δ, Ξ, α, ρ, ι, τ_above, β, τ_below, i => by
    unfold Expr.η
    change inst.aux α ρ ι ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply' (tauSlot (Δ ⋈ α) (i.arity :: τ_above) β τ_below i)
          i.arity (tauSlot_arity (Δ ⋈ α) (i.arity :: τ_above) β τ_below i)
          (fun k =>
            Expr.η ⟨.here k, rfl⟩))
        =
      Expr.apply' (tauSlot Ξ (i.arity :: τ_above) β τ_below i)
        i.arity (tauSlot_arity Ξ (i.arity :: τ_above) β τ_below i)
        (fun k =>
          Expr.η ⟨.here k, rfl⟩)
    rw [inst_aux_ext_eq]
    congr 1
    funext k
    exact inst_aux_η_tauSlot α ρ ι [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

private theorem inst_aux_η_inv_of {C : Carrier} (Δ : Shape C) (α : C.Arity)
    (hη : ∀ (j : C.Binder α) {Δ' Ξ' : Shape C}
      (ρ : Δ' →ʳ Ξ') (ι : Inst j.arity Ξ') (v : Expr.J Δ' j.arity),
      inst.aux j.arity ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) j.arity ((ρ.arity v.val).trans v.property) ι) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α) τ e = e
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α)
          (j.arity :: τ) (args j) = args j := by
      intro j
      exact inst_aux_η_inv_of Δ α hη (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      rw [inst_aux_ext_eq]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      cases q with
      | there r =>
        rw [inst_aux_base_there_eq]
        congr 1
        funext j
        exact ih_arg j
      | here j =>
        have hs : j.arity = α_h :=
          ((Renaming.weakenList (Δ ⋈ α) τ).arity (.here j)).symm.trans h
        cases hs
        rw [inst_aux_base_here_eq]
        change inst.aux j.arity (Renaming.weakenList (Δ ⋈ α) τ)
            (fun k => inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) []
            (Expr.η ⟨.here j, rfl⟩)
          = Expr.apply' ((Renaming.weakenList (Δ ⋈ α) τ).toFun (.here j))
            j.arity h args
        rw [hη j (Δ' := Δ ⋈ α) (Ξ' := (Δ ⋈ α) ⋈* τ)
          (ρ := Renaming.weakenList (Δ ⋈ α) τ)
          (ι := fun k =>
            inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α)
              (k.arity :: τ) (args k)) (v := ⟨.here j, rfl⟩)]
        congr 1
        funext k
        exact ih_arg k
termination_by τ e => (⟨(Δ ⋈ α) ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

private theorem inst_aux_η_bundle {C : Carrier} (α : C.Arity) :
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (v : Expr.J Δ α),
      inst.aux α ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α) τ e = e) := by
  refine C.subWf.induction (C := fun α =>
    (∀ {Δ Ξ : Shape C} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
      (v : Expr.J Δ α),
      inst.aux α ρ ι [] (Expr.η v)
        = Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι)
    ∧
    (∀ (Δ : Shape C) (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α) τ e = e)) α ?_
  intro α ih
  constructor
  · intro Δ Ξ ρ ι v
    rcases v with ⟨p, hp⟩
    unfold Expr.η
    change inst.aux α ρ ι []
        (Expr.apply' ((Renaming.weakenList (Δ ⋈ α) []).toFun (.there p))
          α hp (fun i => Expr.η ⟨.here i, rfl⟩))
        = Expr.apply' (ρ p) α ((ρ.arity p).trans hp) ι
    rw [inst_aux_base_there_eq]
    congr 1
    funext i
    unfold Expr.η
    change inst.aux α ρ ι [i.arity]
        (Expr.apply' ((Renaming.weakenList (Δ ⋈ α) [i.arity]).toFun (.here i))
          i.arity rfl
          (fun k => Expr.η ⟨.here k, rfl⟩))
        = ι i
    rw [inst_aux_base_here_eq]
    change inst.aux i.arity (Renaming.weakenList Ξ [i.arity])
        (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η ⟨.here k, rfl⟩)) [] (ι i)
      = ι i
    have hargs : (fun k : C.Binder i.arity => inst.aux α ρ ι (k.arity :: [i.arity])
          (Expr.η ⟨.here k, rfl⟩))
        = η_fillers Ξ i.arity := by
      funext k
      unfold η_fillers
      exact inst_aux_η_tauSlot α ρ ι [] i.arity [] k
    rw [hargs]
    exact (ih i.arity ⟨i, rfl⟩).2 Ξ [] (ι i)
  · intro Δ
    exact inst_aux_η_inv_of Δ α (fun j => (ih j.arity ⟨j, rfl⟩).1)

private theorem inst_aux_η {C : Carrier} {Δ Ξ : Shape C}
    (α : C.Arity) (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ)
    (v : Expr.J Δ α) :
    inst.aux α ρ ι [] (Expr.η v)
      =
    Expr.apply' (ρ v.val) α ((ρ.arity v.val).trans v.property) ι :=
  (inst_aux_η_bundle α).1 ρ ι v

private theorem inst_aux_η_inv {C : Carrier} (Δ : Shape C) (α : C.Arity) :
    ∀ (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)),
      inst.aux α (Renaming.weakenList Δ [α]) (η_fillers Δ α) τ e = e :=
  (inst_aux_η_bundle α).2 Δ

/-- Kleisli extension walker.  Walks `e : Expr (Γ ⋈* τ)` by classifying each head:
τ-binder rebuilds; Γ-slot substitutes via σ and threads the target weakening through
`inst.aux`. -/
private def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (e : Expr (Γ ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match e with
  | .apply' p α_h h_α_h args =>
      match classify τ p with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
          let new_args : (i : C.Binder α_h) →
              Expr ((Δ ⋈* (ta ++ b :: tb)) ⋈ i.arity) :=
            fun i => lift.aux σ (i.arity :: (ta ++ b :: tb)) (args i)
          have new_h : (tauSlot Δ ta b tb i).arity = α_h :=
            (tauSlot_arity Δ ta b tb i).trans
              ((tauSlot_arity Γ ta b tb i).symm.trans h_α_h)
          Expr.apply' (tauSlot Δ ta b tb i) α_h new_h new_args
      | XPos.base q =>
          have hs : q.arity = α_h :=
            ((Renaming.weakenList Γ τ).arity q).symm.trans h_α_h
          match hs with
          | rfl =>
              let new_args : (i : C.Binder q.arity) →
                  Expr ((Δ ⋈* τ) ⋈ i.arity) :=
                fun i => lift.aux σ (i.arity :: τ) (args i)
              inst.aux q.arity (Renaming.weakenList Δ τ) new_args [] (σ q)
termination_by (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by
  all_goals exact Expr.Subterm.of_arg _ _ _ _ _

@[simp] private theorem lift_aux_ext_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) (α_h : C.Arity)
    (h : (tauSlot Γ τ_above β τ_below i).arity = α_h)
    (args : (j : C.Binder α_h) →
      Expr (Γ ⋈* (τ_above ++ β :: τ_below) ⋈ j.arity)) :
    lift.aux σ (τ_above ++ β :: τ_below)
      (Expr.apply' (tauSlot Γ τ_above β τ_below i) α_h h args)
      =
    Expr.apply' (tauSlot Δ τ_above β τ_below i) α_h
      ((tauSlot_arity Δ τ_above β τ_below i).trans
        ((tauSlot_arity Γ τ_above β τ_below i).symm.trans h))
      (fun j => lift.aux σ (j.arity :: (τ_above ++ β :: τ_below)) (args j)) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ_above ++ β :: τ_below,
        Expr.apply' (tauSlot Γ τ_above β τ_below i) α_h h args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_tauSlot]

@[simp] private theorem lift_aux_base_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (q : Slot Γ)
    (h : ((Renaming.weakenList Γ τ).toFun q).arity = q.arity)
    (args : (j : C.Binder q.arity) → Expr (Γ ⋈* τ ⋈ j.arity)) :
    lift.aux σ τ
      (Expr.apply' ((Renaming.weakenList Γ τ).toFun q) q.arity h args)
      =
    inst.aux q.arity (Renaming.weakenList Δ τ)
      (fun j => lift.aux σ (j.arity :: τ) (args j)) [] (σ q) := by
  delta lift.aux
  change lift.aux._unary (C := C) σ
      ⟨τ, Expr.apply' ((Renaming.weakenList Γ τ).toFun q) q.arity h args⟩ = _
  rw [lift.aux._unary.eq_1]
  simp [classify_weakenList]

private theorem lift_aux_η_tauSlot {C : Carrier} :
    ∀ {Γ Δ : Shape C} (σ : Subst Γ Δ)
      (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
      (i : C.Binder β),
      lift.aux σ (i.arity :: (τ_above ++ β :: τ_below))
        (Expr.η ⟨tauSlot Γ τ_above β τ_below i, tauSlot_arity Γ τ_above β τ_below i⟩)
        =
      Expr.η ⟨tauSlot Δ τ_above β τ_below i, tauSlot_arity Δ τ_above β τ_below i⟩
  | Γ, Δ, σ, τ_above, β, τ_below, i => by
    unfold Expr.η
    change lift.aux σ ((i.arity :: τ_above) ++ β :: τ_below)
        (Expr.apply' (tauSlot Γ (i.arity :: τ_above) β τ_below i)
          i.arity (tauSlot_arity Γ (i.arity :: τ_above) β τ_below i)
          (fun k =>
            Expr.η ⟨.here k, rfl⟩))
        =
      Expr.apply' (tauSlot Δ (i.arity :: τ_above) β τ_below i)
        i.arity (tauSlot_arity Δ (i.arity :: τ_above) β τ_below i)
        (fun k =>
          Expr.η ⟨.here k, rfl⟩)
    rw [lift_aux_ext_eq]
    congr 1
    funext k
    exact lift_aux_η_tauSlot σ [] i.arity (τ_above ++ β :: τ_below) k
termination_by _ _ _ _ _ _ i => i.arity
decreasing_by exact ⟨_, rfl⟩

private theorem unit_right.aux {C : Carrier} {Γ : Shape C} :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)), lift.aux (fun q => Expr.η ⟨q, rfl⟩) τ e = e
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h), lift.aux (fun q => Expr.η ⟨q, rfl⟩) (j.arity :: τ) (args j) = args j := by
      intro j
      exact unit_right.aux (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      rw [lift_aux_ext_eq]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      have hs : q.arity = α_h :=
        ((Renaming.weakenList Γ τ).arity q).symm.trans h
      cases hs
      rw [lift_aux_base_eq]
      change inst.aux q.arity (Renaming.weakenList Γ τ)
          (fun j => lift.aux (fun q => Expr.η ⟨q, rfl⟩) (j.arity :: τ) (args j)) [] (Expr.η ⟨q, rfl⟩)
        = Expr.apply' ((Renaming.weakenList Γ τ).toFun q) q.arity h args
      rw [inst_aux_η]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

private theorem unit_left.aux {C : Carrier} {Γ Δ : Shape C}
    (σ : Subst Γ Δ) :
    ∀ {α : C.Arity} (v : Expr.J Γ α),
      lift.aux σ [α] (Expr.η v)
        =
      (match v with | ⟨p, hp⟩ => match hp with | rfl => σ p)
  | α, ⟨p, hp⟩ => by
    cases hp
    unfold Expr.η
    change lift.aux σ [p.arity]
        (Expr.apply' ((Renaming.weakenList Γ [p.arity]).toFun p)
          p.arity rfl
          (fun i => Expr.η ⟨.here i, rfl⟩))
        = σ p
    rw [lift_aux_base_eq]
    change inst.aux p.arity (Renaming.weakenList Δ [p.arity])
        (fun i : C.Binder p.arity =>
          lift.aux σ (i.arity :: [p.arity])
            (Expr.η ⟨.here i, rfl⟩)) [] (σ p)
      = σ p
    have hargs : (fun i : C.Binder p.arity =>
          lift.aux σ (i.arity :: [p.arity])
            (Expr.η ⟨.here i, rfl⟩))
        = η_fillers Δ p.arity := by
      funext i
      unfold η_fillers
      exact lift_aux_η_tauSlot σ [] p.arity [] i
    rw [hargs]
    exact inst_aux_η_inv Δ p.arity [] (σ p)

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `ι`. -/
def inst {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (e : Expr (Δ ⋈ α)) (ι : Inst α Δ) : Expr Δ :=
  inst.aux α 𝟙ʳ ι [] e

/-- Kleisli extension at a single α-binder. -/
def Subst.lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

theorem unit_right {C : Carrier} {Γ : Shape C}
    (α : C.Arity) (e : Expr.T Γ α) :
    Subst.lift (fun q => Expr.η ⟨q, rfl⟩) e = e :=
  unit_right.aux [α] e

theorem unit_left {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ α : C.Arity, Expr.J Γ α → Expr.T Δ α) :
    ∀ {α : C.Arity} (v : Expr.J Γ α),
      f α v = Subst.lift (fun s => f s.arity ⟨s, rfl⟩) (Expr.η v)
  | _, ⟨p, hp⟩ => by
    cases hp
    symm
    exact unit_left.aux (fun s => f s.arity ⟨s, rfl⟩) ⟨p, rfl⟩

/-! ## Categorical operations: substitution and renaming compositions -/

/-- Embed a renaming as a substitution: send each slot through `ρ` and η-expand. -/
def Renaming.toSubst {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) : Subst Γ Δ :=
  fun p => Expr.η ⟨ρ p, ρ.arity p⟩

/-- Pre-compose a substitution by a renaming: `(ρ ʳ∘ˢ σ) p = σ (ρ p)` up to the
arity-preservation transport carried by `ρ`. -/
def Renaming.preSubst {C : Carrier} {Γ Γ' Δ : Shape C}
    (ρ : Γ →ʳ Γ') (σ : Subst Γ' Δ) : Subst Γ Δ :=
  fun p => (ρ.arity p) ▸ σ (ρ p)

@[inherit_doc Renaming.preSubst]
scoped infixl:90 " ʳ∘ˢ " => Renaming.preSubst

/-- Post-compose a substitution by a renaming: apply `σ`, then rename the result. -/
def Subst.postRen {C : Carrier} {Γ Δ Δ' : Shape C}
    (σ : Subst Γ Δ) (ρ : Δ →ʳ Δ') : Subst Γ Δ' :=
  fun p => ⟦ ρ ⇑ʳ p.arity ⟧ʳ (σ p)

@[inherit_doc Subst.postRen]
scoped infixl:90 " ˢ∘ʳ " => Subst.postRen

/-- Kleisli composition of substitutions: `(σ ˢ∘ˢ θ) p = Subst.lift θ (σ p)`. -/
def Subst.comp {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) : Subst Γ Ε :=
  fun p => Subst.lift θ (σ p)

@[inherit_doc Subst.comp]
scoped infixl:90 " ˢ∘ˢ " => Subst.comp

/-! ## Naturality lemma needed by `comp_lift` -/

/-- **L5** — naturality of `lift` past `inst`.  Walking
`inst.aux α (weakenList Δ τ) ι [] e` with `lift.aux θ τ` is the same as
instantiating with the `lift`ed instantiation data into the `lift`ed expression. -/
private theorem lift_inst_commute {C : Carrier} :
    ∀ {Δ Ε : Shape C} (θ : Subst Δ Ε) (α : C.Arity)
      (τ : List C.Arity) (ι : Inst α (Δ ⋈* τ)) (e : Expr (Δ ⋈ α)),
      lift.aux θ τ (inst.aux α (Renaming.weakenList Δ τ) ι [] e)
        =
      inst.aux α (Renaming.weakenList Ε τ)
        (fun j => lift.aux θ (j.arity :: τ) (ι j))
        [] (Subst.lift θ e) := by
  sorry

/-! ## Composition law -/

private theorem comp_lift.aux {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux (σ ˢ∘ˢ θ) τ e = lift.aux θ τ (lift.aux σ τ e)
  | τ, Expr.apply' p α_h h args => by
    have ih_arg : ∀ (j : C.Binder α_h),
        lift.aux (σ ˢ∘ˢ θ) (j.arity :: τ) (args j)
          = lift.aux θ (j.arity :: τ) (lift.aux σ (j.arity :: τ) (args j)) := by
      intro j
      exact comp_lift.aux σ θ (j.arity :: τ) (args j)
    cases classify τ p with
    | ext i =>
      simp only [lift_aux_ext_eq]
      congr 1
      funext j
      exact ih_arg j
    | base q =>
      have hs : q.arity = α_h :=
        ((Renaming.weakenList Γ τ).arity q).symm.trans h
      cases hs
      simp only [lift_aux_base_eq]
      rw [lift_inst_commute]
      congr 1
      funext j
      exact ih_arg j
termination_by τ e => (⟨Γ ⋈* τ, e⟩ : Σ Γ : Shape C, Expr Γ)
decreasing_by exact Expr.Subterm.of_arg p α_h h args j

/-- Composition of Kleisli extensions: substituting via σ then via θ equals substituting
via the composed substitution `σ ˢ∘ˢ θ`. -/
theorem comp_lift {C : Carrier} {Γ Δ Ε : Shape C}
    (σ : Subst Γ Δ) (θ : Subst Δ Ε) :
    ∀ {α : C.Arity} (e : Expr (Γ ⋈ α)),
      Subst.lift (fun q => Subst.lift θ (σ q)) e
        =
      Subst.lift θ (Subst.lift σ e) := by
  intro α e
  exact comp_lift.aux σ θ [α] e

end Action
