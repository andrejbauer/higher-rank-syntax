import HigherRankSyntax.Action.Expr

/-!
# Substitution, instantiation, and the Kleisli extension — definitions

The substitution machinery: slot classification, the walkers `inst.aux` and
`lift.aux`, their per-case unfolders, the public wrappers `inst` and
`Subst.lift`, and the categorical operations (`Renaming.toSubst`,
`Renaming.preSubst`, `Subst.postRen`, `Subst.comp`).

Each head slot is classified by `classify` into either a Γ-slot (`XPos.base`, the
weakening of some `p : Slot Γ` through τ) or a τ-binder (`XPos.ext`, identified by a
split of τ as `τ_above ++ β :: τ_below` with a binder `i` of `β`).  The
slot-correspondence witness lives in the inductive's index, so pattern matching on
`classify`'s result yields it definitionally — no `Eq.rec`.

`lift.aux` walks `Expr (Γ ⋈* τ)`; the Γ-slot case substitutes via σ and uses
`inst.aux` directly on σ's image, threading the target weakening as a renaming.
`inst.aux` walks `Expr ((Δ ⋈ α) ⋈* τ)`, carries a renaming `ρ : Δ →ʳ Ξ`, and
maps Δ-slots through `ρ` during traversal.

Equational theorems about these walkers — the η-laws, the relative-monad laws
(`unit_right`, `unit_left`, `comp_lift`), and the categorical embedding `L3` —
live in `Action/Equations.lean`.
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
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → Slot (Γ ⋈* (τ_above ++ β :: τ_below))
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- A `tauSlot`'s arity is the binder's sub-arity. -/
theorem tauSlot_arity {C : Carrier} (Γ : Shape C)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) : (tauSlot Γ τ_above β τ_below i).arity = i.arity := by
  induction τ_above with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Position of a slot in `Γ ⋈* τ`: a Γ-slot weakened through τ, or a τ-binder. -/
inductive XPos {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Slot (Γ ⋈* τ) → Type where
  | base : ∀ {τ : List C.Arity}, (p : Slot Γ) →
           XPos Γ τ (Renaming.weakenList Γ τ p)
  | ext  : ∀ {τ_above : List C.Arity} {β : C.Arity} {τ_below : List C.Arity},
           (i : C.Binder β) →
           XPos Γ (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)

/-- Classify a slot in an iterated extension. -/
def classify {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → (p : Slot (Γ ⋈* τ)) → XPos Γ τ p
  | [],       p        => XPos.base p
  | _ :: _,   .here i  => XPos.ext (τ_above := []) i
  | β :: τ',  .there p =>
      match classify τ' p with
      | XPos.base q => XPos.base q
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) j =>
          XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) j

/-- Classifying a Γ-slot weakened through τ recovers the original Γ-slot. -/
@[simp] theorem classify_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) (p : Slot Γ) :
    classify τ ((Renaming.weakenList Γ τ).toFun p) = XPos.base p := by
  induction τ with
  | nil => rfl
  | cons β rest ih =>
    show classify (β :: rest)
           (.there ((Renaming.weakenList Γ rest).toFun p)) = XPos.base p
    simp [classify, ih]

/-- Classifying a `tauSlot` recovers the corresponding `XPos.ext`. -/
@[simp] theorem classify_tauSlot {C : Carrier} {Γ : Shape C}
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
def inst.aux {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
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

/-! ## η-fillers and per-case unfolders for `inst.aux` -/

/-- Canonical η-fillers for an α-binder over a shape with α at the top.
At each binder position `i`, returns the η-expansion of the bound variable `.here i`. -/
def η_fillers {C : Carrier} (Δ : Shape C) (α : C.Arity) : Inst α (Δ ⋈ α) :=
  fun i => Expr.η ⟨.here i, rfl⟩

@[simp] theorem inst_aux_ext_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
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

@[simp] theorem inst_aux_base_there_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
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

@[simp] theorem inst_aux_base_here_eq {C : Carrier} {Δ Ξ : Shape C} (α : C.Arity)
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

/-- Kleisli extension walker.  Walks `e : Expr (Γ ⋈* τ)` by classifying each head:
τ-binder rebuilds; Γ-slot substitutes via σ and threads the target weakening through
`inst.aux`. -/
def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
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

@[simp] theorem lift_aux_ext_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
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

@[simp] theorem lift_aux_base_eq {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
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

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `ι`. -/
def inst {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (e : Expr (Δ ⋈ α)) (ι : Inst α Δ) : Expr Δ :=
  inst.aux α 𝟙ʳ ι [] e

/-- Kleisli extension at a single α-binder. -/
def Subst.lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    {α : C.Arity} (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

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

end Action
