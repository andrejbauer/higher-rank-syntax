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
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → Slot (Γ ⋈* (τ_above ++ β :: τ_below))
  | [],        _, _, i => Slot.here i
  | _ :: rest, β, τ_below, i => Slot.there (tauSlot Γ rest β τ_below i)

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
           (Slot.there ((Renaming.weakenList Γ rest).toFun p)) = XPos.base p
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
           (Slot.there (tauSlot Γ rest β τ_below i))
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
                    (((Renaming.weakenList (Δ ⋈ α) τ).arity (Slot.there r)).symm.trans h_α_h))
              Expr.apply' ((Renaming.weakenList Ξ τ).toFun (ρ r)) α_h new_h new_args
          | .here j =>
              have hs : j.arity = α_h :=
                ((Renaming.weakenList (Δ ⋈ α) τ).arity (Slot.here j)).symm.trans h_α_h
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

/-! ## η-fillers and the weakening-inverse lemma (work in progress) -/

/-- Canonical η-fillers for an α-binder over a shape with α at the top.
At each binder position `i`, returns the η-expansion of the bound variable `.here i`. -/
def η_fillers {C : Carrier} (Δ : Shape C) (α : C.Arity) : Inst α (Δ ⋈ α) :=
  fun i => Expr.η (Δ ⋈ α) i.arity ⟨.here i, rfl⟩

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

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `ι`. -/
def inst {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (e : Expr (Δ ⋈ α)) (ι : Inst α Δ) : Expr Δ :=
  inst.aux α (Renaming.id Δ) ι [] e

/-- Kleisli extension at a single α-binder. -/
def lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (α : C.Arity) (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

end Action
