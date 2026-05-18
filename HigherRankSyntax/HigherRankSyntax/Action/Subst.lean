import HigherRankSyntax.Action.Expr

/-!
# Substitution, instantiation, and the Kleisli extension

Each head slot is classified by `classify` into either a Γ-slot (`XPos.base`, the
weakening of some `s : Slot Γ` through τ) or a τ-binder (`XPos.ext`, identified by a
split of τ as `τ_above ++ β :: τ_below` with a binder position `z` of `β`).  The
slot-correspondence witness lives in the inductive's index, so pattern matching on
`classify`'s result yields it definitionally — no `Eq.rec`.

`lift.aux` walks `Expr (Γ ⋈* τ)`; the Γ-slot case substitutes via σ and folds the
τ-stack into σ's image via `inst.aux`.  `inst.aux` walks `Expr ((Δ ⋈ α) ⋈* τ)`, with
the α-binder case producing the recursive smaller-arity call.
-/

namespace Action

/-! ## Substitutions and instantiations -/

/-- A substitution from `Γ` to `Δ`. -/
abbrev Subst {C : Carrier} (Γ Δ : Shape C) : Type :=
  (s : Slot Γ) → Expr (Δ ⋈ s.arity)

/-- An instantiation of an α-binder above `Γ`. -/
abbrev Inst {C : Carrier} (α : C.Arity) (Γ : Shape C) : Type :=
  (z : C.AritySlot α) → Expr (Γ ⋈ C.arityArity α z)

/-! ## Slot classification -/

/-- The slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)` corresponding to
binder position `z` of `β`.  Iterates `.there` over `τ_above` from `.here z`. -/
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (z : C.AritySlot β) → Slot (Γ ⋈* (τ_above ++ β :: τ_below))
  | [],        _, _, z => Slot.here z
  | _ :: rest, β, τ_below, z => Slot.there (tauSlot Γ rest β τ_below z)

/-- A `tauSlot`'s arity is the binder's sub-arity. -/
theorem tauSlot_arity {C : Carrier} (Γ : Shape C)
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (z : C.AritySlot β) : (tauSlot Γ τ_above β τ_below z).arity = C.arityArity β z := by
  induction τ_above with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Position of a slot in `Γ ⋈* τ`: a Γ-slot weakened through τ, or a τ-binder. -/
inductive XPos {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → Slot (Γ ⋈* τ) → Type where
  | base : ∀ {τ : List C.Arity}, (s : Slot Γ) →
           XPos Γ τ (Renaming.weakenList Γ τ s)
  | ext  : ∀ {τ_above : List C.Arity} {β : C.Arity} {τ_below : List C.Arity},
           (z : C.AritySlot β) →
           XPos Γ (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below z)

/-- Classify a slot in an iterated extension. -/
def classify {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → (x : Slot (Γ ⋈* τ)) → XPos Γ τ x
  | [],       x        => XPos.base x
  | _ :: _,   .here z  => XPos.ext (τ_above := []) z
  | β :: τ',  .there s =>
      match classify τ' s with
      | XPos.base s' => XPos.base s'
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) z' =>
          XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) z'

/-! ## Walkers -/

/-- α-instantiation walker.  Walks `e : Expr ((Δ ⋈ α) ⋈* τ)` by classifying each head:
τ-binder rebuilds the same `tauSlot` at the Δ-side; Δ-slot rebuilds with the appropriate
weakening; α-binder plugs `i z` (weakened through τ) and recurses at smaller arity. -/
def inst.aux {C : Carrier} {Δ : Shape C} (α : C.Arity) (i : Inst α Δ)
    (τ : List C.Arity) (e : Expr ((Δ ⋈ α) ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match e with
  | .apply' y α_h h_α_h args =>
      match classify τ y with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) z =>
          let new_args : (w : C.AritySlot α_h) →
              Expr ((Δ ⋈* (ta ++ b :: tb)) ⋈ C.arityArity α_h w) :=
            fun w => inst.aux α i (C.arityArity α_h w :: (ta ++ b :: tb)) (args w)
          have new_h : (tauSlot Δ ta b tb z).arity = α_h :=
            (tauSlot_arity Δ ta b tb z).trans
              ((tauSlot_arity (Δ ⋈ α) ta b tb z).symm.trans h_α_h)
          Expr.apply' (tauSlot Δ ta b tb z) α_h new_h new_args
      | XPos.base s =>
          match s with
          | .there s' =>
              let new_args : (w : C.AritySlot α_h) →
                  Expr ((Δ ⋈* τ) ⋈ C.arityArity α_h w) :=
                fun w => inst.aux α i (C.arityArity α_h w :: τ) (args w)
              have new_h : ((Renaming.weakenList Δ τ).toFun s').arity = α_h :=
                ((Renaming.weakenList Δ τ).arity s').trans
                  (((Renaming.weakenList (Δ ⋈ α) τ).arity (Slot.there s')).symm.trans h_α_h)
              Expr.apply' ((Renaming.weakenList Δ τ).toFun s') α_h new_h new_args
          | .here z' =>
              have hs : C.arityArity α z' = α_h :=
                ((Renaming.weakenList (Δ ⋈ α) τ).arity (Slot.here z')).symm.trans h_α_h
              match hs with
              | rfl =>
                  let new_args : (w : C.AritySlot (C.arityArity α z')) →
                      Expr ((Δ ⋈* τ) ⋈ C.arityArity (C.arityArity α z') w) :=
                    fun w => inst.aux α i (C.arityArity (C.arityArity α z') w :: τ) (args w)
                  let weakened_iz :=
                    ⟦ (Renaming.weakenList Δ τ) ⇑ʳ (C.arityArity α z') ⟧ʳ (i z')
                  inst.aux (C.arityArity α z') new_args [] weakened_iz
termination_by sizeOf e
decreasing_by all_goals sorry

/-- Kleisli extension walker.  Walks `e : Expr (Γ ⋈* τ)` by classifying each head:
τ-binder rebuilds; Γ-slot substitutes via σ and folds the τ-stack into σ's image. -/
def lift.aux {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (τ : List C.Arity) (e : Expr (Γ ⋈* τ)) : Expr (Δ ⋈* τ) :=
  match e with
  | .apply' y α_h h_α_h args =>
      match classify τ y with
      | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) z =>
          let new_args : (w : C.AritySlot α_h) →
              Expr ((Δ ⋈* (ta ++ b :: tb)) ⋈ C.arityArity α_h w) :=
            fun w => lift.aux σ (C.arityArity α_h w :: (ta ++ b :: tb)) (args w)
          have new_h : (tauSlot Δ ta b tb z).arity = α_h :=
            (tauSlot_arity Δ ta b tb z).trans
              ((tauSlot_arity Γ ta b tb z).symm.trans h_α_h)
          Expr.apply' (tauSlot Δ ta b tb z) α_h new_h new_args
      | XPos.base s =>
          have hs : s.arity = α_h :=
            ((Renaming.weakenList Γ τ).arity s).symm.trans h_α_h
          match hs with
          | rfl =>
              let new_args : (w : C.AritySlot s.arity) →
                  Expr ((Δ ⋈* τ) ⋈ C.arityArity s.arity w) :=
                fun w => lift.aux σ (C.arityArity s.arity w :: τ) (args w)
              let weakened_σ_s :=
                ⟦ (Renaming.weakenList Δ τ) ⇑ʳ s.arity ⟧ʳ (σ s)
              inst.aux s.arity new_args [] weakened_σ_s
termination_by sizeOf e
decreasing_by all_goals sorry

/-! ## Public wrappers -/

/-- α-instantiation: replace the α-binder of `Δ ⋈ α` by `i`. -/
def inst {C : Carrier} {α : C.Arity} {Δ : Shape C}
    (e : Expr (Δ ⋈ α)) (i : Inst α Δ) : Expr Δ :=
  inst.aux α i [] e

/-- Kleisli extension at a single α-binder. -/
def lift {C : Carrier} {Γ Δ : Shape C} (σ : Subst Γ Δ)
    (α : C.Arity) (e : Expr (Γ ⋈ α)) : Expr (Δ ⋈ α) :=
  lift.aux σ [α] e

end Action
