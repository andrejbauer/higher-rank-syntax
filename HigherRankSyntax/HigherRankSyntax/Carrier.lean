
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Submonoid.Basic

/-- A carrier of a higher-rank binding syntax: the base data from which the framework
builds expressions, renamings, and substitutions. -/
structure Carrier (A : Type) where
  /-- Arities: the binding shape carried by each position. -/
  Arity : Submonoid (Function.End A)
  /-- The positions of an arity. -/
  slotAt : Arity → Arity → Type
  elim : ∀ {Γ} , slotAt Γ 1 → ⊥
  inl : ∀ {Γ Δ α} , slotAt Γ α → slotAt (Γ * Δ) α
  inr : ∀ {Γ Δ α} , slotAt Δ α → slotAt (Γ * Δ) α
  copair : ∀ (Γ Δ) {α} , (X : Type) → slotAt (Γ * Δ) α →
    (slotAt Γ α → X) → (slotAt Δ α → X) → X
  copair_inl : ∀ (Γ Δ : Arity) {α : Arity} (X : Type) (x : slotAt Δ α)
                   (f : slotAt Γ α → X) (g : slotAt Δ α → X),
                   copair Γ Δ X (inr x) f g = g x
  copair_inr : ∀ (Γ Δ : Arity) {α : Arity} (X : Type) (x : slotAt Γ α)
                   (f : slotAt Γ α → X) (g : slotAt Δ α → X),
                   copair Γ Δ X (inl x) f g = f x
  /-- Cover: every slot of a product comes from the right or left injection. -/
  cover : ∀ (Γ Δ : Arity) {α : Arity} (p : slotAt (Γ * Δ) α),
    (∃ x : slotAt Δ α, p = inr x) ∨ (∃ y : slotAt Γ α, p = inl y)
  subWf : WellFounded (fun Δ Γ => Nonempty (slotAt Γ Δ))


/-- One-step sub-arity relation: `α' ≺ α` when `α'` is the sub-arity of some position of
`α`.  Well-founded by `subWf`. -/
abbrev Carrier.Sub {A : Type} {C : Carrier A} (Δ Γ : C.Arity) : Prop :=
  Nonempty (C.slotAt Γ Δ)

/-- The carrier's sub-arity well-founded relation, packaged as a `WellFoundedRelation`
instance for use in `termination_by`. -/
instance {A : Type} (C : Carrier A) : WellFoundedRelation (C.Arity) where
  rel := Carrier.Sub
  wf := C.subWf

abbrev SlotAt {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : Type :=
  C.slotAt Γ Δ

infix:35 " ∋ " => SlotAt

abbrev Ext {A : Type} {C : Carrier A} (Γ Δ : C.Arity) : C.Arity := Γ * Δ

infixl:65 " ⋈ " => Ext
