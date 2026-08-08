import HigherRankSyntax.Typing.Decoration

/-!
# Archived T2 boundary extraction

This file records the first boundary operation anticipated by the future T2
judgment layer.  Given a slot in a decorated telescope, its boundary consists
of the decorated prefix before that slot, its decorated binding arity, and its
raw classifier.  In `A : Type, x : A`, the boundary of `x` therefore contains
the prefix `A : Type`, an empty binding telescope, and the classifier expression
that names `A`.

The construction extracts data already present in a T1 decoration.  It does not
say that the prefix is a well-formed context, that the classifier is a
well-formed type, or that the slot inhabits it.  Those judgments are precisely
what T2 must add later.  The file is archived outside the root import graph so
the completed decoration-module-monoid story remains conceptually independent
of that future layer.
-/

variable {A : Type} {C : Carrier A}

namespace Precedence

variable [P : Precedence C]

/-- The inclusion of the part of an arity preceding a slot. -/
def inclusion {Δ α : C.Arity} {τ : C.Ty} (x : Δ ∋[τ] α) :
    P.before x →ʳ Δ :=
  fun ⦃_⦄ ⦃_⦄ y => P.factor x ▸ C.inl y

end Precedence

namespace Decoration

variable [P : Precedence C] {bd : C.Ty → Option C.Ty}

private def castArity {Ω Γ Δ : C.Arity} (h : Γ = Δ) :
    Decoration bd Ω Γ → Decoration bd Ω Δ :=
  h ▸ fun D => D

private def restrictLeft {Ω Γ Δ : C.Arity}
    (D : Decoration bd Ω (Γ ⋈ Δ)) : Decoration bd Ω Γ := by
  intro Φ α τ p
  cases p with
  | here x =>
      exact ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (P.before_inl x))
        (D (.here (C.inl x)))
  | nested x p =>
      exact ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ _) ⋈ α) (P.before_inl x))
        (D (.nested (C.inl x) p))

/-- Restrict a decoration to the part of its arity preceding a slot. -/
def preceding {Ω Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (x : Δ ∋[τ] α) :
    Decoration bd Ω (P.before x) :=
  restrictLeft (castArity (P.factor x).symm D)

end Decoration

/-- The decorated prefix, binding arity, and classifier of a slot. -/
structure SlotBoundary [Precedence C] (bd : C.Ty → Option C.Ty)
    (Ω : C.Arity) (τ : C.Ty) where
  preceding : DecoratedTelescope bd Ω
  binding : DecoratedTelescope bd (Ω ⋈ preceding.arity)
  classifier : ClassifierAt bd
    (Ω ⋈ preceding.arity ⋈ binding.arity) τ

namespace DecoratedTelescope

variable [P : Precedence C] {bd : C.Ty → Option C.Ty} {Ω : C.Arity}

/-- Restrict a decorated telescope to the part preceding a slot. -/
def preceding (Δ : DecoratedTelescope bd Ω)
    {α : C.Arity} {τ : C.Ty} (x : Δ.arity ∋[τ] α) :
    DecoratedTelescope bd Ω where
  arity := P.before x
  decoration := Decoration.preceding Δ.decoration x

/-- The decorated boundary carried by a slot of a decorated telescope. -/
def boundary (Δ : DecoratedTelescope bd Ω)
    {α : C.Arity} {τ : C.Ty} (x : Δ.arity ∋[τ] α) :
    SlotBoundary bd Ω τ where
  preceding := preceding Δ x
  binding := ⟨α, Decoration.nested Δ.decoration x⟩
  classifier := Decoration.classifier Δ.decoration x

end DecoratedTelescope
