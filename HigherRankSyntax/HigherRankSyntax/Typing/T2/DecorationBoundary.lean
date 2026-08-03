import HigherRankSyntax.Typing.Decoration

/-!
# Boundaries of decorated slots

A slot boundary consists of its decorated preceding telescope, decorated
binding arity, and classifier.
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
