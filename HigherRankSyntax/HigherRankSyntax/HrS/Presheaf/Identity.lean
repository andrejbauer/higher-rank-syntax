import Mathlib.Data.ULift
import Mathlib.Logic.Function.ULift
import HigherRankSyntax.HrS.Presheaf.Basic

/-!
# Equality of sections

For sections `s`, `t` of a dependent presheaf, the dependent presheaf `Equality s t`
whose elements over `γ` are the proofs of `s.app γ = t.app γ`. It has a section
exactly when `s = t`, any two of its sections are equal, and it commutes with
reindexing.
-/

universe v w w'

open CategoryTheory

namespace HrS

namespace DependentPresheaf

variable {𝒞 : Type v} [SmallCategory 𝒞] {Γ Δ : Presheaf.{v, w} 𝒞}
  {a : DependentPresheaf.{v, w, w'} Γ}

/-- The proofs that `s` and `t` agree over `γ`. -/
def Equality (s t : a.Section) : DependentPresheaf.{v, w, w'} Γ where
  fiber _ γ := ULift.{w'} (PLift (s.app γ = t.app γ))
  restrict := fun {_ _} f {_ _} h p =>
    ⟨⟨by rw [← s.naturality f h, ← t.naturality f h, p.down.down]⟩⟩
  restrict_id _ _ := rfl
  restrict_comp := fun {_ _ _} _ _ {_ _ _} _ _ _ _ => rfl

namespace Equality

/-- `s` agrees with itself over every element. -/
def refl (s : a.Section) : (Equality s s).Section where
  app _ := ⟨⟨rfl⟩⟩
  naturality := fun {_ _} _ {_ _} _ => rfl

/-- Any two sections of `Equality s t` are equal. -/
theorem irrelevant {s t : a.Section} (p q : (Equality s t).Section) :
  p = q
  := by
  apply Section.ext
  intro I γ
  apply ULift.ext
  apply PLift.down_injective
  rfl

/-- A section of `Equality s t` gives `s = t`. -/
theorem reflect {s t : a.Section} (p : (Equality s t).Section) :
  s = t
  := by
  apply Section.ext
  intro I γ
  apply (p.app γ).down.down

end Equality

theorem Equality_subst (s t : a.Section) (σ : Presheaf.Hom Δ Γ) :
  (Equality s t).subst σ = Equality (s.subst σ) (t.subst σ)
  := rfl

end DependentPresheaf

end HrS
