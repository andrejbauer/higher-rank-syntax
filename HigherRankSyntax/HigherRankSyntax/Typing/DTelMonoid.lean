import HigherRankSyntax.Typing.DecoratedTelescope
import HigherRankSyntax.Typing.TelescopeTensor

/-!
# Decorated telescopes as an internal monoid

The generic decorated-telescope module is an arity-shaped syntax module.  Its
empty telescope and dependent concatenation are the unit and multiplication
of a monoid object for the context-extension tensor on `ArityMod`.
-/

open CategoryTheory
open MonoidalCategory

variable {A : Type} {C : Carrier A}

namespace ArityMod

variable [Precedence C] (bd : C.Ty → Option C.Ty)

private def dtelShape : DTel (C := C) bd ⟶ arityConst C where
  app _ := ↾DecoratedTelescope.arity
  naturality := by
    intros
    rfl

/-- Decorated telescopes, equipped with their substitution-invariant raw
shape, as an object of `ArityMod`. -/
def DTelArityMod : ArityMod C := Over.mk (dtelShape bd)

@[simp]
theorem DTelArityMod_module : module (DTelArityMod bd) = DTel bd := rfl

@[simp]
theorem DTelArityMod_shape {Ω : C.Arity}
    (Γ : DecoratedTelescope bd Ω) :
    shape (DTelArityMod bd) Γ = Γ.arity := rfl

private def dtelUnitNat :
    module (tensorUnit (C := C)) ⟶ module (DTelArityMod bd) where
  app Ω := ↾fun _ => DecoratedTelescope.empty bd Ω
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    simp only [ConcreteCategory.comp_apply]
    change DecoratedTelescope.empty bd Ξ =
      DecoratedTelescope.act σ (DecoratedTelescope.empty bd Ω)
    exact (DecoratedTelescope.act_empty σ).symm

/-- The empty decorated telescope as a shape-preserving morphism. -/
def DTelOne : tensorUnit (C := C) ⟶ DTelArityMod bd :=
  Over.homMk (dtelUnitNat bd) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

private def dtelMulNat :
    module (tensorObj (DTelArityMod bd) (DTelArityMod bd)) ⟶
      module (DTelArityMod bd) where
  app _ := ↾fun ⟨Γ, Δ⟩ => DecoratedTelescope.concatenate Γ Δ
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    simp only [ConcreteCategory.comp_apply]
    change
      DecoratedTelescope.concatenate
          (DecoratedTelescope.act σ Γ)
          (DecoratedTelescope.act (Subst.lift σ Γ.arity) Δ) =
        DecoratedTelescope.act σ
          (DecoratedTelescope.concatenate Γ Δ)
    exact (DecoratedTelescope.act_concatenate σ Γ Δ).symm

/-- Dependent concatenation as a shape-preserving morphism. -/
def DTelMul :
    tensorObj (DTelArityMod bd) (DTelArityMod bd) ⟶ DTelArityMod bd :=
  Over.homMk (dtelMulNat bd) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    rfl)

private theorem dtel_one_mul :
    tensorMap (DTelOne bd) (𝟙 (DTelArityMod bd)) ≫ DTelMul bd =
      (tensorLeftUnitor (DTelArityMod bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨u, Γ⟩
  cases u
  simp [DTelOne, DTelMul, dtelUnitNat, dtelMulNat, tensorMap,
    tensorLeftUnitor]
  exact DecoratedTelescope.concatenate_empty_left _

private theorem dtel_mul_one :
    tensorMap (𝟙 (DTelArityMod bd)) (DTelOne bd) ≫ DTelMul bd =
      (tensorRightUnitor (DTelArityMod bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, u⟩
  cases u
  simp [DTelOne, DTelMul, dtelUnitNat, dtelMulNat, tensorMap,
    tensorRightUnitor]
  apply DecoratedTelescope.concatenate_empty_right

private theorem dtel_mul_assoc :
    tensorMap (DTelMul bd) (𝟙 (DTelArityMod bd)) ≫ DTelMul bd =
      (tensorAssociator (DTelArityMod bd) (DTelArityMod bd)
          (DTelArityMod bd)).hom ≫
        tensorMap (𝟙 (DTelArityMod bd)) (DTelMul bd) ≫ DTelMul bd := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
  simp [DTelMul, dtelMulNat, tensorMap, tensorAssociator]
  apply DecoratedTelescope.concatenate_assoc

instance : MonObj (DTelArityMod bd) where
  one := DTelOne bd
  mul := DTelMul bd
  one_mul := dtel_one_mul bd
  mul_one := dtel_mul_one bd
  mul_assoc := dtel_mul_assoc bd

/-- Decorated telescopes form a monoid object in the monoidal category of
arity-shaped raw-syntax modules. -/
def DTelMon : CategoryTheory.Mon (ArityMod C) :=
  CategoryTheory.Mon.mk (DTelArityMod bd)

@[simp]
theorem DTelMon_one :
    MonObj.one (X := (DTelMon bd).X) = DTelOne bd := rfl

@[simp]
theorem DTelMon_mul :
    MonObj.mul (X := (DTelMon bd).X) = DTelMul bd := rfl

end ArityMod
