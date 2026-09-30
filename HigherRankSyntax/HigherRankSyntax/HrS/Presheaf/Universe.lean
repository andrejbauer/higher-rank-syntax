import Mathlib.Data.ULift
import HigherRankSyntax.HrS.Presheaf.Basic

/-!
# The universe of sorts

The presheaves of maps into an object; the presheaf of sorts, whose elements at `I`
are the dependent presheaves over the maps into `I` with elements in `Type v`; the
sorts over a presheaf; and the elements of a sort.
-/

universe v

open CategoryTheory

namespace HrS

namespace Presheaf

variable {𝒞 : Type v} [SmallCategory 𝒞]

/-- The presheaf of maps into `I`. -/
def representable (I : 𝒞) : Presheaf.{v, v} 𝒞 where
  obj J := J ⟶ I
  map f u := f ≫ u
  map_id u := Category.id_comp u
  map_comp f g u := Category.assoc g f u

/-- Composition with `f`, from the maps into `J` to the maps into `I`. -/
def representableMap {I J : 𝒞} (f : J ⟶ I) : Hom (representable J) (representable I) where
  app u := u ≫ f
  naturality g u := by
    symm
    apply Category.assoc

theorem representableMap_id (I : 𝒞) :
  representableMap (𝟙 I) = Hom.identity (representable I)
  := by
  apply Hom.ext
  intro J u
  apply Category.comp_id

theorem representableMap_comp {I J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J) :
  representableMap (g ≫ f) = (representableMap f).comp (representableMap g)
  := by
  apply Hom.ext
  intro L u
  symm
  apply Category.assoc

variable (𝒞) in
/-- The presheaf of sorts: at `I`, the dependent presheaves over the maps into `I`
with elements in `Type v`. -/
def sorts : Presheaf.{v, v + 1} 𝒞 where
  obj I := DependentPresheaf.{v, v, v} (representable I)
  map f X := X.subst (representableMap f)
  map_id X := by
    rw [representableMap_id]
    apply DependentPresheaf.subst_identity
  map_comp f g X := by
    rw [representableMap_comp]
    apply DependentPresheaf.subst_comp

variable {Γ Δ : Presheaf.{v, v + 1} 𝒞}

/-- The sorts, over every element of `Γ`. -/
def U (Γ : Presheaf.{v, v + 1} 𝒞) : DependentPresheaf.{v, v + 1, v + 1} Γ where
  fiber I _ := (sorts 𝒞).obj I
  restrict := fun {_ _} f {_ _} _ X => (sorts 𝒞).map f X
  restrict_id _ X := (sorts 𝒞).map_id X
  restrict_comp := fun {_ _ _} f g {_ _ _} _ _ _ X => by
    symm
    apply (sorts 𝒞).map_comp

theorem U_subst (σ : Hom Δ Γ) :
  (U Γ).subst σ = U Δ
  := rfl

/-- The elements of the sort `S`: over `γ`, the elements of `S.app γ` over the
identity. -/
def El (S : (U Γ).Section) : DependentPresheaf.{v, v + 1, v + 1} Γ where
  fiber I γ := ULift.{v + 1} ((S.app γ).fiber I (𝟙 I))
  restrict := fun {_ J} f {γ _} h u =>
    ULift.up (cast (congrArg (fun X => DependentPresheaf.fiber X J (𝟙 J)) (S.naturality f h))
      ((S.app γ).restrict f (γ' := 𝟙 J ≫ f)
        (by simp only [representable, Category.comp_id, Category.id_comp]) u.down))
  restrict_id := fun {_ _} _ u => by
    apply ULift.ext
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    apply HEq.trans ((S.app _).restrict_heq rfl _ (Category.id_comp (𝟙 _)) u.down)
    apply heq_of_eq
    apply (S.app _).restrict_id
  restrict_comp := fun {_ _ _} f g {γ _ _} h _ _ u => by
    apply ULift.ext
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    apply HEq.trans _ (HEq.symm (cast_heq _ _))
    apply HEq.trans (DependentPresheaf.restrict_cast (S.naturality f h) g _ _)
    apply HEq.trans (heq_of_eq ((S.app γ).restrict_comp f g _ _
      (by simp only [representable, representableMap, Category.comp_id, Category.id_comp])
      u.down))
    apply (S.app γ).restrict_heq rfl

theorem El_subst (S : (U Γ).Section) (σ : Hom Δ Γ) :
  (El S).subst σ = El (S.subst σ)
  := rfl

end Presheaf

end HrS
