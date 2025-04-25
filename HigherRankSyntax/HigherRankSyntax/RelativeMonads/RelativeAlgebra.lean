import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Lean.Level
import Mathlib.CategoryTheory.Monad.Basic
import HigherRankSyntax.RelativeMonads.RelativeMonad

open CategoryTheory

section
universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable (T : RelativeMonad J)

  structure RelativeAlgebra where
    carrier : E
    struct : ∀ {ζ : A},
      (J.obj ζ ⟶ carrier) → (T.map ζ ⟶ carrier)
    unit_law : ∀ {ζ : A} (f : J.obj ζ ⟶ carrier),
      f = (T.η ζ)≫ (struct f)
    bind_law : ∀ {ζ ξ: A}
      (k : J.obj ζ ⟶ T.map ξ)
      (f : J.obj ξ ⟶ carrier),
      (T.lift k) ≫ (struct f) = struct (k ≫ (struct f))

  end


/- Relative alegbra morphisms and the resulting category.-/
section
universe u₁ u₂ v₁ v₂

  variable {A : Type u₁} [Category.{v₁} A]
  variable {E : Type u₂} [Category.{v₂} E]
  variable {J : A ⥤ E}
  variable {T : RelativeMonad J}


  structure RelativeAlgebraHom (X Y : RelativeAlgebra T) where
    carrier_map : X.carrier ⟶ Y.carrier
    struct_commute : ∀ {ζ : A} (f : J.obj ζ ⟶ X.carrier),
      (X.struct f) ≫ carrier_map  = Y.struct (f ≫ carrier_map)

  /- Identity morphism for relative algebra. -/
  def RelativeAlgebraHomId (X : RelativeAlgebra T) :
    RelativeAlgebraHom X X where
    carrier_map := 𝟙 X.carrier
    struct_commute {ζ} f := by aesop_cat

  /- Composition of relative algebra morphisms. -/
  def RelativeAlgebraHomComp {X Y Z : RelativeAlgebra T}
    (Φ : RelativeAlgebraHom X Y) (Ψ : RelativeAlgebraHom Y Z) :
    RelativeAlgebraHom X Z  where
    carrier_map := Φ.carrier_map ≫ Ψ.carrier_map
    struct_commute {ζ} f := by
      rw[<-Category.assoc, Φ.struct_commute, Ψ.struct_commute, Category.assoc]

 /- Category of relative algebras. -/
  instance RelativeAlgebraCategory : Category (RelativeAlgebra T) where
    Hom := RelativeAlgebraHom
    id X := RelativeAlgebraHomId X
    comp Φ Ψ := RelativeAlgebraHomComp Φ Ψ
    id_comp {X Y} Ψ := by
      simp
      unfold RelativeAlgebraHomComp
      congr
      unfold RelativeAlgebraHomId
      simp
    comp_id {X Y} Φ := by
      simp
      unfold RelativeAlgebraHomComp
      congr
      unfold RelativeAlgebraHomId
      simp
    assoc {X Y Z W} Φ Ψ Ξ := by
      simp
      unfold RelativeAlgebraHomComp
      simp
end

/- Add proofs that :
  - χ is natural
  - We can define an identity map for relative algebras
  - We can define composition for these maps
  - We can form a category with these algebras and morphisms

-/
