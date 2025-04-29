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

/-- The data for an algebra of a relative monad T over a functor J : A ⥤ E consists of
- A carrier object X in E ;
- A structure that, given an object ζ of A and a map f : Jζ ⟶ X in E, returns a map χf : Tζ ⟶ X ;

and satisfies the following rules :

- ∀ f : Jζ ⟶ X, f = (χf)∘(ηζ)  (unit_law)
- ∀ k : Jζ ⟶ Tξ, ∀ f : Jξ ⟶ X, (χf)∘k⁺ = χ((χf)∘k) (bind_law)
-/
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

  @[ext]
  structure RelativeAlgebra.hom (X Y : RelativeAlgebra T) where
    carrier_map : X.carrier ⟶ Y.carrier
    struct_commute : ∀ {ζ : A} (f : J.obj ζ ⟶ X.carrier),
      (X.struct f) ≫ carrier_map  = Y.struct (f ≫ carrier_map)

  /- Identity morphism for relative algebra. -/
  @[reducible]
  def RelativeAlgebra.homId (X : RelativeAlgebra T) :
    RelativeAlgebra.hom X X where
    carrier_map := 𝟙 X.carrier
    struct_commute {ζ} f := by simp

  /- Composition of relative algebra morphisms. -/
  @[reducible]
  def RelativeAlgebra.homComp {X Y Z : RelativeAlgebra T}
    (Φ : RelativeAlgebra.hom X Y) (Ψ : RelativeAlgebra.hom Y Z) :
    RelativeAlgebra.hom X Z  where
    carrier_map := Φ.carrier_map ≫ Ψ.carrier_map
    struct_commute {ζ} f := by
      rw[←Category.assoc, Φ.struct_commute, Ψ.struct_commute, Category.assoc]

 /- Category of relative algebras. -/
  instance RelativeAlgebra.instCategory : Category (RelativeAlgebra T) where
    Hom := RelativeAlgebra.hom
    id X := RelativeAlgebra.homId X
    comp Φ Ψ := RelativeAlgebra.homComp Φ Ψ
    id_comp {X Y} Ψ := by simp ; ext ; simp
    comp_id {X Y} Φ := by simp ; ext ; simp
    assoc {X Y Z W} Φ Ψ Ξ := by simp
end
