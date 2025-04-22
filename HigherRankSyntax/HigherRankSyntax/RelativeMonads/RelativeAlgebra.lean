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
    struct : ∀ {Z : A},
      (J.obj Z ⟶ carrier) → (T.map Z ⟶ carrier)
    unit_law : ∀ {Z : A} (f : J.obj Z ⟶ carrier),
      f = (T.η Z)≫ (struct f)
    bind_law : ∀ {Z W: A}
      (k : J.obj Z ⟶ T.map W)
      (f : J.obj W ⟶ carrier),
      (T.lift k) ≫ (struct f) = struct (k ≫ (struct f))

  structure RelativeAlgebraHom (X Y : RelativeAlgebra T) where
    carrier_map : X.carrier ⟶ Y.carrier
    struct_commute : ∀ {Z : A} (f : J.obj Z ⟶ X.carrier),
      (X.struct f) ≫ carrier_map  = Y.struct (f ≫ carrier_map)

  def RelativeAlgebraHomId (X : RelativeAlgebra T) :
    RelativeAlgebraHom T X X where
    carrier_map := 𝟙 X.carrier
    struct_commute {ζ} f := by aesop_cat

  def RelativeAlgebraHomComp {X Y Z : RelativeAlgebra T}
    (Φ : RelativeAlgebraHom T X Y) (Ψ : RelativeAlgebraHom T Y Z) :
    RelativeAlgebraHom T X Z  where
    carrier_map := Φ.carrier_map ≫ Ψ.carrier_map
    struct_commute {ζ} f := by
      rw[<-Category.assoc, Φ.struct_commute, Ψ.struct_commute, Category.assoc]


  instance RelativeAlgebraCategory : Category (RelativeAlgebra T) where
    Hom := RelativeAlgebraHom T
    id X := RelativeAlgebraHomId T X
    comp Φ Ψ := RelativeAlgebraHomComp T Φ Ψ
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
