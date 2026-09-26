import HigherRankSyntax.RelativeMonad.Basic

/-!
# The Kleisli category of a relative monad

For a relative monad `T` on `J : A ⥤ E`, a Kleisli morphism from `X` to `Y`
is a morphism `J.obj X ⟶ T.map Y`.  The identity at `X` is `T.η X`, and the
composite of `f` and `g` is `f ≫ T.lift g`.
-/

universe u₁ u₂ v₁ v₂

open CategoryTheory

namespace RelativeMonad

variable {A : Type u₁} [Category.{v₁} A]
  {E : Type u₂} [Category.{v₂} E]
  {J : A ⥤ E}

/-- The objects of the Kleisli category of `T`: the objects of `A`. -/
def Kleisli (_T : RelativeMonad J) := A

namespace Kleisli

variable (T : RelativeMonad J)

/-- `X : A` as an object of `Kleisli T`. -/
def of (X : A) : Kleisli T := X

/-- The object of `A` underlying `X : Kleisli T`. -/
def toBase (X : Kleisli T) : A := X

@[simp]
theorem toBase_of (X : A) :
  toBase T (of T X) = X
  := rfl

@[simp]
theorem of_toBase (X : Kleisli T) :
  of T (toBase T X) = X
  := rfl

instance : Category.{v₂} (Kleisli T) where
  Hom X Y := J.obj (toBase T X) ⟶ T.map (toBase T Y)
  id X := T.η (toBase T X)
  comp f g := f ≫ T.lift g
  id_comp f := by
    symm
    apply T.unit_left
  comp_id f := by
    rw [T.unit_right, Category.comp_id]
  assoc f g h := by
    rw [T.comp_lift, Category.assoc]

/-- Kleisli morphisms `of T X ⟶ of T Y` are the morphisms `J.obj X ⟶ T.map Y`. -/
def homEquiv (X Y : A) :
    (of T X ⟶ of T Y) ≃ (J.obj X ⟶ T.map Y) :=
  Equiv.refl _

@[simp]
theorem id_eq (X : A) :
  (𝟙 (of T X) : of T X ⟶ of T X) = T.η X
  := rfl

@[simp]
theorem comp_eq
    {X Y Z : A}
    (f : J.obj X ⟶ T.map Y) (g : J.obj Y ⟶ T.map Z) :
  (homEquiv T X Z) (f ≫ g) = f ≫ T.lift g
  := rfl

end Kleisli

namespace Hom

variable {T T' : RelativeMonad J}

/-- Postcomposition of `f : J.obj X ⟶ T.map Y` with `F.map_hom`. -/
private def kleisliMap (F : Hom T T')
    {X Y : A} (f : J.obj X ⟶ T.map Y) : J.obj X ⟶ T'.map Y :=
  f ≫ F.map_hom

private theorem kleisliMap_id (F : Hom T T') (X : A) :
  kleisliMap F (T.η X) = T'.η X
  := F.hom_unit

private theorem kleisliMap_comp
    (F : Hom T T')
    {X Y Z : A} (f : J.obj X ⟶ T.map Y) (g : J.obj Y ⟶ T.map Z) :
  kleisliMap F (f ≫ T.lift g) = kleisliMap F f ≫ T'.lift (kleisliMap F g)
  := by
  simp only [kleisliMap, Category.assoc, F.hom_lift]

/-- The identity-on-objects functor `Kleisli T ⥤ Kleisli T'` sending `f` to
`f ≫ F.map_hom`. -/
def kleisliFunctor (F : Hom T T') : Kleisli T ⥤ Kleisli T' where
  obj X := Kleisli.of T' (Kleisli.toBase T X)
  map f := kleisliMap F f
  map_id X := kleisliMap_id F (Kleisli.toBase T X)
  map_comp f g := kleisliMap_comp F f g

end Hom

end RelativeMonad
