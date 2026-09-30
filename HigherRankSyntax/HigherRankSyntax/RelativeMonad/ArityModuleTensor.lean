import Mathlib.CategoryTheory.Monoidal.Category
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.RelativeMonad.ArityModule

/-!
# The tensor product of arity modules

A `KleisliArityAction T` extends the Kleisli arrows of a relative monad `T` over `J` along
arities; `Subst.lift` is one for `SyntaxMonad`.

For arity modules `M` and `N`, an element of the tensor `M ⊗ N` at `Ω` is a pair of
`x : M(Ω)` and `y : N(Ω ⋈ shape x)`, of shape `shape x ⋈ shape y`; a Kleisli arrow `σ`
acts on `y` through the extension of `σ` along `shape x`.  With the one-element module
of shape `1` as unit, `ArityMod T` is a monoidal category.
-/

open CategoryTheory
open RelativeMonad (Kleisli)

/-- A right action of arities on the Kleisli category of `T`: every arrow
`σ : Γ ⟶ Δ` extends along `Φ` to `lift σ Φ : Γ ⋈ Φ ⟶ Δ ⋈ Φ`, functorially in `σ`, with
`lift σ 1 = σ` and `lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ`. -/
class KleisliArityAction (T : RelativeMonad J) where
  lift {Γ Δ : C.Arity} (σ : Kleisli.of T Γ ⟶ Kleisli.of T Δ) (Φ : C.Arity) :
    Kleisli.of T (Γ ⋈ Φ) ⟶ Kleisli.of T (Δ ⋈ Φ)
  lift_id (Γ Φ : C.Arity) : lift (𝟙 (Kleisli.of T Γ)) Φ = 𝟙 (Kleisli.of T (Γ ⋈ Φ))
  lift_comp {Γ Δ Ξ : C.Arity}
    (σ : Kleisli.of T Γ ⟶ Kleisli.of T Δ) (θ : Kleisli.of T Δ ⟶ Kleisli.of T Ξ)
    (Φ : C.Arity) : lift (σ ≫ θ) Φ = lift σ Φ ≫ lift θ Φ
  lift_one {Γ Δ : C.Arity} (σ : Kleisli.of T Γ ⟶ Kleisli.of T Δ) : lift σ 1 = σ
  lift_assoc {Γ Δ : C.Arity} (σ : Kleisli.of T Γ ⟶ Kleisli.of T Δ) (Φ Ψ : C.Arity) :
    lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ

namespace KleisliArityAction

variable {T : RelativeMonad J} [KleisliArityAction T]

/-- The endofunctor of the Kleisli category sending `Ω` to `Ω ⋈ Φ` and `σ` to
`lift σ Φ`. -/
def extendBy (Φ : C.Arity) : Kleisli T ⥤ Kleisli T where
  obj Ω := Ω ⋈ Φ
  map σ := lift σ Φ
  map_id Ω := lift_id Ω Φ
  map_comp σ θ := lift_comp σ θ Φ

/-- Extension by the unit arity is naturally isomorphic to the identity functor. -/
def extendByOne : extendBy (T := T) 1 ≅ 𝟭 (Kleisli T) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_one C.Arity _ Ω)) (by
    intro Ω Ξ σ
    calc _ = lift σ 1 := by apply Category.comp_id
      _ = σ := by apply lift_one
      _ = _ := by symm; apply Category.id_comp)

/-- Extension by `Φ` followed by extension by `Ψ` is naturally isomorphic to extension
by `Φ ⋈ Ψ`. -/
def extendByAssoc (Φ Ψ : C.Arity) :
    extendBy (T := T) Φ ⋙ extendBy Ψ ≅ extendBy (Φ ⋈ Ψ) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_assoc C.Arity _ Ω Φ Ψ)) (by
    intro Ω Ξ σ
    calc _ = lift (lift σ Φ) Ψ := by apply Category.comp_id
      _ = lift σ (Φ ⋈ Ψ) := by symm; apply lift_assoc
      _ = _ := by symm; apply Category.id_comp)

end KleisliArityAction

/-- `Subst.lift` is an arity action on the Kleisli category of `SyntaxMonad`. -/
instance syntaxMonadKleisliArityAction : KleisliArityAction SyntaxMonad where
  lift := Subst.lift
  lift_id := Subst.lift_id
  lift_comp := Subst.lift_comp
  lift_one := Subst.lift_one
  lift_assoc := Subst.lift_assoc

namespace ArityMod

open KleisliArityAction

variable {T : RelativeMonad J}

/-- Transport of an element of `M.obj Ω` along `Ω = Ξ`. -/
private def castObj (M : Kleisli T ⥤ Type) {Ω Ξ : C.Arity}
    (h : Ω = Ξ) : M.obj Ω → M.obj Ξ :=
  h ▸ fun x => x

private theorem castObj_heq
    (M : Kleisli T ⥤ Type) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  castObj M h x ≍ x
  := by
  subst Ξ
  rfl

private theorem shape_castObj
    (M : ArityMod T) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : module M |>.obj Ω) :
  shape M (castObj (module M) h x) = shape M x
  := by
  subst Ξ
  rfl

private theorem app_castObj_heq
    {M N : Kleisli T ⥤ Type} (g : M ⟶ N)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  g.app Ξ (castObj M h x) ≍ g.app Ω x
  := by
  subst Ξ
  rfl

variable [KleisliArityAction T]

private theorem lifted_action_comp_heq
    (N : Kleisli T ⥤ Type)
    {Γ Δ Ξ : C.Arity}
    (σ : Kleisli.of T Γ ⟶ Kleisli.of T Δ) (θ : Kleisli.of T Δ ⟶ Kleisli.of T Ξ)
    (Φ Ψ : C.Arity) (h : Ψ = Φ) (x : N.obj (Γ ⋈ Φ)) :
  N.map (lift (σ ≫ θ) Φ) x
    ≍ N.map (lift θ Ψ) (castObj N (congrArg (fun Λ => Δ ⋈ Λ) h.symm) (N.map (lift σ Φ) x))
  := by
  cases h
  apply heq_of_eq
  apply Functor.map_comp_apply (extendBy Φ ⋙ N)

/-- The module whose elements at `Ω` are pairs of `x : M(Ω)` and `y : N(Ω ⋈ shape x)`;
a Kleisli arrow `σ` acts on `x` through `M` and on `y` through `N` along
`lift σ (shape x)`. -/
def tensorModule (M N : ArityMod T) : Kleisli T ⥤ Type where
  obj Ω := Σ x : module M |>.obj Ω, module N |>.obj (Ω ⋈ shape M x)
  map {Ω Ξ} σ := ↾fun ⟨x, y⟩ =>
    let h := shape_natural M σ x
    ⟨module M |>.map σ x,
      castObj (module N) (congrArg (fun Λ => Ξ ⋈ Λ) h.symm)
        (module N |>.map (lift σ (shape M x)) y)⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    apply Sigma.ext
    · apply Functor.map_id_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply heq_of_eq
      apply Functor.map_id_apply (extendBy _ ⋙ module N)
  map_comp σ θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    apply Sigma.ext
    · apply Functor.map_comp_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply HEq.trans (lifted_action_comp_heq _ σ θ _ _ (shape_natural M σ x) y)
      symm
      apply castObj_heq

private theorem castTensor_fst_heq
    (M N : ArityMod T) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : (tensorModule M N).obj Ω) :
  (castObj (tensorModule M N) h x).1 ≍ x.1
  := by
  subst Ξ
  rfl

private theorem castTensor_snd_heq
    (M N : ArityMod T) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : (tensorModule M N).obj Ω) :
  (castObj (tensorModule M N) h x).2 ≍ x.2
  := by
  subst Ξ
  rfl

/-- The natural transformation sending a pair `⟨x, y⟩` of `tensorModule M N` to
`shape x ⋈ shape y`. -/
def tensorShape (M N : ArityMod T) : tensorModule M N ⟶ arityConst T where
  app Ω := ↾fun ⟨x, y⟩ => shape M x ⋈ shape N y
  naturality _ _ σ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    apply congrArg₂ (· ⋈ ·)
    · apply shape_natural
    · apply Eq.trans (shape_castObj N _ _)
      apply shape_natural

/-- The tensor product of arity modules: the module `tensorModule M N` with shape map
`tensorShape M N`. -/
def tensorObj (M N : ArityMod T) : ArityMod T :=
  Over.mk (tensorShape M N)

private theorem map_lift_natural_heq
    {M N : Kleisli T ⥤ Type} (g : M ⟶ N)
    {Ω Ξ : C.Arity} (σ : Kleisli.of T Ω ⟶ Kleisli.of T Ξ)
    (Φ Ψ Θ : C.Arity) (hΨ : Ψ = Φ) (hΘ : Θ = Φ) (x : M.obj (Ω ⋈ Φ)) :
  g.app (Ξ ⋈ Ψ) (castObj M (congrArg (fun Λ => Ξ ⋈ Λ) hΨ.symm) (M.map (lift σ Φ) x))
    ≍ N.map (lift σ Θ) (castObj N (congrArg (fun Λ => Ω ⋈ Λ) hΘ.symm) (g.app (Ω ⋈ Φ) x))
  := by
  cases hΨ
  cases hΘ
  apply heq_of_eq
  apply NatTrans.naturality_apply

private def tensorMapNat {M M' N N' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorModule M N ⟶ tensorModule M' N' where
  app Ω := ↾fun ⟨x, y⟩ =>
    let h := hom_shape f x
    ⟨f.left.app Ω x,
      castObj (module N') (congrArg (fun Λ => Ω ⋈ Λ) h.symm)
        (g.left.app (Ω ⋈ shape M x) y)⟩
  naturality _ _ σ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    apply Sigma.ext
    · apply NatTrans.naturality_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply HEq.trans
        (map_lift_natural_heq g.left σ _ _ _ (shape_natural M σ x) (hom_shape f x) y)
      symm
      apply castObj_heq

/-- The tensor product of morphisms of arity modules, acting componentwise on pairs. -/
def tensorMap {M M' N N' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  Over.homMk (tensorMapNat f g) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    rintro ⟨x, y⟩
    apply congrArg₂ (· ⋈ ·)
    · apply hom_shape
    · apply Eq.trans (shape_castObj N' _ _)
      apply hom_shape)

private theorem tensorMap_comp
    {M M' M'' N N' N'' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
  tensorMap f g ≫ tensorMap f' g' = tensorMap (f ≫ f') (g ≫ g')
  := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  rintro ⟨x, y⟩
  apply Sigma.ext
  · rfl
  · apply HEq.trans (castObj_heq _ _ _)
    apply HEq.trans (app_castObj_heq g'.left _ _)
    symm
    apply castObj_heq

/-- The module with one element at every arity, on which every Kleisli arrow acts as
the identity. -/
def tensorUnitModule : Kleisli T ⥤ Type where
  obj _ := PUnit
  map _ := ↾id
  map_id _ := rfl
  map_comp _ _ := rfl

private def tensorUnitShape :
    tensorUnitModule ⟶ arityConst T where
  app _ := ↾fun (_ : PUnit) => (1 : C.Arity)
  naturality _ _ _ := rfl

/-- The arity module `tensorUnitModule`, whose element has shape `1`. -/
def tensorUnit : ArityMod T :=
  Over.mk tensorUnitShape

private theorem map_lift_assoc_cast
    (M : Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (σ : Kleisli.of T Ω ⟶ Kleisli.of T Ξ)
    (Φ Ψ : C.Arity) (x : M.obj (Ω ⋈ (Φ ⋈ Ψ))) :
  M.map (lift (lift σ Φ) Ψ) (castObj M (mul_assoc Ω Φ Ψ).symm x)
    = castObj M (mul_assoc Ξ Φ Ψ).symm (M.map (lift σ (Φ ⋈ Ψ)) x)
  := by
  rw [← lift_assoc]
  rfl

private theorem map_lift_one_cast
    (M : Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (σ : Kleisli.of T Ω ⟶ Kleisli.of T Ξ)
    (x : M.obj (Ω ⋈ 1)) :
  castObj M (mul_one Ξ) (M.map (lift σ 1) x) = M.map σ (castObj M (mul_one Ω) x)
  := by
  rw [lift_one]
  rfl

private def associatorAppIso (M N P : ArityMod T) (Ω : C.Arity) :
    (tensorModule (tensorObj M N) P).obj Ω ≅
      (tensorModule M (tensorObj N P)).obj Ω where
  hom := ↾fun ⟨⟨x, y⟩, z⟩ =>
    ⟨x, ⟨y, castObj (module P) (mul_assoc Ω (shape M x) (shape N y)).symm z⟩⟩
  inv := ↾fun ⟨x, ⟨y, z⟩⟩ =>
    ⟨⟨x, y⟩, castObj (module P) (mul_assoc Ω (shape M x) (shape N y)) z⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def associatorNatIso (M N P : ArityMod T) :
    tensorModule (tensorObj M N) P ≅ tensorModule M (tensorObj N P) :=
  NatIso.ofComponents (associatorAppIso M N P) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, y⟩, z⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Sigma.ext
      · apply eq_of_heq
        apply HEq.trans (castObj_heq _ _ _)
        symm
        apply castTensor_fst_heq
      · apply HEq.trans (castObj_heq _ _ _)
        symm
        apply HEq.trans (castTensor_snd_heq _ _ _ _)
        apply HEq.trans (castObj_heq _ _ _)
        apply heq_of_eq
        apply map_lift_assoc_cast)

/-- The associator `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`, sending `⟨⟨x, y⟩, z⟩` to
`⟨x, ⟨y, z⟩⟩`. -/
def tensorAssociator (M N P : ArityMod T) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  Over.isoMk (associatorNatIso M N P) rfl

private def leftUnitorAppIso (M : ArityMod T) (Ω : C.Arity) :
    (tensorModule tensorUnit M).obj Ω ≅ module M |>.obj Ω where
  hom := ↾fun ⟨_, x⟩ => castObj (module M) (mul_one Ω) x
  inv := ↾fun x => ⟨PUnit.unit, castObj (module M) (mul_one Ω).symm x⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def leftUnitorNatIso (M : ArityMod T) :
    tensorModule tensorUnit M ≅ module M :=
  NatIso.ofComponents (leftUnitorAppIso M) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟩, x⟩
    apply map_lift_one_cast (module M) σ x)

/-- The left unitor `1 ⊗ M ≅ M`, sending `⟨*, x⟩` to `x`. -/
def tensorLeftUnitor (M : ArityMod T) : tensorObj tensorUnit M ≅ M :=
  Over.isoMk (leftUnitorNatIso M) rfl

private def rightUnitorAppIso (M : ArityMod T) (Ω : C.Arity) :
    (tensorModule M tensorUnit).obj Ω ≅ module M |>.obj Ω where
  hom := ↾fun ⟨x, _⟩ => x
  inv := ↾fun x => ⟨x, PUnit.unit⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def rightUnitorNatIso (M : ArityMod T) :
    tensorModule M tensorUnit ≅ module M :=
  NatIso.ofComponents (rightUnitorAppIso M) (fun _ => rfl)

/-- The right unitor `M ⊗ 1 ≅ M`, sending `⟨x, *⟩` to `x`. -/
def tensorRightUnitor (M : ArityMod T) : tensorObj M tensorUnit ≅ M :=
  Over.isoMk (rightUnitorNatIso M) rfl

instance : MonoidalCategoryStruct (ArityMod T) where
  tensorObj := tensorObj
  whiskerLeft := fun M {_ _} f => tensorMap (𝟙 M) f
  whiskerRight := fun {_ _} f N => tensorMap f (𝟙 N)
  tensorHom := tensorMap
  tensorUnit := tensorUnit
  associator := tensorAssociator
  leftUnitor := tensorLeftUnitor
  rightUnitor := tensorRightUnitor

private theorem associator_map_natural
    {M M' N N' P P' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
  tensorMap (tensorMap f g) h ≫ (tensorAssociator M' N' P').hom
    = (tensorAssociator M N P).hom ≫ tensorMap f (tensorMap g h)
  := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨x, y⟩, z⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · apply eq_of_heq
      apply HEq.trans (castObj_heq _ _ _)
      symm
      apply castTensor_fst_heq
    · apply HEq.trans (castObj_heq _ _ _)
      symm
      apply HEq.trans (castTensor_snd_heq _ _ _ _)
      apply HEq.trans (castObj_heq _ _ _)
      apply app_castObj_heq

instance : MonoidalCategory (ArityMod T) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by intros; rfl)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensorMap_comp)
    (associator_naturality := associator_map_natural)
    (leftUnitor_naturality := by intros; rfl)
    (rightUnitor_naturality := by intros; rfl)
    (pentagon := by intros; rfl)
    (triangle := by intros; rfl)

end ArityMod
