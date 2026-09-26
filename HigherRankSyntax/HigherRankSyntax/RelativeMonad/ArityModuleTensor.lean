import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.EqToHom
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.RelativeMonad.ArityModule

/-!
# The tensor product of arity modules

Let `T` be a relative monad over `J`.  A `KleisliArityAction T` extends every Kleisli
arrow `σ : Ω ⟶ Ξ` along an arity `Φ` to an arrow `lift σ Φ : Ω ⋈ Φ ⟶ Ξ ⋈ Φ`,
functorially in `σ`, with `lift σ 1 = σ` and `lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ`.
`Subst.lift` is such an action on the Kleisli category of `SyntaxMonad`.

For arity modules `M` and `N`, an element of the tensor `M ⊗ N` at `Ω` is a pair of
`x : M(Ω)` and `y : N(Ω ⋈ shape x)`, of shape `shape x ⋈ shape y`; a Kleisli arrow `σ`
acts on `y` through the extension of `σ` along `shape x`.  With the one-element module
of shape `1` as unit, `ArityMod T` is a monoidal category.
-/

open CategoryTheory

/-- A right action of arities on the Kleisli category of `T`: every arrow
`σ : Γ ⟶ Δ` extends along `Φ` to `lift σ Φ : Γ ⋈ Φ ⟶ Δ ⋈ Φ`, functorially in `σ`, with
`lift σ 1 = σ` and `lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ`. -/
class KleisliArityAction (T : RelativeMonad (J)) where
  lift {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶ RelativeMonad.Kleisli.of T Δ)
    (Φ : C.Arity) :
    RelativeMonad.Kleisli.of T (Γ ⋈ Φ) ⟶
      RelativeMonad.Kleisli.of T (Δ ⋈ Φ)
  lift_id (Γ Φ : C.Arity) :
    lift (𝟙 (RelativeMonad.Kleisli.of T Γ)) Φ =
      𝟙 (RelativeMonad.Kleisli.of T (Γ ⋈ Φ))
  lift_comp {Γ Δ Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶ RelativeMonad.Kleisli.of T Δ)
    (θ : RelativeMonad.Kleisli.of T Δ ⟶ RelativeMonad.Kleisli.of T Ξ)
    (Φ : C.Arity) : lift (σ ≫ θ) Φ = lift σ Φ ≫ lift θ Φ
  lift_one {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶ RelativeMonad.Kleisli.of T Δ) :
    lift σ 1 = σ
  lift_assoc {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶ RelativeMonad.Kleisli.of T Δ)
    (Φ Ψ : C.Arity) : lift σ (Φ ⋈ Ψ) = lift (lift σ Φ) Ψ

namespace KleisliArityAction

variable {T : RelativeMonad (J)} [KleisliArityAction T]

/-- The endofunctor of the Kleisli category sending `Ω` to `Ω ⋈ Φ` and `σ` to
`lift σ Φ`. -/
def extendBy (Φ : C.Arity) :
    RelativeMonad.Kleisli T ⥤ RelativeMonad.Kleisli T where
  obj Ω := Ω ⋈ Φ
  map σ := lift σ Φ
  map_id Ω := lift_id Ω Φ
  map_comp σ θ := lift_comp σ θ Φ

/-- Extension by the unit arity is naturally isomorphic to the identity functor. -/
def extendByOne : extendBy (T := T) 1 ≅ 𝟭 (RelativeMonad.Kleisli T) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_one C.Arity _ Ω)) (by
    intro Ω Ξ σ
    calc _ = lift σ 1 := by apply Category.comp_id
      _ = σ := by apply lift_one
      _ = _ := by
          symm
          apply Category.id_comp)

/-- Extension by `Φ` followed by extension by `Ψ` is naturally isomorphic to extension
by `Φ ⋈ Ψ`. -/
def extendByAssoc (Φ Ψ : C.Arity) :
    extendBy (T := T) Φ ⋙ extendBy Ψ ≅ extendBy (Φ ⋈ Ψ) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_assoc C.Arity _ Ω Φ Ψ)) (by
    intro Ω Ξ σ
    calc _ = lift (lift σ Φ) Ψ := by apply Category.comp_id
      _ = lift σ (Φ ⋈ Ψ) := by
          symm
          apply lift_assoc
      _ = _ := by
          symm
          apply Category.id_comp)

end KleisliArityAction

/-- `Subst.lift` is an arity action on the Kleisli category of `SyntaxMonad`. -/
instance syntaxMonadKleisliArityAction :
    KleisliArityAction (SyntaxMonad) where
  lift := Subst.lift
  lift_id := Subst.lift_id
  lift_comp := Subst.lift_comp
  lift_one := Subst.lift_one
  lift_assoc := Subst.lift_assoc

namespace ArityMod

variable {T : RelativeMonad (J)} [KleisliArityAction T]

private def castObj (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity}
    (h : Ω = Ξ) : M.obj Ω → M.obj Ξ :=
  h ▸ fun x => x

omit [KleisliArityAction T] in
private theorem castObj_symm
    (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  castObj M h.symm (castObj M h x) = x
  := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem castObj_symm'
    (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ξ) :
  castObj M h (castObj M h.symm x) = x
  := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem castObj_heq
    (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  castObj M h x ≍ x
  := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem shape_castObj
    (M : ArityMod T) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : module M |>.obj Ω) :
  shape M (castObj (module M) h x) = shape M x
  := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem nat_cast_heq
    {M N : RelativeMonad.Kleisli T ⥤ Type} (g : M ⟶ N)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  g.app Ξ (castObj M h x) ≍ g.app Ω x
  := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem map_eqToHom_apply
    (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
  M.map (@eqToHom (RelativeMonad.Kleisli T) _ Ω Ξ h) x = castObj M h x
  := by
  subst Ξ
  apply Functor.map_id_apply

private theorem lifted_action_comp_heq
    (N : RelativeMonad.Kleisli T ⥤ Type)
    {Γ Δ Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶ RelativeMonad.Kleisli.of T Δ)
    (θ : RelativeMonad.Kleisli.of T Δ ⟶ RelativeMonad.Kleisli.of T Ξ)
    (r s : C.Arity) (h : s = r) (x : N.obj (Γ ⋈ r)) :
  N.map ((KleisliArityAction.extendBy r).map (σ ≫ θ)) x
    ≍ N.map ((KleisliArityAction.extendBy s).map θ)
        (castObj N (congrArg (fun q => Δ ⋈ q) h.symm)
          (N.map ((KleisliArityAction.extendBy r).map σ) x))
  := by
  cases h
  apply heq_of_eq
  apply Functor.map_comp_apply (KleisliArityAction.extendBy r ⋙ N)

/-- The module whose elements at `Ω` are pairs of `x : M(Ω)` and `y : N(Ω ⋈ shape x)`;
a Kleisli arrow `σ` acts on `x` through `M` and on `y` through `N` along
`lift σ (shape x)`. -/
def tensorModule (M N : ArityMod T) : RelativeMonad.Kleisli T ⥤ Type where
  obj Ω := Σ Γ : module M |>.obj Ω,
    module N |>.obj (Ω ⋈ shape M Γ)
  map {Ω Ξ} σ := ↾fun ⟨Γ, Δ⟩ =>
    let h := shape_natural M σ Γ
    ⟨module M |>.map σ Γ,
      castObj (module N) (congrArg (fun Λ => Ξ ⋈ Λ) h.symm)
        (module N |>.map (KleisliArityAction.lift σ (shape M Γ)) Δ)⟩
  map_id Ω := by
    apply ConcreteCategory.hom_ext
    rintro ⟨Γ, Δ⟩
    apply Sigma.ext
    · apply Functor.map_id_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply heq_of_eq
      apply Functor.map_id_apply (KleisliArityAction.extendBy _ ⋙ module N)
  map_comp σ θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨Γ, Δ⟩
    apply Sigma.ext
    · apply Functor.map_comp_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply HEq.trans (lifted_action_comp_heq _ σ θ _ _ (shape_natural M σ Γ) Δ)
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
  app Ω := ↾fun ⟨Γ, Δ⟩ => shape M Γ ⋈ shape N Δ
  naturality _ _ σ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨Γ, Δ⟩
    apply congrArg₂ (· ⋈ ·)
    · apply shape_natural
    · apply Eq.trans (shape_castObj N _ _)
      apply shape_natural

/-- The tensor product of arity modules: the module `tensorModule M N` with shape map
`tensorShape M N`. -/
def tensorObj (M N : ArityMod T) : ArityMod T :=
  Over.mk (tensorShape M N)

@[simp]
theorem tensorObj_module (M N : ArityMod T) :
  module (tensorObj M N) = tensorModule M N
  := rfl

@[simp]
theorem tensorObj_shape
    (M N : ArityMod T) {Ω : C.Arity} (x : module (tensorObj M N) |>.obj Ω) :
  shape (tensorObj M N) x = shape M x.1 ⋈ shape N x.2
  := rfl

private theorem map_lift_natural_heq
    {M N : RelativeMonad.Kleisli T ⥤ Type} (g : M ⟶ N)
    {Ω Ξ : C.Arity} (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (r s t : C.Arity) (hs : s = r) (ht : t = r)
    (x : M.obj (Ω ⋈ r)) :
  g.app (Ξ ⋈ s)
      (castObj M (congrArg (fun q => Ξ ⋈ q) hs.symm)
        (M.map ((KleisliArityAction.extendBy r).map σ) x))
    ≍ N.map ((KleisliArityAction.extendBy t).map σ)
        (castObj N (congrArg (fun q => Ω ⋈ q) ht.symm) (g.app (Ω ⋈ r) x))
  := by
  cases hs
  cases ht
  apply heq_of_eq
  apply NatTrans.naturality_apply

private def tensorMapNat {M M' N N' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorModule M N ⟶ tensorModule M' N' where
  app Ω := ↾fun ⟨Γ, Δ⟩ =>
    let h := hom_shape f Γ
    ⟨f.left.app Ω Γ,
      castObj (module N') (congrArg (fun Λ => Ω ⋈ Λ) h.symm)
        (g.left.app (Ω ⋈ shape M Γ) Δ)⟩
  naturality _ _ σ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨Γ, Δ⟩
    apply Sigma.ext
    · apply NatTrans.naturality_apply
    · apply HEq.trans (castObj_heq _ _ _)
      apply HEq.trans
        (map_lift_natural_heq g.left σ _ _ _ (shape_natural M σ Γ) (hom_shape f Γ) Δ)
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
    rintro ⟨Γ, Δ⟩
    apply congrArg₂ (· ⋈ ·)
    · apply hom_shape
    · apply Eq.trans (shape_castObj N' _ _)
      apply hom_shape)

@[simp]
theorem tensorMap_left {M M' N N' : ArityMod T} (f : M ⟶ M') (g : N ⟶ N') :
  (tensorMap f g).left = tensorMapNat f g
  := rfl

private theorem tensorMap_id (M N : ArityMod T) :
  tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N)
  := rfl

private theorem tensorMap_comp
    {M M' M'' N N' N'' : ArityMod T}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
  tensorMap f g ≫ tensorMap f' g' = tensorMap (f ≫ f') (g ≫ g')
  := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  rintro ⟨Γ, Δ⟩
  apply Sigma.ext
  · rfl
  · apply HEq.trans (castObj_heq _ _ _)
    apply HEq.trans (nat_cast_heq g'.left _ _)
    symm
    apply castObj_heq

/-- The module with one element at every arity, on which every Kleisli arrow acts as
the identity. -/
def tensorUnitModule : RelativeMonad.Kleisli T ⥤ Type where
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

omit [KleisliArityAction T] in
@[simp]
theorem tensorUnit_module :
  module (tensorUnit (T := T)) = tensorUnitModule (T := T)
  := rfl

omit [KleisliArityAction T] in
@[simp]
theorem tensorUnit_shape {Ω : C.Arity} (x : module (tensorUnit (T := T)) |>.obj Ω) :
  shape (tensorUnit (T := T)) x = 1
  := rfl

private theorem map_lift_assoc_cast
    (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (Φ Ψ : C.Arity) (x : M.obj (Ω ⋈ (Φ ⋈ Ψ))) :
  M.map (KleisliArityAction.lift (KleisliArityAction.lift σ Φ) Ψ)
      (castObj M (@mul_assoc C.Arity _ Ω Φ Ψ).symm x)
    = castObj M (@mul_assoc C.Arity _ Ξ Φ Ψ).symm (M.map (KleisliArityAction.lift σ (Φ ⋈ Ψ)) x)
  := by
  rw [← KleisliArityAction.lift_assoc]
  rfl

private theorem map_lift_one_cast
    (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (x : M.obj (Ω ⋈ 1)) :
  castObj M (@mul_one C.Arity _ Ξ) (M.map (KleisliArityAction.lift σ 1) x)
    = M.map σ (castObj M (@mul_one C.Arity _ Ω) x)
  := by
  rw [KleisliArityAction.lift_one]
  rfl

private def associatorAppIso (M N P : ArityMod T) (Ω : C.Arity) :
    (tensorModule (tensorObj M N) P).obj Ω ≅
      (tensorModule M (tensorObj N P)).obj Ω where
  hom := ↾fun ⟨⟨Γ, Δ⟩, Ξ⟩ =>
    ⟨Γ, ⟨Δ,
      castObj (module P) (@mul_assoc C.Arity _ Ω (shape M Γ)
        (shape N Δ)).symm Ξ⟩⟩
  inv := ↾fun ⟨Γ, ⟨Δ, Ξ⟩⟩ =>
    ⟨⟨Γ, Δ⟩,
      castObj (module P) (@mul_assoc C.Arity _ Ω (shape M Γ)
        (shape N Δ)) Ξ⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def associatorNatIso (M N P : ArityMod T) :
    tensorModule (tensorObj M N) P ≅ tensorModule M (tensorObj N P) :=
  NatIso.ofComponents (associatorAppIso M N P) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨Γ, Δ⟩, Θ⟩
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
  hom := ↾fun ⟨_, Γ⟩ =>
    castObj (module M) (@mul_one C.Arity _ Ω) Γ
  inv := ↾fun Γ =>
    ⟨PUnit.unit, castObj (module M) (@mul_one C.Arity _ Ω).symm Γ⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def leftUnitorNatIso (M : ArityMod T) :
    tensorModule tensorUnit M ≅ module M :=
  NatIso.ofComponents (leftUnitorAppIso M) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟩, Γ⟩
    apply map_lift_one_cast (module M) σ Γ)

/-- The left unitor `1 ⊗ M ≅ M`, sending `⟨*, x⟩` to `x`. -/
def tensorLeftUnitor (M : ArityMod T) : tensorObj tensorUnit M ≅ M :=
  Over.isoMk (leftUnitorNatIso M) rfl

private def rightUnitorAppIso (M : ArityMod T) (Ω : C.Arity) :
    (tensorModule M tensorUnit).obj Ω ≅ module M |>.obj Ω where
  hom := ↾fun ⟨Γ, _⟩ => Γ
  inv := ↾fun Γ => ⟨Γ, PUnit.unit⟩
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
  rintro ⟨⟨Γ, Δ⟩, Ξ⟩
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
      apply nat_cast_heq

private theorem leftUnitor_map_natural {M N : ArityMod T} (f : M ⟶ N) :
  tensorMap (𝟙 tensorUnit) f ≫ (tensorLeftUnitor N).hom = (tensorLeftUnitor M).hom ≫ f
  := rfl

private theorem rightUnitor_map_natural {M N : ArityMod T} (f : M ⟶ N) :
  tensorMap f (𝟙 tensorUnit) ≫ (tensorRightUnitor N).hom = (tensorRightUnitor M).hom ≫ f
  := rfl

private theorem tensor_pentagon (M N P Q : ArityMod T) :
  tensorMap (tensorAssociator M N P).hom (𝟙 Q)
      ≫ (tensorAssociator M (tensorObj N P) Q).hom
      ≫ tensorMap (𝟙 M) (tensorAssociator N P Q).hom
    = (tensorAssociator (tensorObj M N) P Q).hom
      ≫ (tensorAssociator M N (tensorObj P Q)).hom
  := rfl

private theorem tensor_triangle (M N : ArityMod T) :
  (tensorAssociator M tensorUnit N).hom ≫ tensorMap (𝟙 M) (tensorLeftUnitor N).hom
    = tensorMap (tensorRightUnitor M).hom (𝟙 N)
  := rfl

instance : MonoidalCategory (ArityMod T) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intros
      apply tensorMap_comp)
    (associator_naturality := associator_map_natural)
    (leftUnitor_naturality := leftUnitor_map_natural)
    (rightUnitor_naturality := rightUnitor_map_natural)
    (pentagon := tensor_pentagon)
    (triangle := tensor_triangle)

end ArityMod
