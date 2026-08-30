import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.EqToHom
import HigherRankSyntax.SyntaxMonad
import HigherRankSyntax.RelativeMonad.ArityModule

/-!
# The context-extension tensor on arity-shaped modules

Let `T` be a relative monad whose contexts are raw arities.  Extension by an
arity `Φ` should act on `Kl(T)` by sending `Ω` to `Ω ⋈ Φ`: a substitution is
lifted through the new slots and leaves them fixed.  `KleisliArityAction T`
records this action and its unit and associativity coherences.
The comparison isomorphisms are the canonical equality isomorphisms supplied
by the arity monoid, so their triangle and pentagon coherence is forced by
proof irrelevance; the `MonoidalCategory` construction below proves those
diagrams rather than adding further axioms to the interface.

An arity-shaped `T`-module remembers the raw shape of each of its elements.
The tensor of modules `M` and `N` first chooses `m : M(Ω)`, extends the base by
the shape of `m`, and then chooses `n : N(Ω ⋈ |m|)`.  Its action on `n` uses
the lifted substitution, so this tensor is dependent sequencing rather than
the pointwise cartesian product of functors.

The unit, associator and unitors express that extension by the unit arity and
the bracketing of successive extensions are inessential, so `ArityMod T` is a
monoidal category.
-/

open CategoryTheory

/-- A coherent right action of raw arities on a relative Kleisli category. -/
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

/-- Extend every Kleisli context and morphism by a fixed raw suffix. -/
def extendBy (Φ : C.Arity) :
    RelativeMonad.Kleisli T ⥤ RelativeMonad.Kleisli T where
  obj Ω := Ω ⋈ Φ
  map σ := KleisliArityAction.lift σ Φ
  map_id Ω := KleisliArityAction.lift_id Ω Φ
  map_comp σ θ := KleisliArityAction.lift_comp σ θ Φ

/-- Extension by the empty arity is naturally the identity. -/
def extendByOne : extendBy (T := T) 1 ≅ 𝟭 (RelativeMonad.Kleisli T) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_one C.Arity _ Ω)) (by
    intro Ω Ξ σ
    apply eq_of_heq
    exact
      (comp_eqToHom_heq ((extendBy (T := T) 1).map σ)
        (@mul_one C.Arity _ Ξ)).trans
      ((heq_of_eq (KleisliArityAction.lift_one σ)).trans
        (eqToHom_comp_heq σ (@mul_one C.Arity _ Ω)).symm))

/-- Successive extensions are naturally extension by the product suffix. -/
def extendByAssoc (Φ Ψ : C.Arity) :
    extendBy (T := T) Φ ⋙ extendBy Ψ ≅ extendBy (Φ ⋈ Ψ) :=
  NatIso.ofComponents
    (fun Ω => eqToIso (@mul_assoc C.Arity _ Ω Φ Ψ)) (by
    intro Ω Ξ σ
    apply eq_of_heq
    exact
      (comp_eqToHom_heq
        ((extendBy (T := T) Φ ⋙ extendBy Ψ).map σ)
        (@mul_assoc C.Arity _ Ξ Φ Ψ)).trans
      ((heq_of_eq (KleisliArityAction.lift_assoc σ Φ Ψ).symm).trans
        (eqToHom_comp_heq ((extendBy (T := T) (Φ ⋈ Ψ)).map σ)
          (@mul_assoc C.Arity _ Ω Φ Ψ)).symm))

end KleisliArityAction

/-- Raw substitution supplies the arity action on the syntax Kleisli category. -/
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
private theorem castObj_symm (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
    castObj M h.symm (castObj M h x) = x := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem castObj_symm' (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ξ) :
    castObj M h (castObj M h.symm x) = x := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem castObj_heq (M : RelativeMonad.Kleisli T ⥤ Type) {Ω Ξ : C.Arity}
    (h : Ω = Ξ) (x : M.obj Ω) : castObj M h x ≍ x := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem shape_castObj (M : ArityMod T) {Ω Ξ : C.Arity}
    (h : Ω = Ξ) (x : module M |>.obj Ω) :
    shape M (castObj (module M) h x) = shape M x := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem nat_cast_heq {M N : RelativeMonad.Kleisli T ⥤ Type}
    (g : M ⟶ N) {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
    g.app Ξ (castObj M h x) ≍ g.app Ω x := by
  subst Ξ
  rfl

omit [KleisliArityAction T] in
private theorem map_eqToHom_apply (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : M.obj Ω) :
    M.map (@eqToHom (RelativeMonad.Kleisli T) _ Ω Ξ h) x =
      castObj M h x := by
  cases h
  simp [castObj]

private theorem lifted_action_comp_heq (N : RelativeMonad.Kleisli T ⥤ Type)
    {Γ Δ Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Γ ⟶
      RelativeMonad.Kleisli.of T Δ)
    (θ : RelativeMonad.Kleisli.of T Δ ⟶
      RelativeMonad.Kleisli.of T Ξ)
    (r s : C.Arity) (h : s = r) (x : N.obj (Γ ⋈ r)) :
    N.map ((KleisliArityAction.extendBy r).map (σ ≫ θ)) x ≍
      N.map ((KleisliArityAction.extendBy s).map θ)
        (castObj N (congrArg (fun q => Δ ⋈ q) h.symm)
          (N.map ((KleisliArityAction.extendBy r).map σ) x)) := by
  cases h
  rw [(KleisliArityAction.extendBy r).map_comp]
  apply heq_of_eq
  apply N.map_comp_apply

/-- The underlying syntax module of the context-extension tensor. -/
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
    intro x
    rcases x with ⟨Γ, Δ⟩
    dsimp
    apply Sigma.ext
    · apply Functor.map_id_apply
    · change HEq
        (castObj (module N)
          (congrArg (fun Λ => Ω ⋈ Λ)
            (shape_natural M (𝟙 _) Γ).symm)
          (module N |>.map
            (KleisliArityAction.lift (𝟙 _) (shape M Γ)) Δ)) Δ
      exact HEq.trans (castObj_heq _ _ _)
        (heq_of_eq (by
          rw [KleisliArityAction.lift_id]
          apply Functor.map_id_apply))
  map_comp {Ω Ξ Θ} σ θ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    dsimp
    apply Sigma.ext
    · apply Functor.map_comp_apply
    · dsimp
      let h := shape_natural M σ Γ
      exact HEq.trans (castObj_heq _ _ _)
        (HEq.trans (lifted_action_comp_heq _ σ θ _ _ h Δ)
          (castObj_heq _ _ _).symm)

private theorem castTensor_fst_heq (M N : ArityMod T)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : (tensorModule M N).obj Ω) :
    (castObj (tensorModule M N) h x).1 ≍ x.1 := by
  subst Ξ
  rfl

private theorem castTensor_snd_heq (M N : ArityMod T)
    {Ω Ξ : C.Arity} (h : Ω = Ξ) (x : (tensorModule M N).obj Ω) :
    (castObj (tensorModule M N) h x).2 ≍ x.2 := by
  subst Ξ
  rfl

/-- The raw shape of a pair of successive telescopes. -/
def tensorShape (M N : ArityMod T) : tensorModule M N ⟶ arityConst T where
  app Ω := ↾fun ⟨Γ, Δ⟩ => shape M Γ ⋈ shape N Δ
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    change
      shape M (module M |>.map σ Γ) ⋈
          shape N
            (castObj (module N) _
              (module N |>.map (KleisliArityAction.lift σ (shape M Γ)) Δ)) =
        shape M Γ ⋈ shape N Δ
    calc
      _ = shape M Γ ⋈ shape N
          (castObj (module N) _
            (module N |>.map (KleisliArityAction.lift σ (shape M Γ)) Δ)) :=
          congrArg (fun Λ => Λ ⋈ _) (shape_natural M σ Γ)
      _ = shape M Γ ⋈ shape N
          (module N |>.map (KleisliArityAction.lift σ (shape M Γ)) Δ) :=
          congrArg (fun Λ => shape M Γ ⋈ Λ)
            (shape_castObj N _ _)
      _ = _ := congrArg (fun Λ => shape M Γ ⋈ Λ)
        (shape_natural N (KleisliArityAction.lift σ (shape M Γ)) Δ)

/-- The context-extension tensor on arity-shaped syntax modules. -/
def tensorObj (M N : ArityMod T) : ArityMod T :=
  Over.mk (tensorShape M N)

@[simp]
theorem tensorObj_module (M N : ArityMod T) :
    module (tensorObj M N) = tensorModule M N := rfl

@[simp]
theorem tensorObj_shape (M N : ArityMod T) {Ω : C.Arity}
    (x : module (tensorObj M N) |>.obj Ω) :
    shape (tensorObj M N) x = shape M x.1 ⋈ shape N x.2 := rfl

private theorem map_lift_natural_heq
    {M N : RelativeMonad.Kleisli T ⥤ Type} (g : M ⟶ N)
    {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Ω ⟶
      RelativeMonad.Kleisli.of T Ξ)
    (r s t : C.Arity) (hs : s = r) (ht : t = r)
    (x : M.obj (Ω ⋈ r)) :
    g.app (Ξ ⋈ s)
      (castObj M (congrArg (fun q => Ξ ⋈ q) hs.symm)
        (M.map ((KleisliArityAction.extendBy r).map σ) x)) ≍
      N.map ((KleisliArityAction.extendBy t).map σ)
        (castObj N (congrArg (fun q => Ω ⋈ q) ht.symm)
          (g.app (Ω ⋈ r) x)) := by
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
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    dsimp
    apply Sigma.ext
    · apply NatTrans.naturality_apply
    · dsimp
      let hs := shape_natural M σ Γ
      let ht := hom_shape f Γ
      exact HEq.trans (castObj_heq _ _ _)
        (HEq.trans (map_lift_natural_heq g.left σ _ _ _ hs ht Δ)
          (castObj_heq _ _ _).symm)

/-- The context-extension tensor on shape-preserving module morphisms. -/
def tensorMap {M M' N N' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M' N' :=
  Over.homMk (tensorMapNat f g) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    change
      shape M' (f.left.app _ Γ) ⋈
        shape N'
          (castObj (module N') _
            (g.left.app _ Δ)) =
        shape M Γ ⋈ shape N Δ
    calc
      _ = shape M Γ ⋈ shape N'
          (castObj (module N') _ (g.left.app _ Δ)) :=
          congrArg (fun Λ => Λ ⋈ _) (hom_shape f Γ)
      _ = shape M Γ ⋈ shape N' (g.left.app _ Δ) :=
          congrArg (fun Λ => shape M Γ ⋈ Λ) (shape_castObj N' _ _)
      _ = _ := congrArg (fun Λ => shape M Γ ⋈ Λ) (hom_shape g Δ))

@[simp]
theorem tensorMap_left {M M' N N' : ArityMod T}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensorMap f g).left = tensorMapNat f g := rfl

private theorem tensorMap_id (M N : ArityMod T) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N) := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, Δ⟩
  simp [tensorMap, tensorMapNat, castObj]
  rfl

private theorem tensorMap_comp
    {M M' M'' N N' N'' : ArityMod T}
    (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    tensorMap f g ≫ tensorMap f' g' =
      tensorMap (f ≫ f') (g ≫ g') := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, Δ⟩
  dsimp [tensorMap, tensorMapNat]
  apply Sigma.ext
  · rfl
  · exact HEq.trans (castObj_heq _ _ _)
      (HEq.trans (nat_cast_heq g'.left _ _)
        (castObj_heq _ _ _).symm)

/-- The singleton module, whose unique element has empty raw shape. -/
def tensorUnitModule : RelativeMonad.Kleisli T ⥤ Type where
  obj _ := PUnit
  map _ := ↾id
  map_id _ := rfl
  map_comp _ _ := rfl

private def tensorUnitShape :
    tensorUnitModule ⟶ arityConst T where
  app _ := ↾fun (_ : PUnit) => (1 : C.Arity)
  naturality := by intros; rfl

/-- The monoidal unit for context extension. -/
def tensorUnit : ArityMod T :=
  Over.mk tensorUnitShape

omit [KleisliArityAction T] in
@[simp]
theorem tensorUnit_module :
    module (tensorUnit (T := T)) =
      tensorUnitModule (T := T) := rfl

omit [KleisliArityAction T] in
@[simp]
theorem tensorUnit_shape {Ω : C.Arity}
    (x : module (tensorUnit (T := T)) |>.obj Ω) :
    shape (tensorUnit (T := T)) x = 1 := rfl

private theorem map_lift_assoc_cast (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (Φ Ψ : C.Arity)
    (x : M.obj (Ω ⋈ (Φ ⋈ Ψ))) :
    M.map (KleisliArityAction.lift (KleisliArityAction.lift σ Φ) Ψ)
        (castObj M (@mul_assoc C.Arity _ Ω Φ Ψ).symm x) =
      castObj M (@mul_assoc C.Arity _ Ξ Φ Ψ).symm
        (M.map (KleisliArityAction.lift σ (Φ ⋈ Ψ)) x) := by
  calc
    _ = M.map (KleisliArityAction.lift
          (KleisliArityAction.lift σ Φ) Ψ)
        (M.map (@eqToHom (RelativeMonad.Kleisli T) _ _ _
          (@mul_assoc C.Arity _ Ω Φ Ψ).symm) x) :=
      congrArg _ (map_eqToHom_apply M _ x).symm
    _ = M.map
        ((@eqToHom (RelativeMonad.Kleisli T) _ _ _
            (@mul_assoc C.Arity _ Ω Φ Ψ).symm) ≫
          KleisliArityAction.lift
            (KleisliArityAction.lift σ Φ) Ψ) x :=
      (Functor.map_comp_apply _ _ _ _).symm
    _ = M.map
        (KleisliArityAction.lift σ (Φ ⋈ Ψ) ≫
          (@eqToHom (RelativeMonad.Kleisli T) _ _ _
            (@mul_assoc C.Arity _ Ξ Φ Ψ).symm)) x := by
      apply congrArg (fun f => M.map f x)
      exact ((KleisliArityAction.extendByAssoc (T := T) Φ Ψ).inv.naturality σ).symm
    _ = M.map
        (@eqToHom (RelativeMonad.Kleisli T) _ _ _
          (@mul_assoc C.Arity _ Ξ Φ Ψ).symm)
        (M.map (KleisliArityAction.lift σ (Φ ⋈ Ψ)) x) :=
      Functor.map_comp_apply _ _ _ _
    _ = _ := map_eqToHom_apply M _ _

private theorem map_lift_one_cast (M : RelativeMonad.Kleisli T ⥤ Type)
    {Ω Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of T Ω ⟶ RelativeMonad.Kleisli.of T Ξ)
    (x : M.obj (Ω ⋈ 1)) :
    castObj M (@mul_one C.Arity _ Ξ) (M.map (KleisliArityAction.lift σ 1) x) =
      M.map σ (castObj M (@mul_one C.Arity _ Ω) x) := by
  calc
    _ = M.map
        (@eqToHom (RelativeMonad.Kleisli T) _ _ _
          (@mul_one C.Arity _ Ξ))
        (M.map (KleisliArityAction.lift σ 1) x) :=
      (map_eqToHom_apply M _ _).symm
    _ = M.map
        (KleisliArityAction.lift σ 1 ≫
          (@eqToHom (RelativeMonad.Kleisli T) _ _ _
            (@mul_one C.Arity _ Ξ))) x :=
      (Functor.map_comp_apply _ _ _ _).symm
    _ = M.map
        ((@eqToHom (RelativeMonad.Kleisli T) _ _ _
            (@mul_one C.Arity _ Ω)) ≫ σ) x := by
      apply congrArg (fun f => M.map f x)
      exact (KleisliArityAction.extendByOne (T := T)).hom.naturality σ
    _ = M.map σ
        (M.map
          (@eqToHom (RelativeMonad.Kleisli T) _ _ _
            (@mul_one C.Arity _ Ω)) x) :=
      Functor.map_comp_apply _ _ _ _
    _ = _ := congrArg (fun y => M.map σ y) (map_eqToHom_apply M _ _)

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
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
    simp [castObj]
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, ⟨Δ, Ξ⟩⟩
    simp [castObj]

private def associatorNatIso (M N P : ArityMod T) :
    tensorModule (tensorObj M N) P ≅ tensorModule M (tensorObj N P) :=
  NatIso.ofComponents (associatorAppIso M N P) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨⟨Γ, Δ⟩, Θ⟩
    let q := (tensorModule (tensorObj M N) P).map σ
      ⟨⟨Γ, Δ⟩, Θ⟩
    let hp := congrArg (fun Λ => Ξ ⋈ Λ)
      (shape_natural (tensorObj M N) σ ⟨Γ, Δ⟩).symm
    let z : (tensorModule N P).obj (Ω ⋈ shape M Γ) :=
      ⟨Δ, castObj (module P)
        (@mul_assoc C.Arity _ Ω (shape M Γ) (shape N Δ)).symm Θ⟩
    let y := (tensorModule N P).map
      (KleisliArityAction.lift σ (shape M Γ)) z
    let ho := congrArg (fun Λ => Ξ ⋈ Λ)
      (shape_natural M σ Γ).symm
    change
      (associatorAppIso M N P Ξ).hom
          ((tensorModule (tensorObj M N) P).map σ ⟨⟨Γ, Δ⟩, Θ⟩) =
        (tensorModule M (tensorObj N P)).map σ
          ((associatorAppIso M N P Ω).hom ⟨⟨Γ, Δ⟩, Θ⟩)
    dsimp only [associatorAppIso, tensorModule]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Sigma.ext
      · apply eq_of_heq
        change HEq
          (castObj (module N) _
            (module N |>.map (KleisliArityAction.lift σ (shape M Γ)) Δ))
          (castObj (tensorModule N P) ho y).1
        exact HEq.trans (castObj_heq _ _ _)
          (castTensor_fst_heq N P ho y).symm
      · change HEq
          (castObj (module P)
            (@mul_assoc C.Arity _ Ξ (shape M q.1.1)
              (shape N q.1.2)).symm
            (castObj (module P) hp
              (module P |>.map (KleisliArityAction.lift σ
                (shape M Γ ⋈ shape N Δ)) Θ)))
          (castObj (tensorModule N P) ho y).2
        exact HEq.trans (castObj_heq _ _ _)
          (HEq.trans (castObj_heq _ _ _)
            (HEq.trans
              ((HEq.trans
                (heq_of_eq (map_lift_assoc_cast (module P) σ
                  (shape M Γ) (shape N Δ) Θ))
                (castObj_heq _ _ _)).symm)
              (HEq.trans (castObj_heq _ _ _).symm
                (castTensor_snd_heq N P ho y).symm))))

/-- Reassociation of three successive telescope segments. -/
def tensorAssociator (M N P : ArityMod T) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  Over.isoMk (associatorNatIso M N P) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
    exact (@mul_assoc C.Arity _ (shape M Γ) (shape N Δ)
      (shape P Ξ)).symm)

private def leftUnitorAppIso (M : ArityMod T) (Ω : C.Arity) :
    (tensorModule tensorUnit M).obj Ω ≅ module M |>.obj Ω where
  hom := ↾fun ⟨_, Γ⟩ =>
    castObj (module M) (@mul_one C.Arity _ Ω) Γ
  inv := ↾fun Γ =>
    ⟨PUnit.unit, castObj (module M) (@mul_one C.Arity _ Ω).symm Γ⟩
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨u, Γ⟩
    cases u
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (castObj_symm (module M)
        (@mul_one C.Arity _ Ω) Γ)
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro Γ
    exact castObj_symm' (module M) (@mul_one C.Arity _ Ω) Γ

private def leftUnitorNatIso (M : ArityMod T) :
    tensorModule tensorUnit M ≅ module M :=
  NatIso.ofComponents (leftUnitorAppIso M) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨u, Γ⟩
    cases u
    change
      castObj (module M) (@mul_one C.Arity _ Ξ)
          ((module M).map (KleisliArityAction.lift σ 1) Γ) =
        (module M).map σ
          (castObj (module M) (@mul_one C.Arity _ Ω) Γ)
    exact map_lift_one_cast (module M) σ Γ)

/-- The empty telescope is a left unit for context extension. -/
def tensorLeftUnitor (M : ArityMod T) : tensorObj tensorUnit M ≅ M :=
  Over.isoMk (leftUnitorNatIso M) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨u, Γ⟩
    cases u
    exact (@one_mul C.Arity _ (shape M Γ)).symm)

private def rightUnitorAppIso (M : ArityMod T) (Ω : C.Arity) :
    (tensorModule M tensorUnit).obj Ω ≅ module M |>.obj Ω where
  hom := ↾fun ⟨Γ, _⟩ => Γ
  inv := ↾fun Γ => ⟨Γ, PUnit.unit⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

private def rightUnitorNatIso (M : ArityMod T) :
    tensorModule M tensorUnit ≅ module M :=
  NatIso.ofComponents (rightUnitorAppIso M) (by
    intro Ω Ξ σ
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, u⟩
    cases u
    rfl)

/-- The empty telescope is a right unit for context extension. -/
def tensorRightUnitor (M : ArityMod T) : tensorObj M tensorUnit ≅ M :=
  Over.isoMk (rightUnitorNatIso M) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, u⟩
    cases u
    exact (@mul_one C.Arity _ (shape M Γ)).symm)

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
    tensorMap (tensorMap f g) h ≫ (tensorAssociator M' N' P').hom =
      (tensorAssociator M N P).hom ≫ tensorMap f (tensorMap g h) := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
  let z : (tensorModule N P).obj (Ω ⋈ shape M Γ) :=
    ⟨Δ, castObj (module P)
      (@mul_assoc C.Arity _ Ω (shape M Γ) (shape N Δ)).symm Ξ⟩
  let y := (tensorMapNat g h).app (Ω ⋈ shape M Γ) z
  let ho := congrArg (fun Λ => Ω ⋈ Λ) (hom_shape f Γ).symm
  change
    (associatorAppIso M' N' P' Ω).hom
        ((tensorMapNat (tensorMap f g) h).app Ω ⟨⟨Γ, Δ⟩, Ξ⟩) =
      (tensorMapNat f (tensorMap g h)).app Ω
        ((associatorAppIso M N P Ω).hom ⟨⟨Γ, Δ⟩, Ξ⟩)
  dsimp only [associatorAppIso, tensorMapNat]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · apply eq_of_heq
      change HEq
        (castObj (module N') _ (g.left.app _ Δ))
        (castObj (tensorModule N' P') ho y).1
      exact HEq.trans (castObj_heq _ _ _)
        (castTensor_fst_heq N' P' ho y).symm
    · change HEq
        (castObj (module P') _
          (castObj (module P') rfl (h.left.app _ Ξ)))
        (castObj (tensorModule N' P') ho y).2
      exact HEq.trans (castObj_heq _ _ _)
        (HEq.trans (castObj_heq _ _ _)
          (HEq.trans (nat_cast_heq h.left _ _).symm
            (HEq.trans (castObj_heq _ _ _).symm
              (castTensor_snd_heq N' P' ho y).symm)))

private theorem leftUnitor_map_natural {M N : ArityMod T} (f : M ⟶ N) :
    tensorMap (𝟙 tensorUnit) f ≫ (tensorLeftUnitor N).hom =
      (tensorLeftUnitor M).hom ≫ f := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨u, Γ⟩
  cases u
  simp [tensorMap, tensorMapNat, tensorLeftUnitor, leftUnitorNatIso,
    leftUnitorAppIso, castObj]
  rfl

private theorem rightUnitor_map_natural {M N : ArityMod T} (f : M ⟶ N) :
    tensorMap f (𝟙 tensorUnit) ≫ (tensorRightUnitor N).hom =
      (tensorRightUnitor M).hom ≫ f := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, u⟩
  cases u
  rfl

private theorem tensor_pentagon (M N P Q : ArityMod T) :
    tensorMap (tensorAssociator M N P).hom (𝟙 Q) ≫
        (tensorAssociator M (tensorObj N P) Q).hom ≫
        tensorMap (𝟙 M) (tensorAssociator N P Q).hom =
      (tensorAssociator (tensorObj M N) P Q).hom ≫
        (tensorAssociator M N (tensorObj P Q)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨⟨Γ, Δ⟩, Ξ⟩, Θ⟩
  simp [tensorMap, tensorMapNat, tensorAssociator, associatorNatIso,
    associatorAppIso, castObj]
  rfl

private theorem tensor_triangle (M N : ArityMod T) :
    (tensorAssociator M tensorUnit N).hom ≫
        tensorMap (𝟙 M) (tensorLeftUnitor N).hom =
      tensorMap (tensorRightUnitor M).hom (𝟙 N) := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, u⟩, Δ⟩
  cases u
  simp [tensorMap, tensorMapNat, tensorAssociator, associatorNatIso,
    associatorAppIso, tensorLeftUnitor, leftUnitorNatIso,
    leftUnitorAppIso, tensorRightUnitor, rightUnitorNatIso,
    rightUnitorAppIso, castObj]
  rfl

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
