import Mathlib.CategoryTheory.Category.Basic

/-!
# Presheaves and dependent presheaves

Presheaves on a small category, maps between them, dependent presheaves over a
presheaf, and their sections. A dependent presheaf restricts an element over `γ`
along `f` to an element over any point equal to `γ` restricted along `f`.
Reindexing a dependent presheaf or a section along a map precomposes with the map.
-/

universe v w w'

open CategoryTheory

namespace HrS

variable (𝒞 : Type v) [SmallCategory 𝒞]

/-- A presheaf on `𝒞`. -/
structure Presheaf where
  /-- The elements at an object. -/
  obj : 𝒞 → Type w
  /-- Restriction along a map. -/
  map : {I J : 𝒞} → (J ⟶ I) → obj I → obj J
  /-- Restriction along the identity is the identity. -/
  map_id : ∀ {I : 𝒞} (γ : obj I), map (𝟙 I) γ = γ
  /-- Restriction along `g ≫ f` is restriction along `f`, then along `g`. -/
  map_comp : ∀ {I J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J) (γ : obj I),
    map (g ≫ f) γ = map g (map f γ)

variable {𝒞}

namespace Presheaf

/-- Restriction along `f`, then along `g`, is restriction along `g ≫ f`. -/
theorem map_map (Γ : Presheaf.{v, w} 𝒞) {I J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J) (γ : Γ.obj I) :
  Γ.map g (Γ.map f γ) = Γ.map (g ≫ f) γ
  := by
  rw [Γ.map_comp]

/-- A map of presheaves from `Δ` to `Γ`. -/
structure Hom (Δ Γ : Presheaf.{v, w} 𝒞) : Type (max v (w + 1)) where
  /-- The image of an element. -/
  app : {I : 𝒞} → Δ.obj I → Γ.obj I
  /-- The map commutes with restriction. -/
  naturality : ∀ {I J : 𝒞} (f : J ⟶ I) (δ : Δ.obj I), Γ.map f (app δ) = app (Δ.map f δ)

namespace Hom

/-- Restricting along `g` the image of `δ` restricted along `f` gives the image of `δ`
restricted along `g ≫ f`. -/
theorem map_app_map {Δ Γ : Presheaf.{v, w} 𝒞} (σ : Hom Δ Γ) {I J K : 𝒞} (f : J ⟶ I)
    (g : K ⟶ J) (δ : Δ.obj I) :
  Γ.map g (σ.app (Δ.map f δ)) = σ.app (Δ.map (g ≫ f) δ)
  := by
  rw [σ.naturality, Δ.map_map]

/-- Maps agreeing on every element are equal. -/
theorem ext {Δ Γ : Presheaf.{v, w} 𝒞} {σ θ : Hom Δ Γ}
    (h : ∀ {I : 𝒞} (δ : Δ.obj I), σ.app δ = θ.app δ) :
  σ = θ
  := by
  obtain ⟨app, _⟩ := σ
  obtain ⟨app', _⟩ := θ
  obtain rfl : @app = @app' := by
    funext I δ
    apply h
  rfl

/-- The identity map. -/
def identity (Γ : Presheaf.{v, w} 𝒞) : Hom Γ Γ where
  app γ := γ
  naturality _ _ := rfl

/-- `σ` after `θ`. -/
def comp {Γ Δ Ξ : Presheaf.{v, w} 𝒞} (σ : Hom Δ Γ) (θ : Hom Ξ Δ) : Hom Ξ Γ where
  app ξ := σ.app (θ.app ξ)
  naturality f ξ := by
    rw [σ.naturality, θ.naturality]

theorem comp_assoc {Γ Δ Ξ Ψ : Presheaf.{v, w} 𝒞} (σ : Hom Δ Γ) (θ : Hom Ξ Δ)
    (κ : Hom Ψ Ξ) :
  (σ.comp θ).comp κ = σ.comp (θ.comp κ)
  := rfl

theorem identity_comp {Γ Δ : Presheaf.{v, w} 𝒞} (σ : Hom Δ Γ) :
  (identity Γ).comp σ = σ
  := rfl

theorem comp_identity {Γ Δ : Presheaf.{v, w} 𝒞} (σ : Hom Δ Γ) :
  σ.comp (identity Δ) = σ
  := rfl

end Hom

/-- The presheaf with one element at every object. -/
def terminal : Presheaf.{v, w} 𝒞 where
  obj _ := PUnit
  map _ _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- The map to the terminal presheaf. -/
def Hom.toTerminal (Γ : Presheaf.{v, w} 𝒞) : Hom Γ terminal where
  app _ := PUnit.unit
  naturality _ _ := rfl

/-- Every map to the terminal presheaf is `Hom.toTerminal`. -/
theorem Hom.toTerminal_unique {Γ : Presheaf.{v, w} 𝒞} (σ : Hom Γ terminal) :
  σ = Hom.toTerminal Γ
  := rfl

end Presheaf

/-- A dependent presheaf over `Γ`. -/
structure DependentPresheaf (Γ : Presheaf.{v, w} 𝒞) where
  /-- The elements over an element of `Γ`. -/
  fiber : (I : 𝒞) → Γ.obj I → Type w'
  /-- Restriction along `f`, to the elements over a point equal to `γ` restricted
  along `f`. -/
  restrict : {I J : 𝒞} → (f : J ⟶ I) → {γ : Γ.obj I} → {γ' : Γ.obj J} →
    Γ.map f γ = γ' → fiber I γ → fiber J γ'
  /-- Restriction along the identity is the identity. -/
  restrict_id : ∀ {I : 𝒞} {γ : Γ.obj I} (h : Γ.map (𝟙 I) γ = γ) (u : fiber I γ),
    restrict (𝟙 I) h u = u
  /-- Restriction along `g ≫ f` is restriction along `f`, then along `g`. -/
  restrict_comp : ∀ {I J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J) {γ : Γ.obj I} {γ' : Γ.obj J}
      {γ'' : Γ.obj K} (h : Γ.map f γ = γ') (h' : Γ.map g γ' = γ'')
      (h'' : Γ.map (g ≫ f) γ = γ'') (u : fiber I γ),
    restrict g h' (restrict f h u) = restrict (g ≫ f) h'' u

namespace DependentPresheaf

variable {Γ Δ Ξ : Presheaf.{v, w} 𝒞}

/-- Restrictions of one element along equal maps are heterogeneously equal. -/
theorem restrict_heq (a : DependentPresheaf.{v, w, w'} Γ) {I J : 𝒞} {f₁ f₂ : J ⟶ I}
    (hf : f₁ = f₂) {γ : Γ.obj I} {γ₁ γ₂ : Γ.obj J} (h₁ : Γ.map f₁ γ = γ₁)
    (h₂ : Γ.map f₂ γ = γ₂) (u : a.fiber I γ) :
  HEq (a.restrict f₁ h₁ u) (a.restrict f₂ h₂ u)
  := by
  subst hf h₁ h₂
  rfl

/-- Restriction along the identity is heterogeneously the identity. -/
theorem restrict_id_heq (a : DependentPresheaf.{v, w, w'} Γ) {I : 𝒞} {γ γ' : Γ.obj I}
    (h : Γ.map (𝟙 I) γ = γ') (u : a.fiber I γ) :
  HEq (a.restrict (𝟙 I) h u) u
  := by
  apply HEq.trans (a.restrict_heq rfl h (Γ.map_id γ) u)
  apply heq_of_eq
  apply a.restrict_id

/-- Restriction along `f`, then along `g`, is heterogeneously restriction along any map
equal to `g ≫ f`. -/
theorem restrict_restrict_heq (a : DependentPresheaf.{v, w, w'} Γ) {I J K : 𝒞}
    (f : J ⟶ I) (g : K ⟶ J) {k : K ⟶ I} (hk : g ≫ f = k) {γ : Γ.obj I} {γ' : Γ.obj J}
    {γ'' γ''' : Γ.obj K} (h : Γ.map f γ = γ') (h' : Γ.map g γ' = γ'')
    (h'' : Γ.map k γ = γ''') (u : a.fiber I γ) :
  HEq (a.restrict g h' (a.restrict f h u)) (a.restrict k h'' u)
  := by
  rw [a.restrict_comp f g h h' (by rw [Γ.map_comp, h, h'])]
  apply a.restrict_heq hk

/-- Dependent presheaves with equal fibers whose restrictions agree on heterogeneously
equal elements are equal. -/
theorem ext {a b : DependentPresheaf.{v, w, w'} Γ}
    (hfiber : ∀ (I : 𝒞) (γ : Γ.obj I), a.fiber I γ = b.fiber I γ)
    (hrestrict : ∀ {I J : 𝒞} (f : J ⟶ I) {γ : Γ.obj I} {γ' : Γ.obj J}
      (h : Γ.map f γ = γ') (u : a.fiber I γ) (u' : b.fiber I γ), HEq u u' →
        HEq (a.restrict f h u) (b.restrict f h u')) :
  a = b
  := by
  obtain ⟨fiber, restrict, _, _⟩ := a
  obtain ⟨fiber', restrict', _, _⟩ := b
  obtain rfl : fiber = fiber' := by
    funext I γ
    apply hfiber
  obtain rfl : @restrict = @restrict' := by
    funext I J f γ γ' h u
    apply eq_of_heq
    apply hrestrict f h u u HEq.rfl
  rfl

/-- Restricting in `Y` an element transported along `X = Y` is heterogeneously equal to
restricting it in `X`. -/
theorem restrict_cast {X Y : DependentPresheaf.{v, w, w'} Γ} (hXY : X = Y) {I J : 𝒞}
    (f : J ⟶ I) {γ : Γ.obj I} {γ' : Γ.obj J} (h : Γ.map f γ = γ') (u : X.fiber I γ) :
  HEq (Y.restrict f h (cast (congrArg (fun Z => Z.fiber I γ) hXY) u)) (X.restrict f h u)
  := by
  subst hXY
  rfl

/-- `a` reindexed along `σ`: the elements over `δ` are the elements of `a` over
`σ.app δ`. -/
def subst (a : DependentPresheaf.{v, w, w'} Γ) (σ : Presheaf.Hom Δ Γ) :
    DependentPresheaf.{v, w, w'} Δ where
  fiber I δ := a.fiber I (σ.app δ)
  restrict := fun {_ _} f {_ _} h u => a.restrict f (by rw [σ.naturality, h]) u
  restrict_id := fun _ u => a.restrict_id _ u
  restrict_comp := fun {_ _ _} f g {_ _ _} _ _ _ u => a.restrict_comp f g _ _ _ u

theorem subst_identity (a : DependentPresheaf.{v, w, w'} Γ) :
  a.subst (Presheaf.Hom.identity Γ) = a
  := rfl

theorem subst_comp (a : DependentPresheaf.{v, w, w'} Γ) (σ : Presheaf.Hom Δ Γ)
    (θ : Presheaf.Hom Ξ Δ) :
  a.subst (σ.comp θ) = (a.subst σ).subst θ
  := rfl

/-- A section of `a`: an element over every element of `Γ`, commuting with
restriction. -/
structure Section (a : DependentPresheaf.{v, w, w'} Γ) : Type (max v w (w' + 1)) where
  /-- The element over `γ`. -/
  app : {I : 𝒞} → (γ : Γ.obj I) → a.fiber I γ
  /-- Restricting the element over `γ` gives the element over the restricted point. -/
  naturality : ∀ {I J : 𝒞} (f : J ⟶ I) {γ : Γ.obj I} {γ' : Γ.obj J}
    (h : Γ.map f γ = γ'), a.restrict f h (app γ) = app γ'

namespace Section

variable {a : DependentPresheaf.{v, w, w'} Γ}

/-- Sections agreeing over every element are equal. -/
theorem ext {s t : a.Section} (h : ∀ {I : 𝒞} (γ : Γ.obj I), s.app γ = t.app γ) :
  s = t
  := by
  obtain ⟨app, _⟩ := s
  obtain ⟨app', _⟩ := t
  obtain rfl : @app = @app' := by
    funext I γ
    apply h
  rfl

/-- A section transported along `a = b` is a section of `b` agreeing heterogeneously with
it over every element. -/
theorem ext_heq {b : DependentPresheaf.{v, w, w'} Γ} (hab : a = b) {s : a.Section}
    {t : b.Section} (h : ∀ {I : 𝒞} (γ : Γ.obj I), HEq (s.app γ) (t.app γ)) :
  hab ▸ s = t
  := by
  subst hab
  apply ext
  intro I γ
  apply eq_of_heq
  apply h

/-- `t` reindexed along `σ`. -/
def subst (t : a.Section) (σ : Presheaf.Hom Δ Γ) : (a.subst σ).Section where
  app δ := t.app (σ.app δ)
  naturality := fun {_ _} f {_ _} _ => t.naturality f _

theorem subst_identity (t : a.Section) :
  t.subst (Presheaf.Hom.identity Γ) = t
  := rfl

theorem subst_comp (t : a.Section) (σ : Presheaf.Hom Δ Γ) (θ : Presheaf.Hom Ξ Δ) :
  t.subst (σ.comp θ) = (t.subst σ).subst θ
  := rfl

end Section

end DependentPresheaf

end HrS
