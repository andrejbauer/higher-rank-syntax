import HigherRankSyntax.HrS.Presheaf.Basic

/-!
# Extension

A presheaf extended by a dependent presheaf over it: the pairs of an element and
an element over it. The projection, the second components as a section, and the
pairing of a map with a section.
-/

universe v w

open CategoryTheory

namespace HrS

namespace Presheaf

variable {𝒞 : Type v} [SmallCategory 𝒞] {Γ Δ Ξ : Presheaf.{v, w} 𝒞}

/-- `Γ` extended by `a`: the pairs of an element of `Γ` and an element of `a` over
it. -/
def extend (Γ : Presheaf.{v, w} 𝒞) (a : DependentPresheaf.{v, w, w} Γ) :
    Presheaf.{v, w} 𝒞 where
  obj I := Σ γ : Γ.obj I, a.fiber I γ
  map f p := ⟨Γ.map f p.1, a.restrict f rfl p.2⟩
  map_id p := by
    apply Sigma.ext (Γ.map_id p.1)
    apply HEq.trans (a.restrict_heq rfl rfl (Γ.map_id p.1) p.2)
    apply heq_of_eq
    apply a.restrict_id
  map_comp f g p := by
    apply Sigma.ext (Γ.map_comp f g p.1)
    apply HEq.trans (a.restrict_heq rfl rfl (Γ.map_comp f g p.1) p.2)
    apply heq_of_eq
    symm
    apply a.restrict_comp

/-- Restricting a pair restricts both of its components. -/
theorem extend_map {a : DependentPresheaf.{v, w, w} Γ} {I J : 𝒞} (f : J ⟶ I)
    {γ : Γ.obj I} {γ' : Γ.obj J} (h : Γ.map f γ = γ') (u : a.fiber I γ) :
  (Γ.extend a).map f ⟨γ, u⟩ = ⟨γ', a.restrict f h u⟩
  := by
  subst h
  rfl

/-- Restricting along the identity a pair whose second component was moved along the
identity gives back the pair it came from. -/
theorem extend_map_id {a : DependentPresheaf.{v, w, w} Γ} {I : 𝒞} {γ γ' : Γ.obj I}
    (h : Γ.map (𝟙 I) γ' = γ) (u : a.fiber I γ') :
  (Γ.extend a).map (𝟙 I) ⟨γ, a.restrict (𝟙 I) h u⟩ = ⟨γ', u⟩
  := by
  subst h
  apply Eq.trans ((Γ.extend a).map_id _)
  apply (Γ.extend a).map_id ⟨γ', u⟩

/-- The projection from `Γ` extended by `a` to `Γ`. -/
def projection (a : DependentPresheaf.{v, w, w} Γ) : Hom (Γ.extend a) Γ where
  app p := p.1
  naturality _ _ := rfl

/-- The second components: a section of `a` reindexed along the projection. -/
def generic (a : DependentPresheaf.{v, w, w} Γ) : (a.subst (projection a)).Section where
  app p := p.2
  naturality := fun {_ _} _ {_ _} h => by
    subst h
    rfl

/-- `σ` paired with a section of `a` reindexed along `σ`. -/
def pair {a : DependentPresheaf.{v, w, w} Γ} (σ : Hom Δ Γ) (t : (a.subst σ).Section) :
    Hom Δ (Γ.extend a) where
  app δ := ⟨σ.app δ, t.app δ⟩
  naturality f δ := by
    apply Sigma.ext (σ.naturality f δ)
    apply HEq.trans (a.restrict_heq rfl rfl (σ.naturality f δ) (t.app δ))
    apply heq_of_eq
    apply t.naturality f rfl

theorem projection_pair {a : DependentPresheaf.{v, w, w} Γ} (σ : Hom Δ Γ)
    (t : (a.subst σ).Section) :
  (projection a).comp (pair σ t) = σ
  := rfl

theorem generic_pair {a : DependentPresheaf.{v, w, w} Γ} (σ : Hom Δ Γ)
    (t : (a.subst σ).Section) :
  HEq ((generic a).subst (pair σ t)) t
  := HEq.rfl

theorem pair_eta (a : DependentPresheaf.{v, w, w} Γ) :
  pair (projection a) (generic a) = Hom.identity (Γ.extend a)
  := rfl

theorem pair_comp {a : DependentPresheaf.{v, w, w} Γ} (σ : Hom Δ Γ)
    (t : (a.subst σ).Section) (θ : Hom Ξ Δ) :
  (pair σ t).comp θ = pair (σ.comp θ) (t.subst θ)
  := rfl

end Presheaf

end HrS
