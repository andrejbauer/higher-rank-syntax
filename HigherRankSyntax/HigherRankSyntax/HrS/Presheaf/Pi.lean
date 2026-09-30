import HigherRankSyntax.HrS.Presheaf.Extension

/-!
# Binding

For `a` over `Γ` and `c` over `Γ` extended by `a`, the dependent presheaf `Bind a c`.
Its elements over `γ` are the families sending a map `f` into the stage of `γ` and an
element of `a` over `γ` restricted along `f` to an element of `c` over the pair,
commuting with restriction. `lam` and `unlam` are mutually inverse between the sections
of `c` and those of `Bind a c`, and binding commutes with reindexing.
-/

universe v

open CategoryTheory

namespace HrS

namespace Presheaf

variable {𝒞 : Type v} [SmallCategory 𝒞] {Γ Δ : Presheaf.{v, v + 1} 𝒞}
  (a : DependentPresheaf.{v, v + 1, v + 1} Γ)
  (c : DependentPresheaf.{v, v + 1, v + 1} (Γ.extend a))

/-- The families sending each map `f` into `I` and element of `a` over `e J f` to an
element of `c` over the pair, commuting with restriction. -/
def BindFiber {I : 𝒞} (e : (J : 𝒞) → (J ⟶ I) → Γ.obj J)
    (he : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e J f) = e K (g ≫ f)) :
    Type (v + 1) :=
  { family : (J : 𝒞) → (f : J ⟶ I) → (u : a.fiber J (e J f)) → c.fiber J ⟨e J f, u⟩ //
    ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J) (u : a.fiber J (e J f)),
      c.restrict g (extend_map g (he f g) u) (family J f u)
        = family K (g ≫ f) (a.restrict g (he f g) u) }

namespace BindFiber

/-- Families over equal points form one type. -/
theorem congr {I : 𝒞} {e₁ e₂ : (J : 𝒞) → (J ⟶ I) → Γ.obj J}
    {he₁ : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e₁ J f) = e₁ K (g ≫ f)}
    {he₂ : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e₂ J f) = e₂ K (g ≫ f)}
    (heq : ∀ (J : 𝒞) (f : J ⟶ I), e₁ J f = e₂ J f) :
  BindFiber a c e₁ he₁ = BindFiber a c e₂ he₂
  := by
  obtain rfl : e₁ = e₂ := by
    funext J f
    apply heq
  rfl

variable {a c} {I : 𝒞} {e : (J : 𝒞) → (J ⟶ I) → Γ.obj J}
  {he : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e J f) = e K (g ≫ f)}

/-- The values of a family at equal maps and heterogeneously equal elements are
heterogeneously equal. -/
theorem family_heq (w : BindFiber a c e he) {J : 𝒞} {f₁ f₂ : J ⟶ I} (hf : f₁ = f₂)
    {u₁ : a.fiber J (e J f₁)} {u₂ : a.fiber J (e J f₂)} (hu : HEq u₁ u₂) :
  HEq (w.1 J f₁ u₁) (w.1 J f₂ u₂)
  := by
  subst hf
  obtain rfl := eq_of_heq hu
  rfl

/-- A family over the points `e`, restricted along `f'`, as a family over points `e'`
with `e' J f` equal to `e J (f ≫ f')`. -/
def restrict {I' : 𝒞} {e' : (J : 𝒞) → (J ⟶ I') → Γ.obj J}
    {he' : ∀ {J K : 𝒞} (f : J ⟶ I') (g : K ⟶ J), Γ.map g (e' J f) = e' K (g ≫ f)}
    (f' : I' ⟶ I) (hee : ∀ (J : 𝒞) (f : J ⟶ I'), e J (f ≫ f') = e' J f)
    (w : BindFiber a c e he) :
    BindFiber a c e' he' where
  val J f u := c.restrict (𝟙 J) (extend_map_id _ u)
    (w.1 J (f ≫ f') (a.restrict (𝟙 J) (by rw [Γ.map_id, hee]) u))
  property f g u := by
    apply eq_of_heq
    apply HEq.trans (c.restrict_restrict_heq (𝟙 _) g (Category.comp_id g) _ _
      (extend_map g (he (f ≫ f') g) _) _)
    rw [w.2 (f ≫ f') g]
    symm
    apply HEq.trans (c.restrict_id_heq _ _)
    apply w.family_heq (by rw [Category.assoc])
    apply HEq.trans (a.restrict_id_heq _ _)
    symm
    apply a.restrict_restrict_heq (𝟙 _) g (Category.comp_id g)

/-- Restrictions of heterogeneously equal families over equal points to equal points are
heterogeneously equal. -/
theorem restrict_heq {I' : 𝒞} {e₂ : (J : 𝒞) → (J ⟶ I) → Γ.obj J}
    {he₂ : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e₂ J f) = e₂ K (g ≫ f)}
    {e' e₂' : (J : 𝒞) → (J ⟶ I') → Γ.obj J}
    {he' : ∀ {J K : 𝒞} (f : J ⟶ I') (g : K ⟶ J), Γ.map g (e' J f) = e' K (g ≫ f)}
    {he₂' : ∀ {J K : 𝒞} (f : J ⟶ I') (g : K ⟶ J), Γ.map g (e₂' J f) = e₂' K (g ≫ f)}
    (f' : I' ⟶ I) (hee : ∀ (J : 𝒞) (f : J ⟶ I'), e J (f ≫ f') = e' J f)
    (hee₂ : ∀ (J : 𝒞) (f : J ⟶ I'), e₂ J (f ≫ f') = e₂' J f)
    (h : ∀ (J : 𝒞) (f : J ⟶ I), e J f = e₂ J f)
    (h' : ∀ (J : 𝒞) (f : J ⟶ I'), e' J f = e₂' J f)
    {w : BindFiber a c e he} {w₂ : BindFiber a c e₂ he₂} (hw : HEq w w₂) :
  HEq (w.restrict (he' := he') f' hee) (w₂.restrict (he' := he₂') f' hee₂)
  := by
  obtain rfl : e = e₂ := by
    funext J f
    apply h
  obtain rfl : e' = e₂' := by
    funext J f
    apply h'
  obtain rfl := eq_of_heq hw
  rfl

/-- The values of a section of `c` at the points `e`, as a family. -/
def ofSection (t : c.Section) : BindFiber a c e he :=
  ⟨fun J f u => t.app ⟨e J f, u⟩, fun f g u => t.naturality g (extend_map g (he f g) u)⟩

/-- The families of values of a section at equal points are heterogeneously equal. -/
theorem ofSection_heq (t : c.Section) {e₂ : (J : 𝒞) → (J ⟶ I) → Γ.obj J}
    {he₂ : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Γ.map g (e₂ J f) = e₂ K (g ≫ f)}
    (h : ∀ (J : 𝒞) (f : J ⟶ I), e J f = e₂ J f) :
  HEq (ofSection (he := he) t) (ofSection (he := he₂) t)
  := by
  obtain rfl : e = e₂ := by
    funext J f
    apply h
  rfl

end BindFiber

/-- `c` bound over `a`: over `γ`, the families over the restrictions of `γ`. -/
def Bind : DependentPresheaf.{v, v + 1, v + 1} Γ where
  fiber I γ := BindFiber a c (fun J f => Γ.map f γ) (fun f g => Γ.map_map f g γ)
  restrict := fun {_ _} f' {_ _} h w =>
    w.restrict f' (fun J f => by simp only [Γ.map_comp, h])
  restrict_id := fun {_ _} _ w => by
    apply Subtype.ext
    funext J f u
    apply eq_of_heq
    apply HEq.trans (c.restrict_id_heq _ _)
    apply w.family_heq (Category.comp_id f)
    apply a.restrict_id_heq
  restrict_comp := fun {_ _ _} _ _ {_ _ _} _ _ _ w => by
    apply Subtype.ext
    funext J f u
    apply eq_of_heq
    apply HEq.trans (c.restrict_id_heq _ _)
    apply HEq.trans (c.restrict_id_heq _ _)
    symm
    apply HEq.trans (c.restrict_id_heq _ _)
    apply w.family_heq (by rw [Category.assoc])
    apply HEq.trans (a.restrict_id_heq _ _)
    symm
    apply HEq.trans (a.restrict_id_heq _ _)
    apply a.restrict_id_heq

variable {a c}

/-- A section of `c`, read as a section of `Bind a c`. -/
def lam (t : c.Section) : (Bind a c).Section where
  app γ := BindFiber.ofSection (he := fun f g => Γ.map_map f g γ) t
  naturality := fun {_ _} _ {_ _} _ => by
    apply Subtype.ext
    funext J f u
    apply t.naturality

/-- A section of `Bind a c`, read as a section of `c`. -/
def unlam (t : (Bind a c).Section) : c.Section where
  app p := c.restrict (𝟙 _) (γ := (Γ.extend a).map (𝟙 _) p)
    (by rw [(Γ.extend a).map_id, (Γ.extend a).map_id])
    ((t.app p.1).1 _ (𝟙 _) (a.restrict (𝟙 _) rfl p.2))
  naturality := fun {_ _} f {p _} h => by
    subst h
    apply eq_of_heq
    apply HEq.trans (c.restrict_restrict_heq (𝟙 _) f (Category.comp_id f) _ _
      (extend_map f (Γ.map_map (𝟙 _) f p.1) _) _)
    rw [(t.app p.1).2 (𝟙 _) f]
    symm
    apply HEq.trans (c.restrict_id_heq _ _)
    rw [← t.naturality f (γ' := ((Γ.extend a).map f p).1) rfl]
    apply HEq.trans (c.restrict_id_heq _ _)
    apply (t.app p.1).family_heq (he := fun f g => Γ.map_map f g p.1)
      (by rw [Category.id_comp, Category.comp_id])
    apply HEq.trans (a.restrict_id_heq _ _)
    apply HEq.trans (a.restrict_id_heq _ _)
    symm
    apply a.restrict_restrict_heq (𝟙 _) f (Category.comp_id f)

theorem lam_unlam (t : (Bind a c).Section) :
  lam (unlam t) = t
  := by
  apply DependentPresheaf.Section.ext
  intro I γ
  apply Subtype.ext
  funext J f u
  apply eq_of_heq
  dsimp only [lam, unlam, BindFiber.ofSection]
  apply HEq.trans (c.restrict_id_heq _ _)
  rw [← t.naturality f rfl]
  apply HEq.trans (c.restrict_id_heq _ _)
  apply (t.app γ).family_heq (he := fun f g => Γ.map_map f g γ) (Category.id_comp f)
  apply HEq.trans (a.restrict_id_heq _ _)
  apply a.restrict_id_heq

theorem unlam_lam (t : c.Section) :
  unlam (lam t) = t
  := by
  apply DependentPresheaf.Section.ext
  intro I p
  dsimp only [unlam, lam, BindFiber.ofSection]
  apply t.naturality

/-- The lift of `σ` through the extension by `a`. -/
abbrev liftAlong (σ : Hom Δ Γ) : Hom (Δ.extend (a.subst σ)) (Γ.extend a) :=
  pair (σ.comp (projection (a.subst σ))) (generic (a.subst σ))

theorem BindFiber.subst (σ : Hom Δ Γ) {I : 𝒞} {e : (J : 𝒞) → (J ⟶ I) → Δ.obj J}
    {he : ∀ {J K : 𝒞} (f : J ⟶ I) (g : K ⟶ J), Δ.map g (e J f) = e K (g ≫ f)} :
  BindFiber (a.subst σ) (c.subst (liftAlong σ)) e he
    = BindFiber a c (fun J f => σ.app (e J f)) (fun f g => by rw [σ.naturality, he])
  := rfl

variable (a c) in
/-- Binding commutes with reindexing along `σ`, the dependent presheaf over the extension
being reindexed along the lift of `σ`. -/
theorem Bind_subst (σ : Hom Δ Γ) :
  (Bind a c).subst σ = Bind (a.subst σ) (c.subst (liftAlong σ))
  := by
  apply DependentPresheaf.ext
  · intro I δ
    apply BindFiber.congr a c (he₁ := fun f g => Γ.map_map f g (σ.app δ))
      (he₂ := fun f g => σ.map_app_map f g δ)
    intro J f
    apply σ.naturality
  · intro I J f δ δ' h w w' hw
    apply BindFiber.restrict_heq f (fun J g => by rw [← h, ← σ.naturality, Γ.map_comp])
      (fun J g => by rw [← h, Δ.map_comp]) (fun J f => σ.naturality f δ)
      (fun J f => σ.naturality f δ') (he := fun f g => Γ.map_map f g (σ.app δ))
      (he₂ := fun f g => σ.map_app_map f g δ) (he' := fun f g => Γ.map_map f g (σ.app δ'))
      (he₂' := fun f g => σ.map_app_map f g δ') hw

/-- `lam` commutes with reindexing along `σ`, the section over the extension being
reindexed along the lift of `σ`. -/
theorem lam_subst (t : c.Section) (σ : Hom Δ Γ) :
  Bind_subst a c σ ▸ (lam t).subst σ = lam (t.subst (liftAlong σ))
  := by
  apply DependentPresheaf.Section.ext_heq
  intro I δ
  apply BindFiber.ofSection_heq t (he := fun f g => Γ.map_map f g (σ.app δ))
    (he₂ := fun f g => σ.map_app_map f g δ) (fun J f => σ.naturality f δ)

end Presheaf

end HrS
