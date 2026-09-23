import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.MorphismProperty.Representable
import HigherRankSyntax.Ctx.Telescope

/-!
# The natural model

`Tm` is the telescopes with a filling modulo 13.1, and `q : Tm ⟶ Ty` forgets the
filling.
-/

open CategoryTheory

namespace Ctx

/-- A telescope over a context class together with a filling of it. -/
def Ob.Term (X : Ob) : Type := Σ Θ : Ob.Tele X, Ob.Fill X Θ

/-- 13.1: two telescopes with fillings declare the same arity, are equal, and
their fillings agree. -/
def Ob.Term.Rel {X : Ob} : Ob.Term X → Ob.Term X → Prop
  | ⟨⟨Ω, Θ, _⟩, σ, _⟩, ⟨⟨Ω', Θ', _⟩, σ', _⟩ =>
      ∃ h : Ω = Ω', Ob.Tele.Eq X (h ▸ Θ) Θ' ∧ Ob.Fill.Eq X (h ▸ Θ) (h ▸ σ) σ'

theorem Ob.Term.Rel.refl {X : Ob} (t : Ob.Term X) : Ob.Term.Rel t t := by
  refine Quotient.inductionOn (motive := fun X => ∀ t : Ob.Term X,
    Ob.Term.Rel t t) X ?_ t
  rintro _ ⟨⟨_, _, hΘ⟩, _, hσ⟩
  exact ⟨rfl, ⟨hΘ, Wf_t.refl hΘ⟩, hσ.1, hσ.2, Eq_s.refl hσ.2⟩

theorem Ob.Term.Rel.symm {X : Ob} {t t' : Ob.Term X} (h : Ob.Term.Rel t t') :
    Ob.Term.Rel t' t := by
  refine Quotient.inductionOn (motive := fun X => ∀ t t' : Ob.Term X,
    Ob.Term.Rel t t' → Ob.Term.Rel t' t) X ?_ t t' h
  rintro Γ ⟨⟨_, _, _⟩, _, _⟩ ⟨⟨_, _, hΘ'⟩, _, hσ'⟩ ⟨rfl, ⟨hΘ, he⟩, _, hσ, hst⟩
  have hsym := Eq_t.symm Γ.wf he
  have hσ'Θ := Wf_s.ofEq_t Γ.wf hσ'.2 hsym
  refine ⟨rfl, ⟨hΘ', hsym⟩, hΘ', hσ'.2, ?_⟩
  exact Eq_s.ofEq_t Γ.wf (Eq_s.symm Γ.wf hst hΘ hσ hσ'Θ) hσ'Θ he

theorem Ob.Term.Rel.trans {X : Ob} {t t' t'' : Ob.Term X} (h : Ob.Term.Rel t t')
    (h' : Ob.Term.Rel t' t'') : Ob.Term.Rel t t'' := by
  refine Quotient.inductionOn (motive := fun X => ∀ t t' t'' : Ob.Term X,
    Ob.Term.Rel t t' → Ob.Term.Rel t' t'' → Ob.Term.Rel t t'') X ?_ t t' t'' h h'
  rintro Γ ⟨⟨_, _, _⟩, _, _⟩ ⟨⟨_, _, _⟩, _, _⟩ ⟨⟨_, _, _⟩, _, _⟩
    ⟨rfl, ⟨hΘ, he⟩, _, hσ, hst⟩ ⟨rfl, ⟨_, he'⟩, _, hσ', hst'⟩
  have hsym := Eq_t.symm Γ.wf he
  have hσ'Θ := Wf_s.ofEq_t Γ.wf hσ' hsym
  refine ⟨rfl, ⟨hΘ, Eq_t.trans Γ.wf hΘ he he'⟩, hΘ, hσ, ?_⟩
  exact Eq_s.trans Γ.wf hst (Eq_s.ofEq_t Γ.wf hst' hσ' hsym) hΘ hσ hσ'Θ

/-- 13.1 as a setoid on the telescopes with a filling. -/
def Ob.Term.setoid (X : Ob) : Setoid (Ob.Term X) where
  r := Ob.Term.Rel
  iseqv := ⟨Ob.Term.Rel.refl, Ob.Term.Rel.symm, Ob.Term.Rel.trans⟩

/-- Telescopes with fillings that agree componentwise agree. -/
theorem Ob.Term.ext {X : Ob} {Ω : C.Arity} {Θ Θ' : dTel X.arity Ω}
    {hΘ : Ob.Tele.Wf X Θ} {hΘ' : Ob.Tele.Wf X Θ'}
    {τ τ' : _root_.Subst Ω X.arity} {hτ : Ob.Fill.Wf X Θ τ}
    {hτ' : Ob.Fill.Wf X Θ' τ'} (h : Θ = Θ') (h' : τ = τ') :
    (⟨⟨Ω, Θ, hΘ⟩, τ, hτ⟩ : Ob.Term X) = ⟨⟨Ω, Θ', hΘ'⟩, τ', hτ'⟩ := by
  subst h
  subst h'
  rfl

theorem Ob.Fill.Wf.subst {X Y : Ob} (σ : Ob.Subst X Y) (t : Ob.Term Y) :
    Ob.Fill.Wf X (Ob.Tele.subst σ t.1).telescope
      (_root_.Subst.applyEach σ.1 t.2.1) := by
  refine Quotient.inductionOn₂ (motive := fun X Y => ∀ (σ : Ob.Subst X Y)
    (t : Ob.Term Y), Ob.Fill.Wf X (Ob.Tele.subst σ t.1).telescope
      (_root_.Subst.applyEach σ.1 t.2.1)) X Y ?_ σ t
  intro _ _ σ t
  exact ⟨Wf_t.subst_ambient σ.2.toWf_sub t.2.2.1,
    Wf_s.subst_ambient σ.2.toWf_sub t.2.2.2⟩

/-- 13.1: the action of a filling on a telescope with a filling. -/
def Ob.Term.subst {X Y : Ob} (σ : Ob.Subst X Y) (t : Ob.Term Y) : Ob.Term X :=
  ⟨Ob.Tele.subst σ t.1, _root_.Subst.applyEach σ.1 t.2.1, Ob.Fill.Wf.subst σ t⟩

theorem Ob.Term.Rel.subst {X Y : Ob} {σ σ' : Ob.Subst X Y} {t t' : Ob.Term Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (ht : Ob.Term.Rel t t') :
    Ob.Term.Rel (Ob.Term.subst σ t) (Ob.Term.subst σ' t') := by
  refine Quotient.inductionOn₂ (motive := fun X Y =>
    ∀ (σ σ' : Ob.Subst X Y) (t t' : Ob.Term Y), Ob.Subst.Rel X Y σ.1 σ'.1 →
      Ob.Term.Rel t t' → Ob.Term.Rel (Ob.Term.subst σ t) (Ob.Term.subst σ' t'))
    X Y ?_ σ σ' t t' hσ ht
  rintro Γ Δ σ σ' ⟨⟨_, _, _⟩, _, _⟩ ⟨⟨_, _, hΘ'⟩, _, hτ'w⟩ hs
    ⟨rfl, ⟨hΘ, he⟩, _, hτ, hst⟩
  have hτ'Θ := Wf_s.ofEq_t Δ.wf hτ'w.2 (Eq_t.symm Δ.wf he)
  have hΘσ := Wf_t.subst_ambient σ.2.toWf_sub hΘ
  have hτσ := Wf_s.subst_ambient σ.2.toWf_sub hτ
  refine ⟨rfl, ⟨hΘσ, ?tele⟩, hΘσ, hτσ, ?fill⟩
  case tele =>
    refine Eq_t.trans Γ.wf hΘσ (Eq_t.subst_ambient σ.2.toWf_sub he) ?_
    exact Eq_t.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hs.2.toEq_sub hΘ'
  case fill =>
    refine Eq_s.trans Γ.wf (Eq_s.subst_ambient σ.2.toWf_sub hst) ?_ hΘσ hτσ
      (Wf_s.subst_ambient σ.2.toWf_sub hτ'Θ)
    exact Eq_s.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hs.2.toEq_sub hΘ hτ'Θ

/-- 13.1: the presheaf of telescopes with a filling. -/
def Tm : Obᵒᵖ ⥤ Type where
  obj X := Quotient (Ob.Term.setoid X.unop)
  map {X Y} f :=
    TypeCat.ofHom (Quotient.map₂ (sa := Ob.Subst.setoid Y.unop X.unop)
      (sb := Ob.Term.setoid X.unop) (sc := Ob.Term.setoid Y.unop)
      Ob.Term.subst (fun _ _ hσ _ _ ht => Ob.Term.Rel.subst hσ ht) f.unop)
  map_id X := by
    ext t
    refine Quotient.inductionOn t ?_
    rintro ⟨⟨_, Θ₀, _⟩, τ₀, _⟩
    refine congrArg (Quotient.mk (Ob.Term.setoid X.unop))
      (Ob.Term.ext (dTel.actBase_id Θ₀) ?_)
    funext Λ i
    exact act_id (Ob.arity X.unop) Λ (τ₀ i)
  map_comp {X Y Z} f g := by
    obtain ⟨u⟩ := f
    obtain ⟨v⟩ := g
    ext t
    refine Quotient.inductionOn₃ u v t ?_
    rintro σ θ ⟨⟨_, Θ₀, _⟩, τ₀, _⟩
    refine congrArg (Quotient.mk (Ob.Term.setoid Z.unop))
      (Ob.Term.ext (dTel.actBase_comp σ.1 θ.1 Θ₀) ?_)
    funext Λ i
    exact act_comp (Γ := 1) σ.1 θ.1 Λ (τ₀ i)

theorem Ob.Term.Rel.tele {X : Ob} {t t' : Ob.Term X} (h : Ob.Term.Rel t t') :
    Ob.Tele.Rel t.1 t'.1 := by
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t'
  obtain ⟨rfl, hTele, _⟩ := h
  exact ⟨rfl, hTele⟩

/-- The class of the telescope carried by a telescope with a filling. -/
def Ob.Term.tele {X : Ob} :
    Quotient (Ob.Term.setoid X) → Quotient (Ob.Tele.setoid X) :=
  Quotient.map Sigma.fst (fun _ _ h => Ob.Term.Rel.tele h)

/-- 13.1: the projection forgetting the filling. -/
def q : Tm ⟶ Ty where
  app X := TypeCat.ofHom (Ob.Term.tele (X := X.unop))
  naturality {X Y} f := by
    obtain ⟨u⟩ := f
    ext t
    refine Quotient.inductionOn₂ u t ?_
    intro _ _
    rfl

/-- 13.1 on the telescopes with a filling lying over a fixed telescope. -/
def Ob.Term.fibreSetoid {X : Ob} (Θ : Ob.Tele X) :
    Setoid { s : Ob.Term X // Ob.Tele.Rel s.1 Θ } where
  r a b := Ob.Term.Rel a.1 b.1
  iseqv := ⟨fun a => Ob.Term.Rel.refl a.1, Ob.Term.Rel.symm, Ob.Term.Rel.trans⟩

theorem Ob.Term.fibre_map {X : Ob} {Θ : Ob.Tele X}
    (a b : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }) (h : Ob.Term.Rel a.1 b.1) :
    Ob.Fill.Rel (Ob.Fill.ofRel a.2 a.1.2) (Ob.Fill.ofRel b.2 b.1.2) := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (a b : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }), Ob.Term.Rel a.1 b.1 →
      Ob.Fill.Rel (Ob.Fill.ofRel a.2 a.1.2) (Ob.Fill.ofRel b.2 b.1.2))
    X ?_ Θ a b h
  rintro Ξ ⟨_, _, _⟩ ⟨⟨⟨_, _, _⟩, τ, hτ⟩, ⟨rfl, hwfa, heqa⟩⟩
    ⟨⟨⟨_, _, _⟩, τ', hτ'⟩, ⟨rfl, _, _⟩⟩ ⟨_, ⟨_, _⟩, _, _, hst⟩
  exact ⟨Wf_t.ofEq_t Ξ.wf hwfa heqa, Wf_s.ofEq_t Ξ.wf hτ.2 heqa,
    Eq_s.ofEq_t Ξ.wf hst hτ.2 heqa⟩

theorem Ob.Term.fibre_comap {X : Ob} {Θ : Ob.Tele X} (τ τ' : Ob.Fill X Θ)
    (h : Ob.Fill.Rel τ τ') :
    Ob.Term.Rel (⟨Θ, τ⟩ : Ob.Term X) ⟨Θ, τ'⟩ := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (τ τ' : Ob.Fill X Θ), Ob.Fill.Rel τ τ' →
      Ob.Term.Rel (⟨Θ, τ⟩ : Ob.Term X) ⟨Θ, τ'⟩) X ?_ Θ τ τ' h
  rintro Ξ ⟨_, _, hΘ⟩ τ τ' h
  exact ⟨rfl, ⟨hΘ, Wf_t.refl hΘ⟩, h⟩

theorem Ob.Term.fibre_left {X : Ob} {Θ : Ob.Tele X}
    (s : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }) :
    Ob.Term.Rel (⟨Θ, Ob.Fill.ofRel s.2 s.1.2⟩ : Ob.Term X) s.1 := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (s : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }),
      Ob.Term.Rel (⟨Θ, Ob.Fill.ofRel s.2 s.1.2⟩ : Ob.Term X) s.1) X ?_ Θ s
  rintro Ξ ⟨_, _, hΘ⟩ ⟨⟨⟨_, _, _⟩, τ, hτ⟩, ⟨rfl, _, heq⟩⟩
  exact ⟨rfl, ⟨hΘ, Eq_t.symm Ξ.wf heq⟩, hΘ, Wf_s.ofEq_t Ξ.wf hτ.2 heq,
    Eq_s.refl (Wf_s.ofEq_t Ξ.wf hτ.2 heq)⟩

/-- 13.2: the telescopes with a filling lying over a telescope are its
fillings. -/
def Ob.Term.fibreEquiv {X : Ob} (Θ : Ob.Tele X) :
    Quotient (Ob.Term.fibreSetoid Θ) ≃ Quotient (Ob.Fill.setoid Θ) where
  toFun := Quotient.map (fun s => Ob.Fill.ofRel s.2 s.1.2) Ob.Term.fibre_map
  invFun := Quotient.map (fun τ => ⟨⟨Θ, τ⟩, Ob.Tele.Rel.refl Θ⟩)
    (fun _ _ h => Ob.Term.fibre_comap _ _ h)
  left_inv := by
    refine Quotient.ind ?_
    intro s
    exact Quotient.sound (Ob.Term.fibre_left s)
  right_inv := by
    refine Quotient.ind ?_
    intro _
    rfl

/-- A telescope with a filling lies over a telescope exactly when its class
does. -/
theorem Ob.Term.tele_eq_iff {X : Ob} {Θ : Ob.Tele X} (s : Ob.Term X) :
    Ob.Tele.Rel s.1 Θ ↔ Ob.Term.tele ⟦s⟧ = ⟦Θ⟧ :=
  ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- 13.2: the fibre of `q` over a telescope is the fillings of that
telescope. -/
def Ob.fillEquiv {X : Ob} (Θ : Ob.Tele X) :
    { t : Quotient (Ob.Term.setoid X) // Ob.Term.tele t = ⟦Θ⟧ }
      ≃ Quotient (Ob.Fill.setoid Θ) :=
  (Equiv.subtypeQuotientEquivQuotientSubtype (s₂ := Ob.Term.fibreSetoid Θ)
      (fun s => Ob.Tele.Rel s.1 Θ) (fun t => Ob.Term.tele t = ⟦Θ⟧)
      Ob.Term.tele_eq_iff (fun _ _ => Iff.rfl)).trans
    (Ob.Term.fibreEquiv Θ)

/-- The weakening of an extension splits into the two weakenings. -/
theorem weaken_extend (Ξ Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    dTel.rename (Renaming.fromUnit Ξ.arity) (Γ.ambient ⋈ Θ.telescope)
      = dTel.concatenate (dTel.rename (Renaming.fromUnit Ξ.arity) Γ.ambient)
          (dTel.rename (Renaming.inr Ξ.arity Γ.arity) Θ.telescope) := by
  refine (dTel.rename_concatenate _ Γ.ambient Θ.telescope).trans ?_
  exact congrArg (fun ρ => dTel.concatenate
    (dTel.rename (Renaming.fromUnit Ξ.arity) Γ.ambient) (dTel.rename ρ Θ.telescope))
    (Renaming.fromUnit_extend Ξ.arity Γ.arity)

/-- The first half of a filling of an extension fills the base. -/
theorem Ob.Subst.Wf.left {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (Ctx.extend Γ Θ)) :
    Ob.Subst.Wf X Γ.toOb (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w)) := by
  refine Quotient.inductionOn (motive := fun X =>
    ∀ κ : Ob.Subst X (Ctx.extend Γ Θ),
      Ob.Subst.Wf X Γ.toOb (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w))) X ?_ κ
  intro Ξ κ
  exact Wf_s.concatenate_left
    (Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T κ.1) (weaken_extend Ξ Γ Θ)) κ.2)

/-- The second half of a filling of an extension fills the telescope. -/
theorem Ob.Fill.Wf.right {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (Ctx.extend Γ Θ)) :
    Ob.Fill.Wf X
        (dTel.actBase (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w)) Θ.telescope)
        (fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z)) := by
  refine Quotient.inductionOn (motive := fun X =>
    ∀ κ : Ob.Subst X (Ctx.extend Γ Θ), Ob.Fill.Wf X
      (dTel.actBase (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w)) Θ.telescope)
      (fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z))) X ?_ κ
  intro Ξ κ
  have hcat := Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T κ.1)
    (weaken_extend Ξ Γ Θ)) κ.2
  refine ⟨Wf_t.subst_ambient (Wf_s.toWf_sub (Wf_s.concatenate_left hcat)) Θ.wf, ?_⟩
  exact Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T
    (fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z)))
    (dTel.instantiate_weaken _ Θ.telescope)) (Wf_s.concatenate_right hcat)

/-- A filling of the base and a filling of the telescope pair to a filling of the
extension. -/
theorem Ob.Subst.Wf.pair {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (σ : Ob.Subst X Γ.toOb) (τ : _root_.Subst Θ.arity X.arity)
    (hτ : Ob.Fill.Wf X (dTel.actBase σ.1 Θ.telescope) τ) :
    Ob.Subst.Wf X (Ctx.extend Γ Θ) (Subst.copair σ.1 τ) := by
  refine Quotient.inductionOn (motive := fun X =>
    ∀ (σ : Ob.Subst X Γ.toOb) (τ : _root_.Subst Θ.arity (Ob.arity X)),
      Ob.Fill.Wf X (dTel.actBase σ.1 Θ.telescope) τ →
        Ob.Subst.Wf X (Ctx.extend Γ Θ) (Subst.copair σ.1 τ)) X ?_ σ τ hτ
  intro Ξ σ τ hτ
  refine Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T (Subst.copair σ.1 τ))
    (weaken_extend Ξ Γ Θ).symm) ?_
  refine Wf_s.concatenate σ.2 ?_
  exact Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T τ)
    (dTel.instantiate_weaken σ.1 Θ.telescope).symm) hτ.2

/-- The base half of a filling of an extension. -/
def Ob.Subst.left {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (Ctx.extend Γ Θ)) : Ob.Subst X Γ.toOb :=
  ⟨fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w), Ob.Subst.Wf.left κ⟩

/-- The telescope half of a filling of an extension. -/
def Ob.Subst.right {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (Ctx.extend Γ Θ)) : _root_.Subst Θ.arity X.arity :=
  fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z)

/-- 13.2: a filling of an extension is a filling of the base together with a
filling of the telescope it carries. -/
def splitEquiv (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Ob.Subst X (Ctx.extend Γ Θ) ≃
      { p : Ob.Subst X Γ.toOb × _root_.Subst Θ.arity X.arity //
          Ob.Fill.Wf X (dTel.actBase p.1.1 Θ.telescope) p.2 } where
  toFun κ := ⟨(κ.left, κ.right), Ob.Fill.Wf.right κ⟩
  invFun p := ⟨Subst.copair p.1.1.1 p.1.2, Ob.Subst.Wf.pair p.1.1 p.1.2 p.2⟩
  left_inv κ := Subtype.ext (Subst.copair_eta κ.1)
  right_inv p := by
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
    · exact Subst.copair_left p.1.1.1 p.1.2
    · exact Subst.copair_right p.1.1.1 p.1.2

/-- The splitting respects 9.2 on both sides. -/
theorem splitEquiv_rel (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (κ κ' : Ob.Subst X (Ctx.extend Γ Θ)) :
    Ob.Subst.Rel X (Ctx.extend Γ Θ) κ.1 κ'.1
      ↔ Ob.Subst.Rel X Γ.toOb κ.left.1 κ'.left.1 ∧
          Ob.Fill.Eq X (dTel.actBase κ.left.1 Θ.telescope) κ.right κ'.right := by
  refine Quotient.inductionOn (motive := fun X =>
    ∀ κ κ' : Ob.Subst X (Ctx.extend Γ Θ),
      (Ob.Subst.Rel X (Ctx.extend Γ Θ) κ.1 κ'.1
        ↔ Ob.Subst.Rel X Γ.toOb κ.left.1 κ'.left.1 ∧
            Ob.Fill.Eq X (dTel.actBase κ.left.1 Θ.telescope) κ.right κ'.right))
    X ?_ κ κ'
  intro Ξ κ κ'
  constructor
  · rintro ⟨hwf, heq⟩
    have hwf' := Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T κ.1)
      (weaken_extend Ξ Γ Θ)) hwf
    have heq' := Eq.mp (congrArg (fun T => Eq_s Ξ.ambient T κ.1 κ'.1)
      (weaken_extend Ξ Γ Θ)) heq
    refine ⟨⟨Wf_s.concatenate_left hwf', Eq_s.concatenate_left heq'⟩,
      Wf_t.subst_ambient (Wf_s.toWf_sub (Wf_s.concatenate_left hwf')) Θ.wf, ?_, ?_⟩
    · exact Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T κ.right)
        (dTel.instantiate_weaken _ Θ.telescope)) (Wf_s.concatenate_right hwf')
    · exact Eq.mp (congrArg (fun T => Eq_s Ξ.ambient T κ.right κ'.right)
        (dTel.instantiate_weaken _ Θ.telescope)) (Eq_s.concatenate_right heq')
  · rintro ⟨⟨hσ, hst⟩, _, hτ, htt⟩
    have hτ' := Eq.mp (congrArg (fun T => Wf_s Ξ.ambient T κ.right)
      (dTel.instantiate_weaken κ.left.1 Θ.telescope).symm) hτ
    have htt' := Eq.mp (congrArg (fun T => Eq_s Ξ.ambient T κ.right κ'.right)
      (dTel.instantiate_weaken κ.left.1 Θ.telescope).symm) htt
    refine ⟨?_, ?_⟩
    · refine Eq.mp (congrArg₂ (fun (T : dTel Ξ.arity (Γ.arity ⋈ Θ.arity)) s => Wf_s Ξ.ambient T s)
        (weaken_extend Ξ Γ Θ).symm (Subst.copair_eta κ.1)) ?_
      exact Wf_s.concatenate hσ hτ'
    · refine Eq.mp (congrArg₂ (fun (T : dTel Ξ.arity (Γ.arity ⋈ Θ.arity))
        (p : _root_.Subst (Γ.arity ⋈ Θ.arity) Ξ.arity ×
             _root_.Subst (Γ.arity ⋈ Θ.arity) Ξ.arity) => Eq_s Ξ.ambient T p.1 p.2)
        (weaken_extend Ξ Γ Θ).symm
        (congrArg₂ Prod.mk (Subst.copair_eta κ.1) (Subst.copair_eta κ'.1))) ?_
      exact Eq_s.concatenate hst htt'

section

variable {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}

/-- A telescope with a filling, paired with a filling of the base it lies
over. -/
def Ob.Pair (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : Type :=
  { p : Ob.Term X × Ob.Subst X Γ.toOb //
      Ob.Tele.Rel p.1.1 (Ob.Tele.subst p.2 Θ) }

/-- 13.1 and 9.2 componentwise on such pairs. -/
def Ob.Pair.setoid (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Setoid (Ob.Pair X Γ Θ) where
  r a b := Ob.Term.Rel a.1.1 b.1.1 ∧ Ob.Subst.Rel X Γ.toOb a.1.2.1 b.1.2.1
  iseqv := ⟨fun a => ⟨Ob.Term.Rel.refl a.1.1, Ob.Subst.Rel.refl a.1.2⟩,
    fun h => ⟨Ob.Term.Rel.symm h.1, Ob.Subst.Rel.symm h.2⟩,
    fun h h' => ⟨Ob.Term.Rel.trans h.1 h'.1, Ob.Subst.Rel.trans h.2 h'.2⟩⟩

/-- The filling of the telescope carried by such a pair. -/
def Ob.Pair.fill {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb} (a : Ob.Pair X Γ Θ) :
    Ob.Fill X (Ob.Tele.subst a.1.2 Θ) :=
  Ob.Fill.ofRel a.2 a.1.1.2

/-- The filling of the extension determined by such a pair. -/
def Ob.Pair.subst {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb} (a : Ob.Pair X Γ Θ) :
    Ob.Subst X (Ctx.extend Γ Θ) :=
  (Ctx.splitEquiv X Γ Θ).symm ⟨(a.1.2, a.fill.1), a.fill.2⟩

/-- The pair determined by a filling of the extension. -/
def Ob.Subst.toPair {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (Ctx.extend Γ Θ)) : Ob.Pair X Γ Θ :=
  ⟨(⟨Ob.Tele.subst κ.left Θ, κ.right, Ob.Fill.Wf.right κ⟩, κ.left),
    Ob.Tele.Rel.refl _⟩


theorem Ob.Pair.subst_left (a : Ob.Pair X Γ Θ) : a.subst.left = a.1.2 :=
  Subtype.ext (Subst.copair_left a.1.2.1 a.fill.1)

theorem Ob.Pair.subst_right (a : Ob.Pair X Γ Θ) : a.subst.right = a.fill.1 :=
  Subst.copair_right a.1.2.1 a.fill.1

theorem Ob.Subst.toPair_subst (κ : Ob.Subst X (Ctx.extend Γ Θ)) :
    κ.toPair.subst = κ :=
  (Ctx.splitEquiv X Γ Θ).left_inv κ

theorem Ob.Pair.subst_toPair (a : Ob.Pair X Γ Θ) :
    Ob.Term.Rel a.subst.toPair.1.1 a.1.1 ∧
      Ob.Subst.Rel X Γ.toOb a.subst.toPair.1.2.1 a.1.2.1 := by
  refine Quotient.inductionOn (motive := fun X => ∀ a : Ob.Pair X Γ Θ,
    Ob.Term.Rel a.subst.toPair.1.1 a.1.1 ∧
      Ob.Subst.Rel X Γ.toOb a.subst.toPair.1.2.1 a.1.2.1) X ?_ a
  rintro Ξ ⟨⟨⟨⟨_, _, _⟩, τ, hτ⟩, σ⟩, ⟨rfl, hwf, heq⟩⟩
  have hl := Subst.copair_left σ.1 τ
  have hr := Subst.copair_right σ.1 τ
  have hwfσ := Wf_t.ofEq_t Ξ.wf hwf heq
  have hτσ := Wf_s.ofEq_t Ξ.wf hτ.2 heq
  refine ⟨⟨rfl, ?tele, ?fill⟩, ?base⟩
  case tele =>
    refine Eq.mp (congrArg (fun s => Ob.Tele.Eq (Quotient.mk Ctx.setoid Ξ)
      (dTel.actBase s Θ.telescope) _) hl.symm) ?_
    exact ⟨hwfσ, Eq_t.symm Ξ.wf heq⟩
  case fill =>
    refine Eq.mp (congrArg₂ (fun s (t : _root_.Subst Θ.arity Ξ.arity) =>
      Ob.Fill.Eq (Quotient.mk Ctx.setoid Ξ)
        (dTel.actBase s Θ.telescope) t τ) hl.symm hr.symm) ?_
    exact ⟨hwfσ, hτσ, Eq_s.refl hτσ⟩
  case base =>
    refine Eq.mp (congrArg (fun s => Ob.Subst.Rel (Quotient.mk Ctx.setoid Ξ)
      Γ.toOb s σ.1) hl.symm) ?_
    exact Ob.Subst.Rel.refl σ

theorem Ob.Pair.subst_congr (a b : Ob.Pair X Γ Θ)
    (h : Ob.Term.Rel a.1.1 b.1.1 ∧ Ob.Subst.Rel X Γ.toOb a.1.2.1 b.1.2.1) :
    Ob.Subst.Rel X (Ctx.extend Γ Θ) a.subst.1 b.subst.1 := by
  refine Quotient.inductionOn (motive := fun X => ∀ (a b : Ob.Pair X Γ Θ),
    (Ob.Term.Rel a.1.1 b.1.1 ∧ Ob.Subst.Rel X Γ.toOb a.1.2.1 b.1.2.1) →
      Ob.Subst.Rel X (Ctx.extend Γ Θ) a.subst.1 b.subst.1) X ?_ a b h
  rintro Ξ ⟨⟨⟨⟨_, _, _⟩, τ, hτ⟩, σ⟩, ⟨rfl, hwfa, heqa⟩⟩
    ⟨⟨⟨⟨_, _, _⟩, τ', hτ'⟩, σ'⟩, ⟨rfl, _, _⟩⟩ ⟨⟨_, ⟨_, _⟩, _, _, hst⟩, hσσ⟩
  refine (Ctx.splitEquiv_rel _ Γ Θ _ _).mpr ⟨?base, ?fill⟩
  case base =>
    exact Eq.mp (congrArg₂ (fun s t => Ob.Subst.Rel (Quotient.mk Ctx.setoid Ξ)
      Γ.toOb s t) (Subst.copair_left σ.1 τ).symm
      (Subst.copair_left σ'.1 τ').symm) hσσ
  case fill =>
    refine Eq.mp (congrArg (fun s => Ob.Fill.Eq (Quotient.mk Ctx.setoid Ξ)
      (dTel.actBase s Θ.telescope) _ _) (Subst.copair_left σ.1 τ).symm) ?_
    refine Eq.mp (congrArg₂ (fun (s t : _root_.Subst Θ.arity Ξ.arity) =>
      Ob.Fill.Eq (Quotient.mk Ctx.setoid Ξ)
        (dTel.actBase σ.1 Θ.telescope) s t)
      (Subst.copair_right σ.1 τ).symm (Subst.copair_right σ'.1 τ').symm) ?_
    exact ⟨Wf_t.ofEq_t Ξ.wf hwfa heqa, Wf_s.ofEq_t Ξ.wf hτ.2 heqa,
      Eq_s.ofEq_t Ξ.wf hst hτ.2 heqa⟩

theorem Ob.Subst.toPair_congr (κ κ' : Ob.Subst X (Ctx.extend Γ Θ))
    (h : Ob.Subst.Rel X (Ctx.extend Γ Θ) κ.1 κ'.1) :
    Ob.Term.Rel κ.toPair.1.1 κ'.toPair.1.1 ∧
      Ob.Subst.Rel X Γ.toOb κ.toPair.1.2.1 κ'.toPair.1.2.1 := by
  obtain ⟨hσ, hfill⟩ := (Ctx.splitEquiv_rel X Γ Θ κ κ').mp h
  obtain ⟨_, htele⟩ := Ob.Tele.Rel.subst hσ (Ob.Tele.Rel.refl Θ)
  exact ⟨⟨rfl, htele, hfill⟩, hσ⟩

/-- 13.2: a filling of an extension is a telescope with a filling lying over the
telescope, paired with a filling of the base. -/
def pairEquiv (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Quotient (Ob.Pair.setoid X Γ Θ) ≃ (X ⟶ Ctx.extend Γ Θ) where
  toFun := Quotient.map Ob.Pair.subst (fun _ _ h => Ob.Pair.subst_congr _ _ h)
  invFun := Quotient.map Ob.Subst.toPair (fun _ _ h => Ob.Subst.toPair_congr _ _ h)
  left_inv := by
    refine Quotient.ind ?_
    intro a
    exact Quotient.sound (Ob.Pair.subst_toPair a)
  right_inv := by
    refine Quotient.ind ?_
    intro κ
    exact congrArg (Quotient.mk (Ob.Subst.setoid X (Ctx.extend Γ Θ)))
      (Ob.Subst.toPair_subst κ)

end

section

variable (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)

/-- 13.2: the telescope of an extension read over the extension. -/
def genericTele : Ob.Tele (Ctx.extend Γ Θ) :=
  ⟨Θ.arity, _, Wf_t.weaken (Ambient.Renaming.weaken Γ.ambient Θ.telescope) Θ.wf⟩

theorem generic_wf : Ob.Fill.Wf (Ctx.extend Γ Θ) (genericTele Γ Θ).telescope
    (_root_.Subst.instId Γ.arity Θ.arity) :=
  ⟨(genericTele Γ Θ).wf, Wf_s.eta Γ.ambient Θ.telescope Θ.wf⟩

/-- 13.2: the generic telescope with a filling, each slot filled by itself. -/
def generic : Ob.Term (Ctx.extend Γ Θ) :=
  ⟨genericTele Γ Θ, _root_.Subst.instId Γ.arity Θ.arity, generic_wf Γ Θ⟩

theorem Ty_map_mk {X : Ob} (σ : Ob.Subst X Γ.toOb) :
    Ty.map (Quiver.Hom.op (Quotient.mk (Ob.Subst.setoid X Γ.toOb) σ :
        X ⟶ Γ.toOb)) ⟦Θ⟧ = ⟦Ob.Tele.subst σ Θ⟧ := rfl

theorem generic_tele :
    Ob.Term.tele (Quotient.mk (Ob.Term.setoid (Ctx.extend Γ Θ)) (generic Γ Θ))
      = Ty.map (Ctx.projection Γ Θ).op ⟦Θ⟧ := by
  have h : dTel.rename (Renaming.inl Γ.arity Θ.arity) Θ.telescope
      = dTel.actBase (_root_.Subst.ofRenaming (Renaming.inl Γ.arity Θ.arity))
          Θ.telescope :=
    (dTel.actBase_ofRenaming (Renaming.inl Γ.arity Θ.arity) Θ.telescope).symm
  refine Quotient.sound ⟨rfl, ?_⟩
  refine Eq.mp (congrArg (fun T => Ob.Tele.Eq (Ctx.extend Γ Θ)
    (dTel.rename (Renaming.inl Γ.arity Θ.arity) Θ.telescope) T) h) ?_
  exact ⟨(genericTele Γ Θ).wf, Wf_t.refl (genericTele Γ Θ).wf⟩

end

section

variable (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)

/-- Lying over `Θ`, as a predicate on classes of pairs. -/
def fibrePred :
    Quotient ((Ob.Term.setoid X).prod (Ob.Subst.setoid X Γ.toOb)) → Prop :=
  Quotient.lift (fun s => Ob.Tele.Rel s.1.1 (Ob.Tele.subst s.2 Θ))
    (by
      rintro ⟨s, σ⟩ ⟨s', σ'⟩ ⟨hs, hσ⟩
      refine propext ⟨fun h => ?_, fun h => ?_⟩
      · refine Ob.Tele.Rel.trans (Ob.Tele.Rel.symm (Ob.Term.Rel.tele hs)) ?_
        exact Ob.Tele.Rel.trans h (Ob.Tele.Rel.subst hσ (Ob.Tele.Rel.refl Θ))
      · refine Ob.Tele.Rel.trans (Ob.Term.Rel.tele hs) ?_
        refine Ob.Tele.Rel.trans h ?_
        exact Ob.Tele.Rel.symm (Ob.Tele.Rel.subst hσ (Ob.Tele.Rel.refl Θ)))

theorem fibrePred_iff (p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb)) :
    (Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧)
      ↔ fibrePred X Γ Θ (Setoid.prodQuotientEquiv _ _ p) := by
  obtain ⟨t, s⟩ := p
  refine Quotient.inductionOn₂ t s ?_
  intro a b
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- 13.2: a telescope with a filling lying over `Θ[σ]`, paired with `σ`. -/
def fibreEquiv :
    { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }
      ≃ Quotient (Ob.Pair.setoid X Γ Θ) :=
  (Equiv.subtypeEquiv (Setoid.prodQuotientEquiv _ _)
      (fibrePred_iff X Γ Θ)).trans
    (Equiv.subtypeQuotientEquivQuotientSubtype (s₂ := Ob.Pair.setoid X Γ Θ)
      (fun s : Ob.Term X × Ob.Subst X Γ.toOb =>
        Ob.Tele.Rel s.1.1 (Ob.Tele.subst s.2 Θ)) (fibrePred X Γ Θ)
      (fun _ => Iff.rfl) (fun _ _ => Iff.rfl))

/-- 13.2: the hom-set bijection, pointwise. -/
def homEquiv :
    { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }
      ≃ (X ⟶ Ctx.extend Γ Θ) :=
  (fibreEquiv X Γ Θ).trans (pairEquiv X Γ Θ)

end

/-- 13.2: the hom-set bijection is natural. -/
theorem homEquiv_naturality {X Y : Ob} (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (t : Tm.obj (Opposite.op X)) (s : X ⟶ Γ.toOb) (g : Y ⟶ X)
    (hp : Ob.Term.tele t = Ty.map s.op ⟦Θ⟧)
    (hq : Ob.Term.tele (Tm.map g.op t) = Ty.map (g ≫ s).op ⟦Θ⟧) :
    homEquiv Y Γ Θ ⟨(Tm.map g.op t, g ≫ s), hq⟩
      = g ≫ homEquiv X Γ Θ ⟨(t, s), hp⟩ := by
  refine Quotient.inductionOn₃ (motive := fun t s g =>
    ∀ (hp : Ob.Term.tele t
          = Ty.map (Quiver.Hom.op (s : X ⟶ Γ.toOb)) ⟦Θ⟧)
      (hq : Ob.Term.tele (Tm.map (Quiver.Hom.op (g : Y ⟶ X)) t)
          = Ty.map (Quiver.Hom.op ((g : Y ⟶ X) ≫ (s : X ⟶ Γ.toOb))) ⟦Θ⟧),
      homEquiv Y Γ Θ ⟨(Tm.map (Quiver.Hom.op (g : Y ⟶ X)) t,
          (g : Y ⟶ X) ≫ (s : X ⟶ Γ.toOb)), hq⟩
        = (g : Y ⟶ X) ≫ homEquiv X Γ Θ ⟨(t, s), hp⟩) t s g ?_ hp hq
  rintro ⟨⟨_, _, _⟩, τ, hτ⟩ b c hp hq
  obtain ⟨rfl, _⟩ := Quotient.exact hp
  refine congrArg (Quotient.mk (Ob.Subst.setoid Y (Ctx.extend Γ Θ))) ?_
  refine Subtype.ext ?_
  exact (Subst.applyEach_copair c.1 b.1 τ).symm

theorem Ob.Tele.subst_comp {X Y Z : Ob} (f : Ob.Subst X Y) (g : Ob.Subst Y Z)
    (Θ : Ob.Tele Z) :
    Ob.Tele.subst (Ob.Subst.comp f g) Θ = Ob.Tele.subst f (Ob.Tele.subst g Θ) :=
  Ob.Tele.ext (dTel.actBase_comp g.1 f.1 Θ.telescope)

/-- The constraint of 13.2 is stable under restriction. -/
theorem tele_map {X Y : Ob} (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (t : Tm.obj (Opposite.op X)) (s : X ⟶ Γ.toOb) (g : Y ⟶ X)
    (h : Ob.Term.tele t = Ty.map s.op ⟦Θ⟧) :
    Ob.Term.tele (Tm.map g.op t) = Ty.map (g ≫ s).op ⟦Θ⟧ := by
  refine Quotient.inductionOn₃ (motive := fun t s g =>
    Ob.Term.tele t = Ty.map (Quiver.Hom.op (s : X ⟶ Γ.toOb)) ⟦Θ⟧ →
      Ob.Term.tele (Tm.map (Quiver.Hom.op (g : Y ⟶ X)) t)
        = Ty.map (Quiver.Hom.op ((g : Y ⟶ X) ≫ (s : X ⟶ Γ.toOb))) ⟦Θ⟧)
    t s g ?_ h
  intro a b c h
  refine Quotient.sound ?_
  refine Eq.mp (congrArg (fun T => Ob.Tele.Rel (Ob.Tele.subst c a.1) T)
    (Ob.Tele.subst_comp c b Θ).symm) ?_
  exact Ob.Tele.Rel.subst (Ob.Subst.Rel.refl c) (Quotient.exact h)

/-- 13.2: the bijection recovers the filling of the base. -/
theorem homEquiv_projection (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (p : { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }) :
    homEquiv X Γ Θ p ≫ Ctx.projection Γ Θ = p.1.2 := by
  obtain ⟨⟨t, s⟩, hp⟩ := p
  refine Quotient.inductionOn₂ (motive := fun t s =>
    ∀ hp : Ob.Term.tele t = Ty.map (Quiver.Hom.op (s : X ⟶ Γ.toOb)) ⟦Θ⟧,
      homEquiv X Γ Θ ⟨(t, s), hp⟩ ≫ Ctx.projection Γ Θ
        = (s : X ⟶ Γ.toOb)) t s ?_ hp
  intro a b hp
  refine congrArg (Quotient.mk (Ob.Subst.setoid X Γ.toOb)) (Subtype.ext ?_)
  funext Λ w
  exact (act_η _ Λ (C.inl w)).trans (Subst.copair_inl b.1 _ w)

/-- Induction on a context class through its representatives. -/
theorem Ob.ind {motive : Ob → Prop} (h : ∀ Γ : Ctx, motive Γ.toOb) (X : Ob) :
    motive X :=
  Quotient.ind h X

/-- 13.2: the bijection recovers the telescope with its filling. -/
theorem homEquiv_generic (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (p : { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }) :
    Tm.map (homEquiv X Γ Θ p).op ⟦Ctx.generic Γ Θ⟧ = p.1.1 := by
  obtain ⟨⟨t, s⟩, hp⟩ := p
  refine Ob.ind (motive := fun X =>
    ∀ (t : Tm.obj (Opposite.op X)) (s : X ⟶ Γ.toOb)
      (hp : Ob.Term.tele t = Ty.map (Quiver.Hom.op s) ⟦Θ⟧),
      Tm.map (Quiver.Hom.op (homEquiv X Γ Θ ⟨(t, s), hp⟩))
          ⟦Ctx.generic Γ Θ⟧ = t) ?_ X t s hp
  intro Ξ t s
  refine Quotient.inductionOn₂ (motive := fun t s =>
    ∀ (hp : Ob.Term.tele t = Ty.map (Quiver.Hom.op (s : Ξ.toOb ⟶ Γ.toOb)) ⟦Θ⟧),
      Tm.map (Quiver.Hom.op (homEquiv Ξ.toOb Γ Θ ⟨(t, s), hp⟩))
          ⟦Ctx.generic Γ Θ⟧ = t) t s ?_
  rintro ⟨⟨_, Θ₀, hΘ₀⟩, τ, hτ⟩ b hp
  obtain ⟨rfl, hwf, heq⟩ := Quotient.exact hp
  have hrel : Ob.Tele.Rel (⟨Θ.arity, Θ₀, hΘ₀⟩ : Ob.Tele Ξ.toOb)
      (Ob.Tele.subst b Θ) := ⟨rfl, hwf, heq⟩
  have hi : dTel.actBase
        (Ob.Pair.subst ⟨(⟨⟨Θ.arity, Θ₀, hΘ₀⟩, τ, hτ⟩, b), hrel⟩).1
        (Ctx.genericTele Γ Θ).telescope
      = dTel.actBase b.1 Θ.telescope := by
    refine Eq.trans (dTel.actBase_square (Renaming.inl Γ.arity Θ.arity)
      (𝟙ʳ Ξ.arity) _ b.1 ?_ Θ.telescope) ?_
    · intro α u
      refine (Subst.copair_inl b.1 _ u).trans ?_
      refine Eq.symm (Eq.trans (congrArg (fun ρ => Renaming.act ρ (b.1 u))
        (Renaming.extend_id Ξ.arity α)) ?_)
      exact Renaming.act_id _
    · exact dTel.rename_id _
  have hii : Subst.applyEach
        (Ob.Pair.subst ⟨(⟨⟨Θ.arity, Θ₀, hΘ₀⟩, τ, hτ⟩, b), hrel⟩).1
        (_root_.Subst.instId Γ.arity Θ.arity)
      = (Ob.Pair.fill ⟨(⟨⟨Θ.arity, Θ₀, hΘ₀⟩, τ, hτ⟩, b), hrel⟩).1 := by
    funext Λ z
    exact (act_η _ Λ (C.inr z)).trans (Subst.copair_inr _ _ z)
  refine Quotient.sound ⟨rfl, ?tele, ?fill⟩
  case tele =>
    refine Eq.mp (congrArg (fun T => Ob.Tele.Eq Ξ.toOb T Θ₀) hi.symm) ?_
    exact (Ob.Tele.Rel.symm hrel).2
  case fill =>
    refine Eq.mp (congrArg₂ (fun T s => Ob.Fill.Eq Ξ.toOb T s τ)
      hi.symm hii.symm) ?_
    exact Ob.Fill.Rel.refl
      (Ob.Pair.fill ⟨(⟨⟨Θ.arity, Θ₀, hΘ₀⟩, τ, hτ⟩, b), hrel⟩)

/-- 13.2: the square of the natural model commutes. -/
theorem q_commSq (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    CommSq (yonedaEquiv.symm ⟦Ctx.generic Γ Θ⟧)
      (yoneda.map (Ctx.projection Γ Θ)) Ctx.q (yonedaEquiv.symm ⟦Θ⟧) := by
  refine ⟨?_⟩
  ext Y κ
  exact tele_map Γ Θ ⟦Ctx.generic Γ Θ⟧ (Ctx.projection Γ Θ) κ
    (generic_tele Γ Θ)

theorem homEquiv_symm_apply (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (κ : X ⟶ Ctx.extend Γ Θ) :
    ((homEquiv X Γ Θ).symm κ).1
      = (Tm.map κ.op ⟦Ctx.generic Γ Θ⟧, κ ≫ Ctx.projection Γ Θ) := by
  have h₁ := homEquiv_generic X Γ Θ ((homEquiv X Γ Θ).symm κ)
  have h₂ := homEquiv_projection X Γ Θ ((homEquiv X Γ Θ).symm κ)
  rw [Equiv.apply_symm_apply] at h₁ h₂
  exact Prod.ext h₁.symm h₂.symm

section

variable (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
  (s : Limits.PullbackCone Ctx.q (yonedaEquiv.symm ⟦Θ⟧))

theorem q_cone_condition (Y : Obᵒᵖ) (x : s.pt.obj Y) :
    Ob.Term.tele (s.fst.app Y x) = Ty.map (s.snd.app Y x).op ⟦Θ⟧ :=
  ConcreteCategory.congr_hom (NatTrans.congr_app s.condition Y) x


/-- 13.2: the lift into the extension. -/
def q_lift : s.pt ⟶ yoneda.obj (Ctx.extend Γ Θ) where
  app Y := TypeCat.ofHom (fun x => homEquiv (Opposite.unop Y) Γ Θ
    ⟨(s.fst.app Y x, s.snd.app Y x), q_cone_condition Γ Θ s Y x⟩)
  naturality := by
    intro Y Z g
    ext x
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
    refine Eq.trans ?_ (homEquiv_naturality Γ Θ (s.fst.app Y x)
      (s.snd.app Y x) g.unop (q_cone_condition Γ Θ s Y x)
      (tele_map Γ Θ (s.fst.app Y x) (s.snd.app Y x) g.unop
        (q_cone_condition Γ Θ s Y x)))
    refine congrArg (homEquiv (Opposite.unop Z) Γ Θ) (Subtype.ext ?_)
    exact congrArg₂ Prod.mk (ConcreteCategory.congr_hom (s.fst.naturality g) x)
      (ConcreteCategory.congr_hom (s.snd.naturality g) x)


theorem q_fac_left :
    q_lift Γ Θ s ≫ yonedaEquiv.symm ⟦Ctx.generic Γ Θ⟧ = s.fst := by
  ext Y x
  simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
  exact homEquiv_generic (Opposite.unop Y) Γ Θ
    ⟨(s.fst.app Y x, s.snd.app Y x), q_cone_condition Γ Θ s Y x⟩

theorem q_fac_right :
    q_lift Γ Θ s ≫ yoneda.map (Ctx.projection Γ Θ) = s.snd := by
  ext Y x
  simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
  exact homEquiv_projection (Opposite.unop Y) Γ Θ
    ⟨(s.fst.app Y x, s.snd.app Y x), q_cone_condition Γ Θ s Y x⟩

theorem q_uniq (m : s.pt ⟶ yoneda.obj (Ctx.extend Γ Θ))
    (h₁ : m ≫ yonedaEquiv.symm ⟦Ctx.generic Γ Θ⟧ = s.fst)
    (h₂ : m ≫ yoneda.map (Ctx.projection Γ Θ) = s.snd) :
    m = q_lift Γ Θ s := by
  ext Y x
  simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply]
  refine Eq.trans
    (Equiv.apply_symm_apply (homEquiv (Opposite.unop Y) Γ Θ) _).symm ?_
  refine congrArg (homEquiv (Opposite.unop Y) Γ Θ) (Subtype.ext ?_)
  refine (homEquiv_symm_apply _ Γ Θ (m.app Y x)).trans ?_
  refine congrArg₂ Prod.mk ?_ ?_
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ Y) x
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₂ Y) x

end

/-- 13.2: the square of the natural model is a pullback. -/
theorem q_isPullback (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    IsPullback (yonedaEquiv.symm ⟦Ctx.generic Γ Θ⟧)
      (yoneda.map (Ctx.projection Γ Θ)) Ctx.q (yonedaEquiv.symm ⟦Θ⟧) :=
  IsPullback.of_isLimit' (q_commSq Γ Θ)
    (Limits.PullbackCone.IsLimit.mk (q_commSq Γ Θ).w (q_lift Γ Θ) (q_fac_left Γ Θ)
      (q_fac_right Γ Θ) (fun s m h₁ h₂ => q_uniq Γ Θ s m h₁ h₂))

/-- 13.2: `q` is a natural model — every pullback of it along a representable is
representable, the pullback along `よΓ` being `よ(Γ ⋈ Θ)`. -/
theorem q_representable : yoneda.relativelyRepresentable Ctx.q := by
  intro a g
  refine Ob.ind (motive := fun a => ∀ g : yoneda.obj a ⟶ Ty,
    ∃ (b : Ob) (snd : b ⟶ a) (fst : yoneda.obj b ⟶ Tm),
      IsPullback fst (yoneda.map snd) Ctx.q g) ?_ a g
  intro Γ g
  obtain ⟨Θ, rfl⟩ : ∃ Θ, g = yonedaEquiv.symm Θ := ⟨yonedaEquiv g, by simp⟩
  refine Quotient.ind (motive := fun Θ =>
    ∃ (b : Ob) (snd : b ⟶ Γ.toOb) (fst : yoneda.obj b ⟶ Tm),
      IsPullback fst (yoneda.map snd) Ctx.q (yonedaEquiv.symm Θ)) ?_ Θ
  intro Θ
  exact ⟨Ctx.extend Γ Θ, Ctx.projection Γ Θ, _, q_isPullback Γ Θ⟩

end Ctx
