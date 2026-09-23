import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Types.Basic
import HigherRankSyntax.Ctx.Ctx

/-!
# Telescopes over a context

`Ob.Tele X` is the well-formed telescopes over a context class and `Ty` the
presheaf they form modulo 7.4.
-/

open CategoryTheory

namespace Ctx

/-- 7.1 for a telescope over a context class. -/
def Ob.Tele.Wf (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω → Prop)
    X (fun Γ _ Θ => Wf_t Γ.ambient Θ)
    (by
      intro _ Γ' h
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨rfl, hA⟩ := h
      exact heq_of_eq (funext fun _ => funext fun _ =>
        propext ⟨Wf_t.ofEq hA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hA)⟩))
    Ω Θ

/-- A well-formed telescope over a context class, with its arity. -/
def Ob.Tele (X : Ob) : Type :=
  Σ Ω : C.Arity, { Θ : dTel X.arity Ω // Ob.Tele.Wf X Θ }

/-- The arity a telescope declares. -/
def Ob.Tele.arity {X : Ob} (Θ : Ob.Tele X) : C.Arity := Θ.1

/-- The underlying telescope. -/
def Ob.Tele.telescope {X : Ob} (Θ : Ob.Tele X) : dTel X.arity Θ.arity := Θ.2.1

/-- The telescope is well formed. -/
theorem Ob.Tele.wf {X : Ob} (Θ : Ob.Tele X) : Ob.Tele.Wf X Θ.telescope := Θ.2.2

/-- 7.4 for telescopes over a context class. -/
def Ob.Tele.Eq (X : Ob) {Ω : C.Arity} (Θ Θ' : dTel X.arity Ω) : Prop :=
  Quotient.hrecOn (motive := fun X =>
      (Ω : C.Arity) → dTel (Ob.arity X) Ω → dTel (Ob.arity X) Ω → Prop)
    X (fun Γ _ Θ Θ' => Wf_t Γ.ambient Θ ∧ Eq_t Γ.ambient Θ Θ')
    (by
      intro Γ Γ' h
      obtain ⟨_, _, _⟩ := Γ
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨rfl, hA⟩ := h
      refine heq_of_eq (funext fun _ => funext fun _ => funext fun _ =>
        propext ⟨?_, ?_⟩)
      · rintro ⟨hΘ, he⟩
        exact ⟨Wf_t.ofEq hA hΘ, Eq_t.ofEq hA hΘ he⟩
      · rintro ⟨hΘ, he⟩
        have hsym := Eq_t.symm Wf_t.nil hA
        exact ⟨Wf_t.ofEq hsym hΘ, Eq_t.ofEq hsym hΘ he⟩)
    Ω Θ Θ'

/-- 7.4 on the telescopes over a context class. -/
def Ob.Tele.Rel {X : Ob} : Ob.Tele X → Ob.Tele X → Prop
  | ⟨Ω, Θ, _⟩, ⟨Ω', Θ', _⟩ => ∃ h : Ω = Ω', Ob.Tele.Eq X (h ▸ Θ) Θ'

theorem Ob.Tele.Rel.refl {X : Ob} (Θ : Ob.Tele X) : Ob.Tele.Rel Θ Θ := by
  refine Quotient.inductionOn (motive := fun X => ∀ Θ : Ob.Tele X, Ob.Tele.Rel Θ Θ)
    X ?_ Θ
  rintro _ ⟨_, _, hΘ⟩
  exact ⟨rfl, hΘ, Wf_t.refl hΘ⟩

theorem Ob.Tele.Rel.symm {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ') :
    Ob.Tele.Rel Θ' Θ := by
  refine Quotient.inductionOn (motive := fun X => ∀ Θ Θ' : Ob.Tele X,
    Ob.Tele.Rel Θ Θ' → Ob.Tele.Rel Θ' Θ) X ?_ Θ Θ' h
  rintro Γ ⟨_, _, _⟩ ⟨_, _, hΘ'⟩ ⟨rfl, _, he⟩
  exact ⟨rfl, hΘ', Eq_t.symm Γ.wf he⟩

theorem Ob.Tele.Rel.trans {X : Ob} {Θ Θ' Θ'' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ')
    (h' : Ob.Tele.Rel Θ' Θ'') : Ob.Tele.Rel Θ Θ'' := by
  refine Quotient.inductionOn (motive := fun X => ∀ Θ Θ' Θ'' : Ob.Tele X,
    Ob.Tele.Rel Θ Θ' → Ob.Tele.Rel Θ' Θ'' → Ob.Tele.Rel Θ Θ'') X ?_ Θ Θ' Θ'' h h'
  rintro Γ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hΘ, he⟩ ⟨rfl, _, he'⟩
  exact ⟨rfl, hΘ, Eq_t.trans Γ.wf hΘ he he'⟩

/-- 7.4 as a setoid on the telescopes over a context class. -/
def Ob.Tele.setoid (X : Ob) : Setoid (Ob.Tele X) where
  r := Ob.Tele.Rel
  iseqv := ⟨Ob.Tele.Rel.refl, Ob.Tele.Rel.symm, Ob.Tele.Rel.trans⟩

/-- 9.1 for a filling of a telescope over a context class. -/
def Ob.Fill.Wf (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω)
    (σ : _root_.Subst Ω X.arity) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω →
      _root_.Subst Ω (Ob.arity X) → Prop)
    X (fun Γ _ Θ σ => Wf_t Γ.ambient Θ ∧ Wf_s Γ.ambient Θ σ)
    (by
      intro Γ Γ' h
      obtain ⟨_, _, _⟩ := Γ
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨rfl, hA⟩ := h
      refine heq_of_eq (funext fun _ => funext fun _ => funext fun _ =>
        propext ⟨?_, ?_⟩)
      · rintro ⟨hΘ, hσ⟩
        exact ⟨Wf_t.ofEq hA hΘ, Wf_s.ofEq hA hσ (Wf_t.refl hΘ)⟩
      · rintro ⟨hΘ, hσ⟩
        have hsym := Eq_t.symm Wf_t.nil hA
        exact ⟨Wf_t.ofEq hsym hΘ, Wf_s.ofEq hsym hσ (Wf_t.refl hΘ)⟩)
    Ω Θ σ

/-- A well-formed filling of a telescope over a context class. -/
def Ob.Fill (X : Ob) (Θ : Ob.Tele X) : Type :=
  { σ : _root_.Subst Θ.arity X.arity // Ob.Fill.Wf X Θ.telescope σ }

/-- 9.2 for fillings of a telescope over a context class. -/
def Ob.Fill.Eq (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω)
    (σ σ' : _root_.Subst Ω X.arity) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω →
      _root_.Subst Ω (Ob.arity X) → _root_.Subst Ω (Ob.arity X) → Prop)
    X (fun Γ _ Θ σ σ' =>
      Wf_t Γ.ambient Θ ∧ Wf_s Γ.ambient Θ σ ∧ Eq_s Γ.ambient Θ σ σ')
    (by
      intro Γ Γ' h
      obtain ⟨_, _, _⟩ := Γ
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨rfl, hA⟩ := h
      refine heq_of_eq (funext fun _ => funext fun _ => funext fun _ =>
        funext fun _ => propext ⟨?_, ?_⟩)
      · rintro ⟨hΘ, hσ, hst⟩
        have hbase := Eq_t.toBoth Eq_t.Both.nil hA
        refine ⟨Wf_t.ofEq hA hΘ, Wf_s.ofEq hA hσ (Wf_t.refl hΘ), ?_⟩
        exact Eq_s.ofBoth hbase hst (Eq_t.Both.refl hbase hΘ) hσ
          (Wf_s.ofEq hA hσ (Wf_t.refl hΘ))
      · rintro ⟨hΘ, hσ, hst⟩
        have hsym := Eq_t.symm Wf_t.nil hA
        have hbase := Eq_t.toBoth Eq_t.Both.nil hsym
        refine ⟨Wf_t.ofEq hsym hΘ, Wf_s.ofEq hsym hσ (Wf_t.refl hΘ), ?_⟩
        exact Eq_s.ofBoth hbase hst (Eq_t.Both.refl hbase hΘ) hσ
          (Wf_s.ofEq hsym hσ (Wf_t.refl hΘ)))
    Ω Θ σ σ'

/-- 9.2 on the fillings of a telescope over a context class. -/
def Ob.Fill.Rel {X : Ob} {Θ : Ob.Tele X} (σ σ' : Ob.Fill X Θ) : Prop :=
  Ob.Fill.Eq X Θ.telescope σ.1 σ'.1

theorem Ob.Fill.Rel.refl {X : Ob} {Θ : Ob.Tele X} (σ : Ob.Fill X Θ) :
    Ob.Fill.Rel σ σ := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (σ : Ob.Fill X Θ), Ob.Fill.Rel σ σ) X ?_ Θ σ
  intro _ _ σ
  exact ⟨σ.2.1, σ.2.2, Eq_s.refl σ.2.2⟩

theorem Ob.Fill.Rel.symm {X : Ob} {Θ : Ob.Tele X} {σ σ' : Ob.Fill X Θ}
    (h : Ob.Fill.Rel σ σ') : Ob.Fill.Rel σ' σ := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (σ σ' : Ob.Fill X Θ), Ob.Fill.Rel σ σ' → Ob.Fill.Rel σ' σ) X ?_ Θ σ σ' h
  intro Γ _ _ σ' h
  exact ⟨h.1, σ'.2.2, Eq_s.symm Γ.wf h.2.2 h.1 h.2.1 σ'.2.2⟩

theorem Ob.Fill.Rel.trans {X : Ob} {Θ : Ob.Tele X} {σ σ' σ'' : Ob.Fill X Θ}
    (h : Ob.Fill.Rel σ σ') (h' : Ob.Fill.Rel σ' σ'') : Ob.Fill.Rel σ σ'' := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ : Ob.Tele X)
    (σ σ' σ'' : Ob.Fill X Θ), Ob.Fill.Rel σ σ' → Ob.Fill.Rel σ' σ'' →
      Ob.Fill.Rel σ σ'') X ?_ Θ σ σ' σ'' h h'
  intro Γ _ _ σ' _ h h'
  exact ⟨h.1, h.2.1, Eq_s.trans Γ.wf h.2.2 h'.2.2 h.1 h.2.1 σ'.2.2⟩

/-- 9.2 as a setoid on the fillings of a telescope over a context class. -/
def Ob.Fill.setoid {X : Ob} (Θ : Ob.Tele X) : Setoid (Ob.Fill X Θ) where
  r := Ob.Fill.Rel
  iseqv := ⟨Ob.Fill.Rel.refl, Ob.Fill.Rel.symm, Ob.Fill.Rel.trans⟩

/-- The arities of equal telescopes agree. -/
theorem Ob.Tele.Rel.arity {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ') :
    Θ.arity = Θ'.arity := by
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨e, _⟩ := h
  exact e

theorem Ob.Fill.Wf.ofRel {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ')
    (τ : Ob.Fill X Θ) : Ob.Fill.Wf X Θ'.telescope (h.arity ▸ τ.1) := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ Θ' : Ob.Tele X)
    (h : Ob.Tele.Rel Θ Θ') (τ : Ob.Fill X Θ),
      Ob.Fill.Wf X Θ'.telescope (h.arity ▸ τ.1)) X ?_ Θ Θ' h τ
  rintro Ξ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hwf, heq⟩ τ
  exact ⟨Wf_t.ofEq_t Ξ.wf hwf heq, Wf_s.ofEq_t Ξ.wf τ.2.2 heq⟩

/-- 8(10): a filling transported along an equality of telescopes. -/
def Ob.Fill.ofRel {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ')
    (τ : Ob.Fill X Θ) : Ob.Fill X Θ' :=
  ⟨h.arity ▸ τ.1, Ob.Fill.Wf.ofRel h τ⟩

/-- Transport along an equality of telescopes respects 9.2. -/
theorem Ob.Fill.Rel.ofRel {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ')
    (τ τ' : Ob.Fill X Θ) :
    Ob.Fill.Rel τ τ' ↔ Ob.Fill.Rel (Ob.Fill.ofRel h τ) (Ob.Fill.ofRel h τ') := by
  refine Quotient.inductionOn (motive := fun X => ∀ (Θ Θ' : Ob.Tele X)
    (h : Ob.Tele.Rel Θ Θ') (τ τ' : Ob.Fill X Θ),
      (Ob.Fill.Rel τ τ' ↔
        Ob.Fill.Rel (Ob.Fill.ofRel h τ) (Ob.Fill.ofRel h τ'))) X ?_ Θ Θ' h τ τ'
  rintro Ξ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hwf, heq⟩ τ τ'
  refine ⟨fun hr => ⟨Wf_t.ofEq_t Ξ.wf hwf heq, Wf_s.ofEq_t Ξ.wf τ.2.2 heq, ?_⟩,
    fun hr => ⟨hwf, τ.2.2, ?_⟩⟩
  · exact Eq_s.ofEq_t Ξ.wf hr.2.2 τ.2.2 heq
  · exact Eq_s.ofEq_t Ξ.wf hr.2.2 (Wf_s.ofEq_t Ξ.wf τ.2.2 heq) (Eq_t.symm Ξ.wf heq)

/-- Telescopes with the same arity and the same underlying telescope agree. -/
theorem Ob.Tele.ext {X : Ob} {Ω : C.Arity} {Θ Θ' : dTel X.arity Ω}
    {hΘ : Ob.Tele.Wf X Θ} {hΘ' : Ob.Tele.Wf X Θ'} (h : Θ = Θ') :
    (⟨Ω, Θ, hΘ⟩ : Ob.Tele X) = ⟨Ω, Θ', hΘ'⟩ := by
  subst h
  rfl

theorem Ob.Tele.Wf.subst {X Y : Ob} (σ : Ob.Subst X Y) (Θ : Ob.Tele Y) :
    Ob.Tele.Wf X (dTel.actBase σ.1 Θ.telescope) := by
  refine Quotient.inductionOn₂ (motive := fun X Y =>
    ∀ (σ : Ob.Subst X Y) (Θ : Ob.Tele Y),
      Ob.Tele.Wf X (dTel.actBase σ.1 Θ.telescope)) X Y ?_ σ Θ
  intro _ _ σ Θ
  exact Wf_t.subst_ambient σ.2.toWf_sub Θ.wf

/-- 10.2: the action of a filling on a telescope. -/
def Ob.Tele.subst {X Y : Ob} (σ : Ob.Subst X Y) (Θ : Ob.Tele Y) : Ob.Tele X :=
  ⟨Θ.arity, dTel.actBase σ.1 Θ.telescope, Ob.Tele.Wf.subst σ Θ⟩

theorem Ob.Tele.Rel.subst {X Y : Ob} {σ σ' : Ob.Subst X Y} {Θ Θ' : Ob.Tele Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (hΘ : Ob.Tele.Rel Θ Θ') :
    Ob.Tele.Rel (Ob.Tele.subst σ Θ) (Ob.Tele.subst σ' Θ') := by
  refine Quotient.inductionOn₂ (motive := fun X Y =>
    ∀ (σ σ' : Ob.Subst X Y) (Θ Θ' : Ob.Tele Y), Ob.Subst.Rel X Y σ.1 σ'.1 →
      Ob.Tele.Rel Θ Θ' → Ob.Tele.Rel (Ob.Tele.subst σ Θ) (Ob.Tele.subst σ' Θ'))
    X Y ?_ σ σ' Θ Θ' hσ hΘ
  rintro Γ Δ σ σ' ⟨_, _, _⟩ ⟨_, _, hΘ'⟩ hσ ⟨rfl, hwf, he⟩
  refine ⟨rfl, Wf_t.subst_ambient σ.2.toWf_sub hwf, ?_⟩
  refine Eq_t.trans Γ.wf (Wf_t.subst_ambient σ.2.toWf_sub hwf)
    (Eq_t.subst_ambient σ.2.toWf_sub he) ?_
  exact Eq_t.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hσ.2.toEq_sub hΘ'

/-- 10.1, 10.2: the presheaf of telescopes. -/
def Ty : Obᵒᵖ ⥤ Type where
  obj X := Quotient (Ob.Tele.setoid X.unop)
  map {X Y} f :=
    TypeCat.ofHom (Quotient.map₂ (sa := Ob.Subst.setoid Y.unop X.unop)
      (sb := Ob.Tele.setoid X.unop) (sc := Ob.Tele.setoid Y.unop)
      Ob.Tele.subst (fun _ _ hσ _ _ hΘ => Ob.Tele.Rel.subst hσ hΘ) f.unop)
  map_id X := by
    ext Θ
    refine Quotient.inductionOn Θ ?_
    rintro ⟨_, Θ₀, _⟩
    exact congrArg (Quotient.mk (Ob.Tele.setoid X.unop))
      (Ob.Tele.ext (dTel.actBase_id Θ₀))
  map_comp {X Y Z} f g := by
    obtain ⟨u⟩ := f
    obtain ⟨v⟩ := g
    ext Θ
    refine Quotient.inductionOn₃ u v Θ ?_
    rintro σ θ ⟨_, Θ₀, _⟩
    exact congrArg (Quotient.mk (Ob.Tele.setoid Z.unop))
      (Ob.Tele.ext (dTel.actBase_comp σ.1 θ.1 Θ₀))

/-- A context as a class. -/
def toOb (Γ : Ctx) : Ob := Quotient.mk Ctx.setoid Γ

/-- 10.4: the context extended by a telescope. -/
def extend (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : Ob :=
  Ctx.toOb ⟨Γ.arity ⋈ Θ.arity, Γ.ambient ⋈ Θ.telescope,
    Wf_t.concatenate Γ.wf Θ.wf⟩

/-- 10.4: the projection off an extension. -/
def projection (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : Ctx.extend Γ Θ ⟶ Γ.toOb := by
  refine Quotient.mk (Ob.Subst.setoid (Ctx.extend Γ Θ) Γ.toOb)
    ⟨_root_.Subst.ofRenaming (Renaming.inl Γ.arity Θ.arity), ?_⟩
  have hrename : dTel.rename (Renaming.inl Γ.arity Θ.arity)
      (dTel.rename (Renaming.fromUnit Γ.arity) Γ.ambient)
      = dTel.rename (Renaming.fromUnit (Γ.arity ⋈ Θ.arity)) Γ.ambient := by
    refine Eq.trans (dTel.rename_comp (Renaming.fromUnit Γ.arity)
      (Renaming.inl Γ.arity Θ.arity) Γ.ambient).symm ?_
    exact congrArg (fun ρ => dTel.rename ρ Γ.ambient) (Renaming.eq_fromUnit
      (Renaming.inl Γ.arity Θ.arity ∘ʳ Renaming.fromUnit Γ.arity))
  have hsubst : (fun ⦃Λ : C.Arity⦄ (i : Γ.arity ∋ Λ) =>
      ⟦ Renaming.inl Γ.arity Θ.arity ⇑ʳ Λ ⟧ʳ (_root_.Subst.id Γ.arity i))
      = _root_.Subst.ofRenaming (Renaming.inl Γ.arity Θ.arity) := by
    funext Λ i
    exact Renaming.act_eta (Renaming.inl Γ.arity Θ.arity) i
  refine Eq.mp (congrArg₂ (fun T s => Wf_s (Γ.ambient ⋈ Θ.telescope) T s)
    hrename hsubst) ?_
  exact Wf_s.weaken (Ambient.Renaming.weaken Γ.ambient Θ.telescope)
    (Wf_sub.id Γ.wf).toFilling

/-- Extension respects equality of the context and of the telescope. -/
theorem extend_congr {Ω Λ : C.Arity} {A A' : Ambient Ω} {Θ Θ' : dTel Ω Λ}
    {hA : Ambient.Wf A} {hA' : Ambient.Wf A'} {hΘ : Wf_t A Θ} {hΘ' : Wf_t A' Θ'}
    (hAA : Eq_t (.nil : Ambient 1) A A') (hΘΘ : Eq_t A Θ Θ') :
    Ctx.extend ⟨Ω, A, hA⟩ ⟨Λ, Θ, hΘ⟩ = Ctx.extend ⟨Ω, A', hA'⟩ ⟨Λ, Θ', hΘ'⟩ :=
  Quotient.sound ⟨rfl, Eq_t.concatenate hAA hΘΘ⟩

/-- 10.4: a filling extended past a telescope. -/
def lift {Ξ Γ : Ctx} (σ : Ob.Subst Ξ.toOb Γ.toOb) (Θ : Ob.Tele Γ.toOb) :
    Ctx.extend Ξ (Ob.Tele.subst σ Θ) ⟶ Ctx.extend Γ Θ :=
  Quotient.mk (Ob.Subst.setoid (Ctx.extend Ξ (Ob.Tele.subst σ Θ)) (Ctx.extend Γ Θ))
    ⟨_root_.Subst.lift σ.1 Θ.arity, (Wf_sub.lift σ.2.toWf_sub Θ.wf).toFilling⟩

/-- 10.4: the projection square. -/
theorem lift_projection {Ξ Γ : Ctx} (σ : Ob.Subst Ξ.toOb Γ.toOb)
    (Θ : Ob.Tele Γ.toOb) :
    Ctx.lift σ Θ ≫ Ctx.projection Γ Θ
      = Ctx.projection Ξ (Ob.Tele.subst σ Θ)
        ≫ Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ := by
  refine congrArg (Quotient.mk (Ob.Subst.setoid
    (Ctx.extend Ξ (Ob.Tele.subst σ Θ)) Γ.toOb)) (Subtype.ext ?_)
  funext Λ x
  refine Eq.trans (act_η (_root_.Subst.lift σ.1 Θ.arity) Λ (C.inl x)) ?_
  refine Eq.trans (Subst.lift_inl σ.1 x) ?_
  exact (act_ofRenaming (Renaming.inl Ξ.arity Θ.arity) (σ.1 x)).symm

end Ctx
