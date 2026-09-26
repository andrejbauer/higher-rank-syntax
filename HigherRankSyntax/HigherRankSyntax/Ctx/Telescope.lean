import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import HigherRankSyntax.Ctx.Ctx

/-!
# Telescopes over a context

`Ob.Tele X` is the well-formed telescopes over a context class `X`, and `Ty` is
the presheaf sending `X` to these telescopes modulo equality, a filling acting by
substitution into the base.  `Ob.Fill X Θ` is the fillings of such a telescope.
A context `Γ` extended by a telescope `Θ` over it projects to `Γ`, a filling
lifts to a morphism between extensions, and the class of the empty context is
terminal.
-/

open CategoryTheory

namespace Ctx

/-- `Θ` is well formed over the ambient of `X`. -/
def Ob.Tele.Wf (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω → Prop)
    X (fun Γ _ Θ => Wf_t Γ.ambient Θ)
    (by
      rintro _ ⟨_, _, _⟩ ⟨rfl, hA⟩
      apply heq_of_eq
      funext _ _
      apply propext ⟨Wf_t.ofEq hA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hA)⟩)
    Ω Θ

/-- A well-formed telescope over a context class, with its arity. -/
def Ob.Tele (X : Ob) : Type :=
  Σ Ω : C.Arity, { Θ : dTel X.arity Ω // Ob.Tele.Wf X Θ }

/-- The arity a telescope declares. -/
def Ob.Tele.arity {X : Ob} (Θ : Ob.Tele X) : C.Arity := Θ.1

/-- The underlying telescope. -/
def Ob.Tele.telescope {X : Ob} (Θ : Ob.Tele X) : dTel X.arity Θ.arity := Θ.2.1

/-- The telescope is well formed. -/
theorem Ob.Tele.wf {X : Ob} (Θ : Ob.Tele X) :
  Ob.Tele.Wf X Θ.telescope
  := Θ.2.2

/-- `Θ` is well formed over the ambient of `X` and equal to `Θ'`. -/
def Ob.Tele.Eq (X : Ob) {Ω : C.Arity} (Θ Θ' : dTel X.arity Ω) : Prop :=
  Quotient.hrecOn (motive := fun X =>
      (Ω : C.Arity) → dTel (Ob.arity X) Ω → dTel (Ob.arity X) Ω → Prop)
    X (fun Γ _ Θ Θ' => Wf_t Γ.ambient Θ ∧ Eq_t Γ.ambient Θ Θ')
    (by
      rintro _ ⟨_, _, _⟩ ⟨rfl, hA⟩
      apply heq_of_eq
      funext _ _ _
      apply propext
      constructor
      · rintro ⟨hΘ, he⟩
        exact ⟨Wf_t.ofEq hA hΘ, Eq_t.ofEq hA hΘ he⟩
      · rintro ⟨hΘ, he⟩
        have hA' := Eq_t.symm Wf_t.nil hA
        exact ⟨Wf_t.ofEq hA' hΘ, Eq_t.ofEq hA' hΘ he⟩)
    Ω Θ Θ'

/-- Two telescopes over a context class declare the same arity and are equal
over its ambient. -/
def Ob.Tele.Rel {X : Ob} : Ob.Tele X → Ob.Tele X → Prop
  | ⟨Ω, Θ, _⟩, ⟨Ω', Θ', _⟩ => ∃ h : Ω = Ω', Ob.Tele.Eq X (h ▸ Θ) Θ'

theorem Ob.Tele.Rel.refl {X : Ob} (Θ : Ob.Tele X) :
  Ob.Tele.Rel Θ Θ
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_, _, hΘ⟩ := Θ
  exact ⟨rfl, hΘ, Wf_t.refl hΘ⟩

theorem Ob.Tele.Rel.symm {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ') :
  Ob.Tele.Rel Θ' Θ
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, hΘ'⟩ := Θ'
  obtain ⟨rfl, _, he⟩ := h
  exact ⟨rfl, hΘ', Eq_t.symm Γ.wf he⟩

theorem Ob.Tele.Rel.trans
    {X : Ob} {Θ Θ' Θ'' : Ob.Tele X}
    (h : Ob.Tele.Rel Θ Θ') (h' : Ob.Tele.Rel Θ' Θ'') :
  Ob.Tele.Rel Θ Θ''
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨_, _, _⟩ := Θ''
  obtain ⟨rfl, hΘ, he⟩ := h
  obtain ⟨rfl, _, he'⟩ := h'
  exact ⟨rfl, hΘ, Eq_t.trans Γ.wf hΘ he he'⟩

/-- The setoid of telescopes over `X` under `Ob.Tele.Rel`. -/
def Ob.Tele.setoid (X : Ob) : Setoid (Ob.Tele X) where
  r := Ob.Tele.Rel
  iseqv := ⟨Ob.Tele.Rel.refl, Ob.Tele.Rel.symm, Ob.Tele.Rel.trans⟩

/-- `Θ` is well formed over the ambient of `X` and `σ` fills it. -/
def Ob.Fill.Wf (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω)
    (σ : _root_.Subst Ω X.arity) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω →
      _root_.Subst Ω (Ob.arity X) → Prop)
    X (fun Γ _ Θ σ => Wf_t Γ.ambient Θ ∧ Wf_s Γ.ambient Θ σ)
    (by
      rintro _ ⟨_, _, _⟩ ⟨rfl, hA⟩
      apply heq_of_eq
      funext _ _ _
      apply propext
      constructor
      · rintro ⟨hΘ, hσ⟩
        exact ⟨Wf_t.ofEq hA hΘ, Wf_s.ofEq hA hσ (Wf_t.refl hΘ)⟩
      · rintro ⟨hΘ, hσ⟩
        have hA' := Eq_t.symm Wf_t.nil hA
        exact ⟨Wf_t.ofEq hA' hΘ, Wf_s.ofEq hA' hσ (Wf_t.refl hΘ)⟩)
    Ω Θ σ

/-- A well-formed filling of a telescope over a context class. -/
def Ob.Fill (X : Ob) (Θ : Ob.Tele X) : Type :=
  { σ : _root_.Subst Θ.arity X.arity // Ob.Fill.Wf X Θ.telescope σ }

/-- `Θ` is well formed over the ambient of `X`, `σ` fills it, and `σ` agrees
with `σ'`. -/
def Ob.Fill.Eq (X : Ob) {Ω : C.Arity} (Θ : dTel X.arity Ω)
    (σ σ' : _root_.Subst Ω X.arity) : Prop :=
  Quotient.hrecOn (motive := fun X => (Ω : C.Arity) → dTel (Ob.arity X) Ω →
      _root_.Subst Ω (Ob.arity X) → _root_.Subst Ω (Ob.arity X) → Prop)
    X (fun Γ _ Θ σ σ' =>
      Wf_t Γ.ambient Θ ∧ Wf_s Γ.ambient Θ σ ∧ Eq_s Γ.ambient Θ σ σ')
    (by
      rintro _ ⟨_, _, _⟩ ⟨rfl, hA⟩
      apply heq_of_eq
      funext _ _ _ _
      apply propext
      constructor
      · rintro ⟨hΘ, hσ, hst⟩
        have hσ' := Wf_s.ofEq hA hσ (Wf_t.refl hΘ)
        have hbase := Eq_t.toBoth Eq_t.Both.nil hA
        use Wf_t.ofEq hA hΘ, hσ'
        apply Eq_s.ofBoth hbase hst (Eq_t.Both.refl hbase hΘ) hσ hσ'
      · rintro ⟨hΘ, hσ, hst⟩
        have hA' := Eq_t.symm Wf_t.nil hA
        have hσ' := Wf_s.ofEq hA' hσ (Wf_t.refl hΘ)
        have hbase := Eq_t.toBoth Eq_t.Both.nil hA'
        use Wf_t.ofEq hA' hΘ, hσ'
        apply Eq_s.ofBoth hbase hst (Eq_t.Both.refl hbase hΘ) hσ hσ')
    Ω Θ σ σ'

/-- Two fillings of a telescope over a context class agree. -/
def Ob.Fill.Rel {X : Ob} {Θ : Ob.Tele X} (σ σ' : Ob.Fill X Θ) : Prop :=
  Ob.Fill.Eq X Θ.telescope σ.1 σ'.1

theorem Ob.Fill.Rel.refl {X : Ob} {Θ : Ob.Tele X} (σ : Ob.Fill X Θ) :
  Ob.Fill.Rel σ σ
  := by
  obtain ⟨_⟩ := X
  exact ⟨σ.2.1, σ.2.2, Eq_s.refl σ.2.2⟩

theorem Ob.Fill.Rel.symm
    {X : Ob} {Θ : Ob.Tele X} {σ σ' : Ob.Fill X Θ}
    (h : Ob.Fill.Rel σ σ') :
  Ob.Fill.Rel σ' σ
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨hΘ, hσ, hst⟩ := h
  exact ⟨hΘ, σ'.2.2, Eq_s.symm Γ.wf hst hΘ hσ σ'.2.2⟩

theorem Ob.Fill.Rel.trans
    {X : Ob} {Θ : Ob.Tele X} {σ σ' σ'' : Ob.Fill X Θ}
    (h : Ob.Fill.Rel σ σ') (h' : Ob.Fill.Rel σ' σ'') :
  Ob.Fill.Rel σ σ''
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨hΘ, hσ, hst⟩ := h
  exact ⟨hΘ, hσ, Eq_s.trans Γ.wf hst h'.2.2 hΘ hσ σ'.2.2⟩

/-- The setoid of fillings of `Θ` under `Ob.Fill.Rel`. -/
def Ob.Fill.setoid {X : Ob} (Θ : Ob.Tele X) : Setoid (Ob.Fill X Θ) where
  r := Ob.Fill.Rel
  iseqv := ⟨Ob.Fill.Rel.refl, Ob.Fill.Rel.symm, Ob.Fill.Rel.trans⟩

/-- Equal telescopes declare the same arity. -/
theorem Ob.Tele.Rel.arity {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ') :
  Θ.arity = Θ'.arity
  := h.1

theorem Ob.Fill.Wf.ofRel
    {X : Ob} {Θ Θ' : Ob.Tele X}
    (h : Ob.Tele.Rel Θ Θ') (τ : Ob.Fill X Θ) :
  Ob.Fill.Wf X Θ'.telescope (h.arity ▸ τ.1)
  := by
  obtain ⟨Ξ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨rfl, hΘ, he⟩ := h
  exact ⟨Wf_t.ofEq_t Ξ.wf hΘ he, Wf_s.ofEq_t Ξ.wf τ.2.2 he⟩

/-- A filling of `Θ` as a filling of an equal telescope `Θ'`. -/
def Ob.Fill.ofRel {X : Ob} {Θ Θ' : Ob.Tele X} (h : Ob.Tele.Rel Θ Θ')
    (τ : Ob.Fill X Θ) : Ob.Fill X Θ' :=
  ⟨h.arity ▸ τ.1, Ob.Fill.Wf.ofRel h τ⟩

/-- Telescopes with the same arity and the same underlying telescope are equal. -/
theorem Ob.Tele.ext
    {X : Ob} {Ω : C.Arity} {Θ Θ' : dTel X.arity Ω}
    {hΘ : Ob.Tele.Wf X Θ} {hΘ' : Ob.Tele.Wf X Θ'}
    (h : Θ = Θ') :
  (⟨Ω, Θ, hΘ⟩ : Ob.Tele X) = ⟨Ω, Θ', hΘ'⟩
  := by
  subst h
  rfl

theorem Ob.Tele.Wf.subst {X Y : Ob} (σ : Ob.Subst X Y) (Θ : Ob.Tele Y) :
  Ob.Tele.Wf X (dTel.actBase σ.1 Θ.telescope)
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_⟩ := Y
  apply Wf_t.subst_ambient σ.2.toWf_sub Θ.wf

/-- The telescope `Θ` over `Y` with the filling `σ` substituted into its base, as
a telescope over `X`. -/
def Ob.Tele.subst {X Y : Ob} (σ : Ob.Subst X Y) (Θ : Ob.Tele Y) : Ob.Tele X :=
  ⟨Θ.arity, dTel.actBase σ.1 Θ.telescope, Ob.Tele.Wf.subst σ Θ⟩

theorem Ob.Tele.Rel.subst
    {X Y : Ob} {σ σ' : Ob.Subst X Y} {Θ Θ' : Ob.Tele Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (hΘ : Ob.Tele.Rel Θ Θ') :
  Ob.Tele.Rel (Ob.Tele.subst σ Θ) (Ob.Tele.subst σ' Θ')
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Δ⟩ := Y
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, hΘ'⟩ := Θ'
  obtain ⟨rfl, hwf, he⟩ := hΘ
  have hwfσ := Wf_t.subst_ambient σ.2.toWf_sub hwf
  use rfl, hwfσ
  apply Eq_t.trans Γ.wf hwfσ (Eq_t.subst_ambient σ.2.toWf_sub he)
  apply Eq_t.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hσ.2.toEq_sub hΘ'

/-- The presheaf sending a context class `X` to the classes of telescopes over
`X`, a filling acting by substitution into the base. -/
def Ty : Obᵒᵖ ⥤ Type where
  obj X := Quotient (Ob.Tele.setoid X.unop)
  map {X Y} f :=
    TypeCat.ofHom (Quotient.map₂ (sa := Ob.Subst.setoid Y.unop X.unop)
      (sb := Ob.Tele.setoid X.unop) (sc := Ob.Tele.setoid Y.unop)
      Ob.Tele.subst (fun _ _ hσ _ _ hΘ => Ob.Tele.Rel.subst hσ hΘ) f.unop)
  map_id X := by
    ext Θ
    obtain ⟨⟨_, Θ, _⟩⟩ := Θ
    apply congrArg (Quotient.mk _)
    apply Ob.Tele.ext (dTel.actBase_id Θ)
  map_comp f g := by
    obtain ⟨⟨σ⟩⟩ := f
    obtain ⟨⟨θ⟩⟩ := g
    ext Θ
    obtain ⟨⟨_, Θ, _⟩⟩ := Θ
    apply congrArg (Quotient.mk _)
    apply Ob.Tele.ext (dTel.actBase_comp σ.1 θ.1 Θ)

/-- The class of a context. -/
def toOb (Γ : Ctx) : Ob := Quotient.mk setoid Γ

/-- The class of the context with ambient `Γ.ambient ⋈ Θ.telescope`. -/
def extend (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : Ob :=
  toOb ⟨Γ.arity ⋈ Θ.arity, Γ.ambient ⋈ Θ.telescope,
    Wf_t.concatenate Γ.wf Θ.wf⟩

/-- The projection from `Γ` extended by `Θ` to `Γ`, sending each slot `x` of `Γ` to
the η-expansion of `C.inl x`. -/
def projection (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : extend Γ Θ ⟶ Γ.toOb :=
  Quotient.mk (Ob.Subst.setoid (extend Γ Θ) Γ.toOb)
    ⟨_root_.Subst.ofRenaming (Renaming.inl Γ.arity Θ.arity), by
      have h := Wf_s.weaken (Ambient.Renaming.weaken Γ.ambient Θ.telescope)
        (Wf_sub.id Γ.wf).toFilling
      rw [← dTel.rename_comp, Renaming.eq_fromUnit (_ ∘ʳ _)] at h
      simp only [_root_.Subst.id, Renaming.act_eta] at h
      exact h⟩

/-- Extending equal ambients by equal telescopes gives the same context class. -/
theorem extend_congr
    {Ω Λ : C.Arity} {A A' : Ambient Ω} {Θ Θ' : dTel Ω Λ}
    {hA : Ambient.Wf A} {hA' : Ambient.Wf A'} {hΘ : Wf_t A Θ} {hΘ' : Wf_t A' Θ'}
    (hAA : Eq_t (.nil : Ambient 1) A A') (hΘΘ : Eq_t A Θ Θ') :
  extend ⟨Ω, A, hA⟩ ⟨Λ, Θ, hΘ⟩ = extend ⟨Ω, A', hA'⟩ ⟨Λ, Θ', hΘ'⟩
  := Quotient.sound ⟨rfl, Eq_t.concatenate hAA hΘΘ⟩

/-- The morphism from `Ξ` extended by `Θ` with `σ` substituted to `Γ` extended by
`Θ`, sending `C.inl x` to `σ x` renamed along `Renaming.inl` and `C.inr z` to the
η-expansion of `C.inr z`. -/
def lift {Ξ Γ : Ctx} (σ : Ob.Subst Ξ.toOb Γ.toOb) (Θ : Ob.Tele Γ.toOb) :
    extend Ξ (Ob.Tele.subst σ Θ) ⟶ extend Γ Θ :=
  Quotient.mk (Ob.Subst.setoid (extend Ξ (Ob.Tele.subst σ Θ)) (extend Γ Θ))
    ⟨_root_.Subst.lift σ.1 Θ.arity, (Wf_sub.lift σ.2.toWf_sub Θ.wf).toFilling⟩

/-- The class of the empty context is terminal. -/
def emptyIsTerminal : Limits.IsTerminal empty.toOb :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => Quotient.mk (Ob.Subst.setoid X empty.toOb)
      ⟨fun ⦃_⦄ x => (C.unit_is_empty x).elim, by obtain ⟨_⟩ := X; exact Wf_s.nil⟩)
    (by
      rintro _ ⟨_⟩
      apply congrArg (Quotient.mk _)
      apply Subtype.ext
      funext _ x
      exact (C.unit_is_empty x).elim)

end Ctx
