import HigherRankSyntax.Ctx.Basic

/-!
# The equivalences on contexts, telescopes and fillings

`Tele.Rel` is 7.4, `Subst.Rel` is 9.2, and `Ctx.Rel` is 7.4 at the empty context.
Each is an equivalence, and `Hom.comp` respects `Subst.Rel` in both arguments.
-/

namespace Ctx

/-- The context declaring no slots. -/
def empty : Ctx := ⟨1, .nil, Wf_t.nil⟩

/-- A context as a telescope over the empty context. -/
def toTele : Ctx → empty.Tele
  | ⟨Ω, A, hA⟩ => ⟨Ω, A, hA⟩

/-- 7.4: two telescopes over a context declare the same arity and are equal. -/
def Tele.Rel {Γ : Ctx} : Γ.Tele → Γ.Tele → Prop
  | ⟨Ω, Θ, _⟩, ⟨Ω', Θ', _⟩ => ∃ h : Ω = Ω', Eq_t Γ.ambient (h ▸ Θ) Θ'

theorem Tele.Rel.refl {Γ : Ctx} : ∀ Θ : Γ.Tele, Tele.Rel Θ Θ
  | ⟨_, _, hΘ⟩ => ⟨rfl, Wf_t.refl hΘ⟩

theorem Tele.Rel.symm {Γ : Ctx} {Θ Θ' : Γ.Tele} (h : Tele.Rel Θ Θ') :
    Tele.Rel Θ' Θ := by
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨rfl, heq⟩ := h
  exact ⟨rfl, Eq_t.symm Γ.wf heq⟩

theorem Tele.Rel.trans {Γ : Ctx} {Θ Θ' Θ'' : Γ.Tele} (h : Tele.Rel Θ Θ')
    (h' : Tele.Rel Θ' Θ'') : Tele.Rel Θ Θ'' := by
  obtain ⟨_, _, hΘ⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨_, _, _⟩ := Θ''
  obtain ⟨rfl, heq⟩ := h
  obtain ⟨rfl, heq'⟩ := h'
  exact ⟨rfl, Eq_t.trans Γ.wf hΘ heq heq'⟩

/-- 7.4 as a setoid on the telescopes over a context. -/
def Tele.setoid (Γ : Ctx) : Setoid Γ.Tele where
  r := Tele.Rel
  iseqv := ⟨Tele.Rel.refl, Tele.Rel.symm, Tele.Rel.trans⟩

/-- Two contexts are equal as telescopes over the empty context. -/
def Rel (Γ Γ' : Ctx) : Prop := Tele.Rel Γ.toTele Γ'.toTele

/-- 7.4 as a setoid on contexts. -/
def setoid : Setoid Ctx where
  r := Rel
  iseqv := ⟨fun Γ => Tele.Rel.refl Γ.toTele, Tele.Rel.symm, Tele.Rel.trans⟩

/-- 9.2: two fillings of a telescope agree at every non-equational slot. -/
def Subst.Rel {Γ : Ctx} {Θ : Γ.Tele} (σ θ : Γ.Subst Θ) : Prop :=
  Eq_s Γ.ambient Θ.telescope σ.1 θ.1

theorem Subst.Rel.refl {Γ : Ctx} {Θ : Γ.Tele} (σ : Γ.Subst Θ) : Subst.Rel σ σ :=
  Eq_s.refl σ.2

theorem Subst.Rel.symm {Γ : Ctx} {Θ : Γ.Tele} {σ θ : Γ.Subst Θ}
    (h : Subst.Rel σ θ) : Subst.Rel θ σ :=
  Eq_s.symm Γ.wf h Θ.wf σ.2 θ.2

theorem Subst.Rel.trans {Γ : Ctx} {Θ : Γ.Tele} {σ θ κ : Γ.Subst Θ}
    (h : Subst.Rel σ θ) (h' : Subst.Rel θ κ) : Subst.Rel σ κ :=
  Eq_s.trans Γ.wf h h' Θ.wf σ.2 θ.2

/-- 9.2 as a setoid on the fillings of a telescope. -/
def Subst.setoid {Γ : Ctx} (Θ : Γ.Tele) : Setoid (Γ.Subst Θ) where
  r := Subst.Rel
  iseqv := ⟨Subst.Rel.refl, Subst.Rel.symm, Subst.Rel.trans⟩

/-- Composition respects agreement of fillings in both arguments. -/
theorem Hom.comp_congr {Γ Δ Ξ : Ctx} {f f' : Γ.Hom Δ} {g g' : Δ.Hom Ξ}
    (hf : Subst.Rel f f') (hg : Subst.Rel g g') :
    Subst.Rel (Hom.comp f g) (Hom.comp f' g') :=
  Eq_sub.toAgreement (Eq_sub.comp Ξ.wf Δ.wf Γ.wf g.2.toWf_sub g'.2.toWf_sub
    f.2.toWf_sub f'.2.toWf_sub hg.toEq_sub hf.toEq_sub)

end Ctx
