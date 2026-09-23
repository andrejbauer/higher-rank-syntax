import Mathlib.CategoryTheory.Category.Basic
import HigherRankSyntax.Typing.Equivalence

/-!
# The category of contexts

A context is an arity together with a well-formed ambient over it, `Ctx.Tele Γ`
the well-formed telescopes over it, and `Ctx.Rel` their equality by 7.4 at the
empty context.  `Ob` is the contexts modulo that, and `X ⟶ Y` the fillings of `Y`
weakened into `X` modulo 9.2, with identity `Subst.id` and composition
`Subst.comp`.
-/

open CategoryTheory

/-- An arity with a well-formed ambient over it. -/
structure Ctx where
  /-- The arity whose slots the ambient declares. -/
  arity : C.Arity
  /-- The ambient. -/
  ambient : Ambient arity
  /-- The ambient is well formed. -/
  wf : Ambient.Wf ambient

namespace Ctx

/-- A well-formed telescope over a context, with its arity. -/
def Tele (Γ : Ctx) : Type :=
  Σ Ω : C.Arity, { Θ : dTel Γ.arity Ω // Wf_t Γ.ambient Θ }

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

/-- Two contexts are equal as telescopes over the empty context. -/
def Rel (Γ Γ' : Ctx) : Prop := Tele.Rel Γ.toTele Γ'.toTele

/-- 7.4 as a setoid on contexts. -/
def setoid : Setoid Ctx where
  r := Rel
  iseqv := ⟨fun Γ => Tele.Rel.refl Γ.toTele, Tele.Rel.symm, Tele.Rel.trans⟩

/-- The arities of equal contexts agree. -/
theorem Rel.arity {Γ Γ' : Ctx} (h : Ctx.Rel Γ Γ') : Γ.arity = Γ'.arity := by
  obtain ⟨e, _⟩ := h
  exact e

/-- Filling the weakening of an equal ambient over an equal ambient. -/
theorem wf_hom_iff {Ω Λ : C.Arity} {A A' : Ambient Ω} {B B' : Ambient Λ}
    (hA : Eq_t (.nil : Ambient 1) A A') (hB : Eq_t (.nil : Ambient 1) B B')
    (σ : _root_.Subst Λ Ω) :
    Wf_s A (dTel.rename (Renaming.fromUnit Ω) B) σ
      ↔ Wf_s A' (dTel.rename (Renaming.fromUnit Ω) B') σ := by
  refine ⟨fun h => Wf_s.ofEq hA h (Eq_t.weaken (Ambient.Renaming.fromEmpty A) hB),
    fun h => ?_⟩
  exact Wf_s.ofEq (Eq_t.symm Wf_t.nil hA) h
    (Eq_t.weaken (Ambient.Renaming.fromEmpty A') (Eq_t.symm Wf_t.nil hB))

/-- Agreement of fillings of the weakening of an equal ambient over an equal
ambient. -/
theorem eq_hom_iff {Ω Λ : C.Arity} {A A' : Ambient Ω} {B B' : Ambient Λ}
    (hA : Eq_t (.nil : Ambient 1) A A') (hB : Eq_t (.nil : Ambient 1) B B')
    {σ θ : _root_.Subst Λ Ω}
    (hσ : Wf_s A (dTel.rename (Renaming.fromUnit Ω) B) σ) :
    Eq_s A (dTel.rename (Renaming.fromUnit Ω) B) σ θ
      ↔ Eq_s A' (dTel.rename (Renaming.fromUnit Ω) B') σ θ := by
  have hbase := Eq_t.toBoth Eq_t.Both.nil hA
  refine ⟨fun h => Eq_s.ofBoth hbase h
      (Eq_t.toBoth hbase (Eq_t.weaken (Ambient.Renaming.fromEmpty A) hB)) hσ
      ((wf_hom_iff hA hB σ).mp hσ), fun h => ?_⟩
  have hbase' := Eq_t.toBoth Eq_t.Both.nil (Eq_t.symm Wf_t.nil hA)
  exact Eq_s.ofBoth hbase' h
    (Eq_t.toBoth hbase' (Eq_t.weaken (Ambient.Renaming.fromEmpty A')
      (Eq_t.symm Wf_t.nil hB))) ((wf_hom_iff hA hB σ).mp hσ) hσ

/-- The contexts modulo 7.4. -/
def Ob : Type := Quotient Ctx.setoid

/-- The arity a context class declares. -/
def Ob.arity (X : Ob) : C.Arity :=
  Quotient.liftOn X Ctx.arity (fun _ _ h => Rel.arity h)

/-- A filling of the weakened target over the source. -/
def Ob.Subst.Wf (X Y : Ob) : _root_.Subst Y.arity X.arity → Prop :=
  Quotient.hrecOn₂ (φ := fun X Y => _root_.Subst (Ob.arity Y) (Ob.arity X) → Prop)
    X Y (fun Γ Δ => Wf_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient))
    (by
      intro Γ Δ Γ' Δ' hΓ hΔ
      obtain ⟨_, _, _⟩ := Γ
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨_, _, _⟩ := Δ
      obtain ⟨_, _, _⟩ := Δ'
      obtain ⟨rfl, hA⟩ := hΓ
      obtain ⟨rfl, hB⟩ := hΔ
      exact heq_of_eq (funext fun σ => propext (wf_hom_iff hA hB σ)))

/-- Two fillings of the weakened target are well formed and agree. -/
def Ob.Subst.Rel (X Y : Ob) :
    _root_.Subst Y.arity X.arity → _root_.Subst Y.arity X.arity → Prop :=
  Quotient.hrecOn₂ (φ := fun X Y => _root_.Subst (Ob.arity Y) (Ob.arity X) →
      _root_.Subst (Ob.arity Y) (Ob.arity X) → Prop)
    X Y (fun Γ Δ σ θ =>
      Wf_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient) σ ∧
        Eq_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient) σ θ)
    (by
      intro Γ Δ Γ' Δ' hΓ hΔ
      obtain ⟨_, _, _⟩ := Γ
      obtain ⟨_, _, _⟩ := Γ'
      obtain ⟨_, _, _⟩ := Δ
      obtain ⟨_, _, _⟩ := Δ'
      obtain ⟨rfl, hA⟩ := hΓ
      obtain ⟨rfl, hB⟩ := hΔ
      refine heq_of_eq (funext fun σ => funext fun θ => propext ⟨?_, ?_⟩)
      · rintro ⟨hσ, hst⟩
        exact ⟨(wf_hom_iff hA hB σ).mp hσ, (eq_hom_iff hA hB hσ).mp hst⟩
      · rintro ⟨hσ, hst⟩
        have hσ' := (wf_hom_iff hA hB σ).mpr hσ
        exact ⟨hσ', (eq_hom_iff hA hB hσ').mpr hst⟩)

/-- A filling of the weakened target over the source. -/
def Ob.Subst (X Y : Ob) : Type := { σ : _root_.Subst Y.arity X.arity // Ob.Subst.Wf X Y σ }

theorem Ob.Subst.Rel.refl {X Y : Ob} (σ : Ob.Subst X Y) : Ob.Subst.Rel X Y σ.1 σ.1 := by
  refine Quotient.inductionOn₂ (motive := fun X Y => ∀ σ : Ob.Subst X Y,
    Ob.Subst.Rel X Y σ.1 σ.1) X Y ?_ σ
  intro _ _ σ
  exact ⟨σ.2, Eq_s.refl σ.2⟩

theorem Ob.Subst.Rel.symm {X Y : Ob} {σ θ : Ob.Subst X Y} (h : Ob.Subst.Rel X Y σ.1 θ.1) :
    Ob.Subst.Rel X Y θ.1 σ.1 := by
  refine Quotient.inductionOn₂ (motive := fun X Y => ∀ σ θ : Ob.Subst X Y,
    Ob.Subst.Rel X Y σ.1 θ.1 → Ob.Subst.Rel X Y θ.1 σ.1) X Y ?_ σ θ h
  intro Γ Δ _ θ h
  exact ⟨θ.2, Eq_s.symm Γ.wf h.2 (Ambient.Wf.weaken Δ.wf Γ.ambient) h.1 θ.2⟩

theorem Ob.Subst.Rel.trans {X Y : Ob} {σ θ κ : Ob.Subst X Y} (h : Ob.Subst.Rel X Y σ.1 θ.1)
    (h' : Ob.Subst.Rel X Y θ.1 κ.1) : Ob.Subst.Rel X Y σ.1 κ.1 := by
  refine Quotient.inductionOn₂ (motive := fun X Y => ∀ σ θ κ : Ob.Subst X Y,
    Ob.Subst.Rel X Y σ.1 θ.1 → Ob.Subst.Rel X Y θ.1 κ.1 → Ob.Subst.Rel X Y σ.1 κ.1) X Y ?_ σ θ κ h h'
  intro Γ Δ _ θ _ h h'
  exact ⟨h.1, Eq_s.trans Γ.wf h.2 h'.2 (Ambient.Wf.weaken Δ.wf Γ.ambient) h.1 θ.2⟩

/-- 9.2 as a setoid on the fillings between context classes. -/
def Ob.Subst.setoid (X Y : Ob) : Setoid (Ob.Subst X Y) where
  r σ θ := Ob.Subst.Rel X Y σ.1 θ.1
  iseqv := ⟨Ob.Subst.Rel.refl, Ob.Subst.Rel.symm, Ob.Subst.Rel.trans⟩

theorem Ob.Subst.Wf.id (X : Ob) : Ob.Subst.Wf X X (_root_.Subst.id X.arity) := by
  refine Quotient.inductionOn
    (motive := fun X => Ob.Subst.Wf X X (_root_.Subst.id (Ob.arity X))) X ?_
  intro Γ
  exact (Wf_sub.id Γ.wf).toFilling

/-- The identity filling. -/
def Ob.Subst.id (X : Ob) : Ob.Subst X X :=
  ⟨_root_.Subst.id X.arity, Ob.Subst.Wf.id X⟩

theorem Ob.Subst.Wf.comp {X Y Z : Ob} (f : Ob.Subst X Y) (g : Ob.Subst Y Z) :
    Ob.Subst.Wf X Z (_root_.Subst.comp (Γ := 1) g.1 f.1) := by
  refine Quotient.inductionOn₃ (motive := fun X Y Z =>
    ∀ (f : Ob.Subst X Y) (g : Ob.Subst Y Z),
      Ob.Subst.Wf X Z (_root_.Subst.comp (Γ := 1) g.1 f.1)) X Y Z ?_ f g
  intro _ _ _ f g
  exact (g.2.toWf_sub.comp f.2.toWf_sub).toFilling

/-- Composition of fillings. -/
def Ob.Subst.comp {X Y Z : Ob} (f : Ob.Subst X Y) (g : Ob.Subst Y Z) :
    Ob.Subst X Z :=
  ⟨_root_.Subst.comp (Γ := 1) g.1 f.1, Ob.Subst.Wf.comp f g⟩

theorem Ob.Subst.Rel.comp {X Y Z : Ob} {f f' : Ob.Subst X Y} {g g' : Ob.Subst Y Z}
    (hf : Ob.Subst.Rel X Y f.1 f'.1) (hg : Ob.Subst.Rel Y Z g.1 g'.1) :
    Ob.Subst.Rel X Z (Ob.Subst.comp f g).1 (Ob.Subst.comp f' g').1 := by
  refine Quotient.inductionOn₃ (motive := fun X Y Z =>
    ∀ (f f' : Ob.Subst X Y) (g g' : Ob.Subst Y Z), Ob.Subst.Rel X Y f.1 f'.1 →
      Ob.Subst.Rel Y Z g.1 g'.1 →
        Ob.Subst.Rel X Z (Ob.Subst.comp f g).1 (Ob.Subst.comp f' g').1)
    X Y Z ?_ f f' g g' hf hg
  intro Γ Δ Ξ f f' g g' hf hg
  refine ⟨(g.2.toWf_sub.comp f.2.toWf_sub).toFilling, ?_⟩
  exact Eq_sub.toAgreement (Eq_sub.comp Ξ.wf Δ.wf Γ.wf g.2.toWf_sub g'.2.toWf_sub
    f.2.toWf_sub f'.2.toWf_sub hg.2.toEq_sub hf.2.toEq_sub)

/-- 9.3: contexts and fillings, both modulo their equivalences. -/
instance : Category Ob where
  Hom X Y := Quotient (Ob.Subst.setoid X Y)
  id X := Quotient.mk (Ob.Subst.setoid X X) (Ob.Subst.id X)
  comp {X Y Z} f g :=
    Quotient.map₂ (sa := Ob.Subst.setoid X Y) (sb := Ob.Subst.setoid Y Z) (sc := Ob.Subst.setoid X Z)
      Ob.Subst.comp (fun _ _ hf _ _ hg => Ob.Subst.Rel.comp hf hg) f g
  id_comp {X Y} f := by
    refine Quotient.inductionOn f ?_
    intro σ
    refine congrArg (Quotient.mk (Ob.Subst.setoid X Y)) (Subtype.ext ?_)
    funext Λ i
    exact act_id (Ob.arity X) Λ (σ.1 i)
  comp_id {X Y} f := by
    refine Quotient.inductionOn f ?_
    intro σ
    refine congrArg (Quotient.mk (Ob.Subst.setoid X Y)) (Subtype.ext ?_)
    funext Λ i
    exact act_η σ.1 Λ i
  assoc {W X Y Z} f g h := by
    refine Quotient.inductionOn₃ f g h ?_
    intro σ θ κ
    refine congrArg (Quotient.mk (Ob.Subst.setoid W Z)) (Subtype.ext ?_)
    funext Λ i
    exact act_comp (Γ := 1) θ.1 σ.1 Λ (κ.1 i)

end Ctx
