import Mathlib.CategoryTheory.Category.Basic
import HigherRankSyntax.Typing.Equivalence

/-!
# The category of contexts

A context is an arity with a well-formed ambient whose slots form it.  Two
contexts are equal when they declare the same arity and their ambients are equal
telescopes over the empty ambient; `Ob` is the contexts modulo this equality.  A
morphism `X ⟶ Y` is a filling over the ambient of `X` of the ambient of `Y`
renamed into the arity of `X`, modulo agreement of fillings.  The identity is
`Subst.id`, and `f ≫ g` substitutes `f` into every filler of `g`.
-/

open CategoryTheory

/-- An arity with a well-formed ambient whose slots form it. -/
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

/-- Two telescopes over a context declare the same arity and are equal over its
ambient. -/
def Tele.Rel {Γ : Ctx} : Γ.Tele → Γ.Tele → Prop
  | ⟨Ω, Θ, _⟩, ⟨Ω', Θ', _⟩ => ∃ h : Ω = Ω', Eq_t Γ.ambient (h ▸ Θ) Θ'

theorem Tele.Rel.refl {Γ : Ctx} :
  ∀ Θ : Γ.Tele, Tele.Rel Θ Θ
  | ⟨_, _, hΘ⟩ => ⟨rfl, Wf_t.refl hΘ⟩

theorem Tele.Rel.symm {Γ : Ctx} {Θ Θ' : Γ.Tele} (h : Tele.Rel Θ Θ') :
  Tele.Rel Θ' Θ
  := by
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, Eq_t.symm Γ.wf h⟩

theorem Tele.Rel.trans
    {Γ : Ctx} {Θ Θ' Θ'' : Γ.Tele}
    (h : Tele.Rel Θ Θ') (h' : Tele.Rel Θ' Θ'') :
  Tele.Rel Θ Θ''
  := by
  obtain ⟨_, _, hΘ⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨_, _, _⟩ := Θ''
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, Eq_t.trans Γ.wf hΘ h h'⟩

/-- Two contexts are equal as telescopes over the empty context. -/
def Rel (Γ Γ' : Ctx) : Prop := Tele.Rel Γ.toTele Γ'.toTele

/-- The setoid of contexts under `Rel`. -/
def setoid : Setoid Ctx where
  r := Rel
  iseqv := ⟨fun Γ => Tele.Rel.refl Γ.toTele, Tele.Rel.symm, Tele.Rel.trans⟩

/-- Equal contexts declare the same arity. -/
theorem Rel.arity {Γ Γ' : Ctx} (h : Rel Γ Γ') :
  Γ.arity = Γ'.arity
  := h.1

/-- For equal ambients `A`, `A'` and equal ambients `B`, `B'`, `σ` fills over `A`
the renaming of `B` into the arity of `A` exactly when it fills over `A'` the
renaming of `B'`. -/
theorem wf_hom_iff
    {Ω Λ : C.Arity} {A A' : Ambient Ω} {B B' : Ambient Λ}
    (hA : Eq_t (.nil : Ambient 1) A A') (hB : Eq_t (.nil : Ambient 1) B B')
    (σ : _root_.Subst Λ Ω) :
  Wf_s A (dTel.rename (Renaming.fromUnit Ω) B) σ
    ↔ Wf_s A' (dTel.rename (Renaming.fromUnit Ω) B') σ
  := by
  constructor
  · intro h
    apply Wf_s.ofEq hA h
    apply Eq_t.weaken (Ambient.Renaming.fromEmpty A) hB
  · intro h
    apply Wf_s.ofEq (Eq_t.symm Wf_t.nil hA) h
    apply Eq_t.weaken (Ambient.Renaming.fromEmpty A') (Eq_t.symm Wf_t.nil hB)

/-- For equal ambients `A`, `A'` and equal ambients `B`, `B'`, and `σ` filling over
`A` the renaming of `B` into the arity of `A`, `σ` and `θ` agree as such fillings
exactly when they agree as fillings over `A'` of the renaming of `B'`. -/
theorem eq_hom_iff
    {Ω Λ : C.Arity} {A A' : Ambient Ω} {B B' : Ambient Λ}
    (hA : Eq_t (.nil : Ambient 1) A A') (hB : Eq_t (.nil : Ambient 1) B B')
    {σ θ : _root_.Subst Λ Ω}
    (hσ : Wf_s A (dTel.rename (Renaming.fromUnit Ω) B) σ) :
  Eq_s A (dTel.rename (Renaming.fromUnit Ω) B) σ θ
    ↔ Eq_s A' (dTel.rename (Renaming.fromUnit Ω) B') σ θ
  := by
  have hσ' := (wf_hom_iff hA hB σ).mp hσ
  constructor
  · intro h
    have hbase := Eq_t.toBoth Eq_t.Both.nil hA
    apply Eq_s.ofBoth hbase h _ hσ hσ'
    apply Eq_t.toBoth hbase (Eq_t.weaken (Ambient.Renaming.fromEmpty A) hB)
  · intro h
    have hbase := Eq_t.toBoth Eq_t.Both.nil (Eq_t.symm Wf_t.nil hA)
    apply Eq_s.ofBoth hbase h _ hσ' hσ
    apply Eq_t.toBoth hbase
    apply Eq_t.weaken (Ambient.Renaming.fromEmpty A') (Eq_t.symm Wf_t.nil hB)

/-- Contexts modulo `Rel`. -/
def Ob : Type := Quotient setoid

/-- The arity a context class declares. -/
def Ob.arity (X : Ob) : C.Arity :=
  Quotient.liftOn X Ctx.arity (fun _ _ h => Rel.arity h)

/-- `σ` fills, over the ambient of `X`, the ambient of `Y` renamed into the arity
of `X`. -/
def Ob.Subst.Wf (X Y : Ob) : _root_.Subst Y.arity X.arity → Prop :=
  Quotient.hrecOn₂ (φ := fun X Y => _root_.Subst (Ob.arity Y) (Ob.arity X) → Prop)
    X Y (fun Γ Δ => Wf_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hA⟩ ⟨rfl, hB⟩
      apply heq_of_eq
      funext σ
      apply propext (wf_hom_iff hA hB σ))

/-- `σ` fills, over the ambient of `X`, the ambient of `Y` renamed into the arity
of `X`, and agrees with `θ` as such a filling. -/
def Ob.Subst.Rel (X Y : Ob) :
    _root_.Subst Y.arity X.arity → _root_.Subst Y.arity X.arity → Prop :=
  Quotient.hrecOn₂ (φ := fun X Y => _root_.Subst (Ob.arity Y) (Ob.arity X) →
      _root_.Subst (Ob.arity Y) (Ob.arity X) → Prop)
    X Y (fun Γ Δ σ θ =>
      Wf_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient) σ ∧
        Eq_s Γ.ambient (dTel.rename (Renaming.fromUnit Γ.arity) Δ.ambient) σ θ)
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hA⟩ ⟨rfl, hB⟩
      apply heq_of_eq
      funext σ θ
      apply propext
      constructor
      · rintro ⟨hσ, hst⟩
        exact ⟨(wf_hom_iff hA hB σ).mp hσ, (eq_hom_iff hA hB hσ).mp hst⟩
      · rintro ⟨hσ, hst⟩
        have hσ' := (wf_hom_iff hA hB σ).mpr hσ
        exact ⟨hσ', (eq_hom_iff hA hB hσ').mpr hst⟩)

/-- The fillings, over the ambient of `X`, of the ambient of `Y` renamed into the
arity of `X`. -/
def Ob.Subst (X Y : Ob) : Type := { σ : _root_.Subst Y.arity X.arity // Ob.Subst.Wf X Y σ }

theorem Ob.Subst.Rel.refl {X Y : Ob} (σ : Ob.Subst X Y) :
  Ob.Subst.Rel X Y σ.1 σ.1
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_⟩ := Y
  exact ⟨σ.2, Eq_s.refl σ.2⟩

theorem Ob.Subst.Rel.symm
    {X Y : Ob} {σ θ : Ob.Subst X Y}
    (h : Ob.Subst.Rel X Y σ.1 θ.1) :
  Ob.Subst.Rel X Y θ.1 σ.1
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Δ⟩ := Y
  constructor
  · apply θ.2
  · apply Eq_s.symm Γ.wf h.2 (Ambient.Wf.weaken Δ.wf Γ.ambient) h.1 θ.2

theorem Ob.Subst.Rel.trans
    {X Y : Ob} {σ θ κ : Ob.Subst X Y}
    (h : Ob.Subst.Rel X Y σ.1 θ.1) (h' : Ob.Subst.Rel X Y θ.1 κ.1) :
  Ob.Subst.Rel X Y σ.1 κ.1
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Δ⟩ := Y
  constructor
  · apply h.1
  · apply Eq_s.trans Γ.wf h.2 h'.2 (Ambient.Wf.weaken Δ.wf Γ.ambient) h.1 θ.2

/-- The setoid of fillings from `X` to `Y` under `Ob.Subst.Rel`. -/
def Ob.Subst.setoid (X Y : Ob) : Setoid (Ob.Subst X Y) where
  r σ θ := Ob.Subst.Rel X Y σ.1 θ.1
  iseqv := ⟨Ob.Subst.Rel.refl, Ob.Subst.Rel.symm, Ob.Subst.Rel.trans⟩

theorem Ob.Subst.Wf.id (X : Ob) :
  Ob.Subst.Wf X X (_root_.Subst.id X.arity)
  := by
  obtain ⟨Γ⟩ := X
  apply (Wf_sub.id Γ.wf).toFilling

/-- The identity filling. -/
def Ob.Subst.id (X : Ob) : Ob.Subst X X :=
  ⟨_root_.Subst.id X.arity, Ob.Subst.Wf.id X⟩

theorem Ob.Subst.Wf.comp {X Y Z : Ob} (f : Ob.Subst X Y) (g : Ob.Subst Y Z) :
  Ob.Subst.Wf X Z (_root_.Subst.comp (Γ := 1) g.1 f.1)
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_⟩ := Y
  obtain ⟨_⟩ := Z
  apply (g.2.toWf_sub.comp f.2.toWf_sub).toFilling

/-- Composition of fillings: `f` substituted into every filler of `g`. -/
def Ob.Subst.comp {X Y Z : Ob} (f : Ob.Subst X Y) (g : Ob.Subst Y Z) :
    Ob.Subst X Z :=
  ⟨_root_.Subst.comp (Γ := 1) g.1 f.1, Ob.Subst.Wf.comp f g⟩

theorem Ob.Subst.Rel.comp
    {X Y Z : Ob} {f f' : Ob.Subst X Y} {g g' : Ob.Subst Y Z}
    (hf : Ob.Subst.Rel X Y f.1 f'.1) (hg : Ob.Subst.Rel Y Z g.1 g'.1) :
  Ob.Subst.Rel X Z (Ob.Subst.comp f g).1 (Ob.Subst.comp f' g').1
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Δ⟩ := Y
  obtain ⟨Ξ⟩ := Z
  constructor
  · apply Ob.Subst.Wf.comp f g
  · apply Eq_sub.toAgreement
    apply Eq_sub.comp Ξ.wf Δ.wf Γ.wf g.2.toWf_sub g'.2.toWf_sub f.2.toWf_sub f'.2.toWf_sub
    · apply hg.2.toEq_sub
    · apply hf.2.toEq_sub

/-- The category of context classes, with the classes of fillings as morphisms. -/
instance : Category Ob where
  Hom X Y := Quotient (Ob.Subst.setoid X Y)
  id X := Quotient.mk (Ob.Subst.setoid X X) (Ob.Subst.id X)
  comp {X Y Z} f g :=
    Quotient.map₂ (sa := Ob.Subst.setoid X Y) (sb := Ob.Subst.setoid Y Z)
      (sc := Ob.Subst.setoid X Z) Ob.Subst.comp (fun _ _ hf _ _ hg => Ob.Subst.Rel.comp hf hg) f g
  id_comp f := by
    obtain ⟨σ⟩ := f
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    funext Λ i
    apply act_id
  comp_id f := by
    obtain ⟨σ⟩ := f
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    funext Λ i
    apply act_η
  assoc f g h := by
    obtain ⟨σ⟩ := f
    obtain ⟨θ⟩ := g
    obtain ⟨κ⟩ := h
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    funext Λ i
    apply act_comp (Γ := 1)

end Ctx
