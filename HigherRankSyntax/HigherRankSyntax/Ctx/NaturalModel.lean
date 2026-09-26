import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.MorphismProperty.Representable
import HigherRankSyntax.Ctx.Telescope

/-!
# The natural model

`Tm` is the presheaf of telescopes with a filling, modulo equality of the
telescopes and agreement of the fillings, and `q : Tm ⟶ Ty` forgets the filling.
For a telescope `Θ` over `Γ`, the generic telescope with a filling over `Γ`
extended by `Θ`, the projection, `q` and `Θ` form a pullback square, so `q` is
relatively representable.
-/

open CategoryTheory

namespace Ctx

/-- A telescope over a context class together with a filling of it. -/
def Ob.Term (X : Ob) : Type := Σ Θ : Ob.Tele X, Ob.Fill X Θ

/-- Two telescopes with fillings declare the same arity, are equal, and their
fillings agree. -/
def Ob.Term.Rel {X : Ob} : Ob.Term X → Ob.Term X → Prop
  | ⟨⟨Ω, Θ, _⟩, σ, _⟩, ⟨⟨Ω', Θ', _⟩, σ', _⟩ =>
      ∃ h : Ω = Ω', Ob.Tele.Eq X (h ▸ Θ) Θ' ∧ Ob.Fill.Eq X (h ▸ Θ) (h ▸ σ) σ'

theorem Ob.Term.Rel.refl {X : Ob} (t : Ob.Term X) :
  Ob.Term.Rel t t
  := by
  obtain ⟨_⟩ := X
  obtain ⟨⟨_, _, hΘ⟩, _, hσ⟩ := t
  exact ⟨rfl, ⟨hΘ, Wf_t.refl hΘ⟩, hσ.1, hσ.2, Eq_s.refl hσ.2⟩

theorem Ob.Term.Rel.symm {X : Ob} {t t' : Ob.Term X} (h : Ob.Term.Rel t t') :
  Ob.Term.Rel t' t
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t
  obtain ⟨⟨_, _, hΘ'⟩, _, hσ'⟩ := t'
  obtain ⟨rfl, ⟨hΘ, he⟩, _, hσ, hst⟩ := h
  have hsym := Eq_t.symm Γ.wf he
  have hσ'Θ := Wf_s.ofEq_t Γ.wf hσ'.2 hsym
  use rfl, ⟨hΘ', hsym⟩, hΘ', hσ'.2
  apply Eq_s.ofEq_t Γ.wf (Eq_s.symm Γ.wf hst hΘ hσ hσ'Θ) hσ'Θ he

theorem Ob.Term.Rel.trans
    {X : Ob} {t t' t'' : Ob.Term X}
    (h : Ob.Term.Rel t t') (h' : Ob.Term.Rel t' t'') :
  Ob.Term.Rel t t''
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t'
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t''
  obtain ⟨rfl, ⟨hΘ, he⟩, _, hσ, hst⟩ := h
  obtain ⟨rfl, ⟨_, he'⟩, _, hσ', hst'⟩ := h'
  have hsym := Eq_t.symm Γ.wf he
  have hσ'Θ := Wf_s.ofEq_t Γ.wf hσ' hsym
  use rfl, ⟨hΘ, Eq_t.trans Γ.wf hΘ he he'⟩, hΘ, hσ
  apply Eq_s.trans Γ.wf hst (Eq_s.ofEq_t Γ.wf hst' hσ' hsym) hΘ hσ hσ'Θ

/-- The setoid of telescopes with a filling over `X` under `Ob.Term.Rel`. -/
def Ob.Term.setoid (X : Ob) : Setoid (Ob.Term X) where
  r := Ob.Term.Rel
  iseqv := ⟨Ob.Term.Rel.refl, Ob.Term.Rel.symm, Ob.Term.Rel.trans⟩

/-- Telescopes with fillings whose telescopes and fillings are equal are equal. -/
theorem Ob.Term.ext
    {X : Ob} {Ω : C.Arity} {Θ Θ' : dTel X.arity Ω}
    {hΘ : Ob.Tele.Wf X Θ} {hΘ' : Ob.Tele.Wf X Θ'}
    {τ τ' : _root_.Subst Ω X.arity} {hτ : Ob.Fill.Wf X Θ τ} {hτ' : Ob.Fill.Wf X Θ' τ'}
    (h : Θ = Θ') (h' : τ = τ') :
  (⟨⟨Ω, Θ, hΘ⟩, τ, hτ⟩ : Ob.Term X) = ⟨⟨Ω, Θ', hΘ'⟩, τ', hτ'⟩
  := by
  subst h
  subst h'
  rfl

theorem Ob.Fill.Wf.subst {X Y : Ob} (σ : Ob.Subst X Y) (t : Ob.Term Y) :
  Ob.Fill.Wf X (Ob.Tele.subst σ t.1).telescope (_root_.Subst.applyEach σ.1 t.2.1)
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_⟩ := Y
  constructor
  · apply Wf_t.subst_ambient σ.2.toWf_sub t.2.2.1
  · apply Wf_s.subst_ambient σ.2.toWf_sub t.2.2.2

/-- The filling `σ` substituted into the telescope of `t` and into every filler
of its filling. -/
def Ob.Term.subst {X Y : Ob} (σ : Ob.Subst X Y) (t : Ob.Term Y) : Ob.Term X :=
  ⟨Ob.Tele.subst σ t.1, _root_.Subst.applyEach σ.1 t.2.1, Ob.Fill.Wf.subst σ t⟩

theorem Ob.Term.Rel.subst
    {X Y : Ob} {σ σ' : Ob.Subst X Y} {t t' : Ob.Term Y}
    (hσ : Ob.Subst.Rel X Y σ.1 σ'.1) (ht : Ob.Term.Rel t t') :
  Ob.Term.Rel (Ob.Term.subst σ t) (Ob.Term.subst σ' t')
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Δ⟩ := Y
  obtain ⟨⟨_, _, _⟩, _, _⟩ := t
  obtain ⟨⟨_, _, hΘ'⟩, _, hτ'⟩ := t'
  obtain ⟨rfl, ⟨hΘ, he⟩, _, hτ, hst⟩ := ht
  have hΘσ := Wf_t.subst_ambient σ.2.toWf_sub hΘ
  have hτσ := Wf_s.subst_ambient σ.2.toWf_sub hτ
  use rfl
  constructor
  · use hΘσ
    apply Eq_t.trans Γ.wf hΘσ (Eq_t.subst_ambient σ.2.toWf_sub he)
    apply Eq_t.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hσ.2.toEq_sub hΘ'
  · use hΘσ, hτσ
    have hτ'Θ := Wf_s.ofEq_t Δ.wf hτ'.2 (Eq_t.symm Δ.wf he)
    have hτ'σ := Wf_s.subst_ambient σ.2.toWf_sub hτ'Θ
    apply Eq_s.trans Γ.wf (Eq_s.subst_ambient σ.2.toWf_sub hst) ?_ hΘσ hτσ hτ'σ
    apply Eq_s.agree Δ.wf Γ.wf σ.2.toWf_sub σ'.2.toWf_sub hσ.2.toEq_sub hΘ hτ'Θ

/-- The presheaf sending a context class `X` to the classes of telescopes with a
filling over `X`, a filling acting by substitution into the telescope and into
every filler. -/
def Tm : Obᵒᵖ ⥤ Type where
  obj X := Quotient (Ob.Term.setoid X.unop)
  map {X Y} f :=
    TypeCat.ofHom (Quotient.map₂ (sa := Ob.Subst.setoid Y.unop X.unop)
      (sb := Ob.Term.setoid X.unop) (sc := Ob.Term.setoid Y.unop)
      Ob.Term.subst (fun _ _ hσ _ _ ht => Ob.Term.Rel.subst hσ ht) f.unop)
  map_id X := by
    ext t
    obtain ⟨⟨⟨_, Θ, _⟩, _, _⟩⟩ := t
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext (dTel.actBase_id Θ)
    funext Λ i
    apply act_id
  map_comp f g := by
    obtain ⟨⟨σ⟩⟩ := f
    obtain ⟨⟨θ⟩⟩ := g
    ext t
    obtain ⟨⟨⟨_, Θ, _⟩, _, _⟩⟩ := t
    apply congrArg (Quotient.mk _)
    apply Ob.Term.ext (dTel.actBase_comp σ.1 θ.1 Θ)
    funext Λ i
    apply act_comp (Γ := 1)

theorem Ob.Term.Rel.tele {X : Ob} {t t' : Ob.Term X} (h : Ob.Term.Rel t t') :
  Ob.Tele.Rel t.1 t'.1
  := ⟨h.1, h.2.1⟩

/-- Sends the class of a telescope with a filling to the class of its telescope. -/
def Ob.Term.tele {X : Ob} :
    Quotient (Ob.Term.setoid X) → Quotient (Ob.Tele.setoid X) :=
  Quotient.map Sigma.fst (fun _ _ h => Ob.Term.Rel.tele h)

/-- The natural transformation forgetting the filling. -/
def q : Tm ⟶ Ty where
  app X := TypeCat.ofHom (Ob.Term.tele (X := X.unop))
  naturality _ _ f := by
    obtain ⟨⟨_⟩⟩ := f
    ext t
    obtain ⟨_⟩ := t
    rfl

/-- The setoid, under `Ob.Term.Rel`, of the telescopes with a filling whose
telescope is equal to `Θ`. -/
def Ob.Term.fibreSetoid {X : Ob} (Θ : Ob.Tele X) :
    Setoid { s : Ob.Term X // Ob.Tele.Rel s.1 Θ } where
  r a b := Ob.Term.Rel a.1 b.1
  iseqv := ⟨fun a => Ob.Term.Rel.refl a.1, Ob.Term.Rel.symm, Ob.Term.Rel.trans⟩

theorem Ob.Term.fibre_map
    {X : Ob} {Θ : Ob.Tele X}
    (a b : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }) (h : Ob.Term.Rel a.1 b.1) :
  Ob.Fill.Rel (Ob.Fill.ofRel a.2 a.1.2) (Ob.Fill.ofRel b.2 b.1.2)
  := by
  obtain ⟨Ξ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨⟨⟨_, _, _⟩, _, hτ⟩, ⟨rfl, hΘ, he⟩⟩ := a
  obtain ⟨⟨⟨_, _, _⟩, _, _⟩, ⟨rfl, _, _⟩⟩ := b
  obtain ⟨_, _, _, _, hst⟩ := h
  use Wf_t.ofEq_t Ξ.wf hΘ he, Wf_s.ofEq_t Ξ.wf hτ.2 he
  apply Eq_s.ofEq_t Ξ.wf hst hτ.2 he

theorem Ob.Term.fibre_comap
    {X : Ob} {Θ : Ob.Tele X}
    (τ τ' : Ob.Fill X Θ) (h : Ob.Fill.Rel τ τ') :
  Ob.Term.Rel (⟨Θ, τ⟩ : Ob.Term X) ⟨Θ, τ'⟩
  := by
  obtain ⟨_⟩ := X
  obtain ⟨_, _, hΘ⟩ := Θ
  exact ⟨rfl, ⟨hΘ, Wf_t.refl hΘ⟩, h⟩

theorem Ob.Term.fibre_left
    {X : Ob} {Θ : Ob.Tele X}
    (s : { s : Ob.Term X // Ob.Tele.Rel s.1 Θ }) :
  Ob.Term.Rel (⟨Θ, Ob.Fill.ofRel s.2 s.1.2⟩ : Ob.Term X) s.1
  := by
  obtain ⟨Ξ⟩ := X
  obtain ⟨_, _, hΘ⟩ := Θ
  obtain ⟨⟨⟨_, _, _⟩, _, hτ⟩, ⟨rfl, _, he⟩⟩ := s
  have hτΘ := Wf_s.ofEq_t Ξ.wf hτ.2 he
  exact ⟨rfl, ⟨hΘ, Eq_t.symm Ξ.wf he⟩, hΘ, hτΘ, Eq_s.refl hτΘ⟩

/-- Classes of telescopes with a filling whose telescope is equal to `Θ`
correspond to classes of fillings of `Θ`. -/
def Ob.Term.fibreEquiv {X : Ob} (Θ : Ob.Tele X) :
    Quotient (Ob.Term.fibreSetoid Θ) ≃ Quotient (Ob.Fill.setoid Θ) where
  toFun := Quotient.map (fun s => Ob.Fill.ofRel s.2 s.1.2) Ob.Term.fibre_map
  invFun := Quotient.map (fun τ => ⟨⟨Θ, τ⟩, Ob.Tele.Rel.refl Θ⟩)
    (fun _ _ h => Ob.Term.fibre_comap _ _ h)
  left_inv := by
    rintro ⟨s⟩
    apply Quotient.sound (Ob.Term.fibre_left s)
  right_inv := by
    rintro ⟨_⟩
    rfl

/-- `Γ.ambient ⋈ Θ.telescope` renamed into the arity of `Ξ` is `Γ.ambient` renamed
into the arity of `Ξ`, concatenated with `Θ.telescope` renamed along
`Renaming.inr`. -/
theorem weaken_extend (Ξ Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
  dTel.rename (Renaming.fromUnit Ξ.arity) (Γ.ambient ⋈ Θ.telescope)
    = dTel.concatenate (dTel.rename (Renaming.fromUnit Ξ.arity) Γ.ambient)
        (dTel.rename (Renaming.inr Ξ.arity Γ.arity) Θ.telescope)
  := by
  rw [dTel.rename_concatenate, Renaming.fromUnit_extend]
  rfl

/-- The restriction to the slots of `Γ` of a filling from `X` to `Γ` extended by
`Θ` is a filling from `X` to `Γ`. -/
theorem Ob.Subst.Wf.left {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (extend Γ Θ)) :
  Ob.Subst.Wf X Γ.toOb (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w))
  := by
  obtain ⟨Ξ⟩ := X
  apply Wf_s.concatenate_left (Θ := dTel.rename (Renaming.fromUnit Ξ.arity) Γ.ambient)
    (X := dTel.rename (Renaming.inr Ξ.arity Γ.arity) Θ.telescope)
  rw [← weaken_extend]
  apply κ.2

/-- The fillers at the slots of `Θ` of a filling `κ` from `X` to `Γ` extended by
`Θ` fill `Θ` with the restriction of `κ` to `Γ` substituted. -/
theorem Ob.Fill.Wf.right {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (extend Γ Θ)) :
  Ob.Fill.Wf X
    (dTel.actBase (fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w)) Θ.telescope)
    (fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z))
  := by
  obtain ⟨Ξ⟩ := X
  constructor
  · apply Wf_t.subst_ambient (Ob.Subst.Wf.left κ).toWf_sub Θ.wf
  · rw [← dTel.instantiate_weaken]
    apply Wf_s.concatenate_right (Θ := dTel.rename (Renaming.fromUnit Ξ.arity) Γ.ambient)
      (X := dTel.rename (Renaming.inr Ξ.arity Γ.arity) Θ.telescope)
    rw [← weaken_extend]
    apply κ.2

/-- A filling `σ` from `X` to `Γ` and a filling of `Θ` with `σ` substituted pair
to a filling from `X` to `Γ` extended by `Θ`. -/
theorem Ob.Subst.Wf.pair
    {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (σ : Ob.Subst X Γ.toOb) (τ : _root_.Subst Θ.arity X.arity)
    (hτ : Ob.Fill.Wf X (dTel.actBase σ.1 Θ.telescope) τ) :
  Ob.Subst.Wf X (extend Γ Θ) (Subst.copair σ.1 τ)
  := by
  obtain ⟨Ξ⟩ := X
  apply Eq.mpr (congrArg (fun T => Wf_s Ξ.ambient T _) (weaken_extend Ξ Γ Θ))
  apply Wf_s.concatenate σ.2
  convert hτ.2 using 1
  apply dTel.instantiate_weaken

/-- The restriction to the slots of `Γ` of a filling from `X` to `Γ` extended by
`Θ`. -/
def Ob.Subst.left {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (extend Γ Θ)) : Ob.Subst X Γ.toOb :=
  ⟨fun ⦃α⦄ (w : Γ.arity ∋ α) => κ.1 (C.inl w), Ob.Subst.Wf.left κ⟩

/-- The fillers at the slots of `Θ` of a filling from `X` to `Γ` extended by
`Θ`. -/
def Ob.Subst.right {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (extend Γ Θ)) : _root_.Subst Θ.arity X.arity :=
  fun ⦃α⦄ (z : Θ.arity ∋ α) => κ.1 (C.inr z)

/-- Fillings from `X` to `Γ` extended by `Θ` correspond to pairs of a filling `σ`
from `X` to `Γ` and a filling of `Θ` with `σ` substituted. -/
def splitEquiv (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Ob.Subst X (extend Γ Θ) ≃
      { p : Ob.Subst X Γ.toOb × _root_.Subst Θ.arity X.arity //
          Ob.Fill.Wf X (dTel.actBase p.1.1 Θ.telescope) p.2 } where
  toFun κ := ⟨(κ.left, κ.right), Ob.Fill.Wf.right κ⟩
  invFun p := ⟨Subst.copair p.1.1.1 p.1.2, Ob.Subst.Wf.pair p.1.1 p.1.2 p.2⟩
  left_inv κ := Subtype.ext (Subst.copair_eta κ.1)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subst.copair_left
    · apply Subst.copair_right

/-- Two fillings from `X` to `Γ` extended by `Θ` agree exactly when their
restrictions to `Γ` agree and their fillers at the slots of `Θ` agree as
fillings of `Θ` with the first restriction substituted. -/
theorem splitEquiv_rel
    (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (κ κ' : Ob.Subst X (extend Γ Θ)) :
  Ob.Subst.Rel X (extend Γ Θ) κ.1 κ'.1
    ↔ Ob.Subst.Rel X Γ.toOb κ.left.1 κ'.left.1 ∧
        Ob.Fill.Eq X (dTel.actBase κ.left.1 Θ.telescope) κ.right κ'.right
  := by
  obtain ⟨Ξ⟩ := X
  constructor
  · rintro ⟨hwf, heq⟩
    rw [weaken_extend] at hwf heq
    have hleft := Wf_s.concatenate_left hwf
    constructor
    · exact ⟨hleft, Eq_s.concatenate_left heq⟩
    · use Wf_t.subst_ambient hleft.toWf_sub Θ.wf
      constructor
      · rw [← dTel.instantiate_weaken]
        apply Wf_s.concatenate_right hwf
      · rw [← dTel.instantiate_weaken]
        apply Eq_s.concatenate_right heq
  · rintro ⟨⟨hσ, hst⟩, _, hτ, htt⟩
    rw [← dTel.instantiate_weaken] at hτ htt
    constructor
    · rw [weaken_extend, ← Subst.copair_eta κ.1]
      apply Wf_s.concatenate hσ hτ
    · rw [weaken_extend, ← Subst.copair_eta κ.1, ← Subst.copair_eta κ'.1]
      apply Eq_s.concatenate hst htt

section

variable {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}

/-- A telescope with a filling over `X` together with a filling `σ` from `X` to
`Γ`, such that the telescope is equal to `Θ` with `σ` substituted. -/
def Ob.Pair (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) : Type :=
  { p : Ob.Term X × Ob.Subst X Γ.toOb //
      Ob.Tele.Rel p.1.1 (Ob.Tele.subst p.2 Θ) }

/-- The setoid on `Ob.Pair X Γ Θ` given by `Ob.Term.Rel` on the telescopes with a
filling and `Ob.Subst.Rel` on the fillings from `X` to `Γ`. -/
def Ob.Pair.setoid (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Setoid (Ob.Pair X Γ Θ) where
  r a b := Ob.Term.Rel a.1.1 b.1.1 ∧ Ob.Subst.Rel X Γ.toOb a.1.2.1 b.1.2.1
  iseqv.refl a := ⟨Ob.Term.Rel.refl a.1.1, Ob.Subst.Rel.refl a.1.2⟩
  iseqv.symm h := ⟨Ob.Term.Rel.symm h.1, Ob.Subst.Rel.symm h.2⟩
  iseqv.trans h h' := ⟨Ob.Term.Rel.trans h.1 h'.1, Ob.Subst.Rel.trans h.2 h'.2⟩

/-- The filling carried by `a`, as a filling of `Θ` with `a.1.2` substituted. -/
def Ob.Pair.fill {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb} (a : Ob.Pair X Γ Θ) :
    Ob.Fill X (Ob.Tele.subst a.1.2 Θ) :=
  Ob.Fill.ofRel a.2 a.1.1.2

/-- The filling from `X` to `Γ` extended by `Θ` that is `a.1.2` on the slots of
`Γ` and `a.fill` on the slots of `Θ`. -/
def Ob.Pair.subst {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb} (a : Ob.Pair X Γ Θ) :
    Ob.Subst X (extend Γ Θ) :=
  (splitEquiv X Γ Θ).symm ⟨(a.1.2, a.fill.1), a.fill.2⟩

/-- The telescope `Θ` with `κ.left` substituted, filled by `κ.right`, paired with
`κ.left`. -/
def Ob.Subst.toPair {X : Ob} {Γ : Ctx} {Θ : Ob.Tele Γ.toOb}
    (κ : Ob.Subst X (extend Γ Θ)) : Ob.Pair X Γ Θ :=
  ⟨(⟨Ob.Tele.subst κ.left Θ, κ.right, Ob.Fill.Wf.right κ⟩, κ.left),
    Ob.Tele.Rel.refl _⟩

theorem Ob.Subst.toPair_subst (κ : Ob.Subst X (extend Γ Θ)) :
  κ.toPair.subst = κ
  := (splitEquiv X Γ Θ).left_inv κ

theorem Ob.Pair.subst_toPair (a : Ob.Pair X Γ Θ) :
  Ob.Term.Rel a.subst.toPair.1.1 a.1.1
    ∧ Ob.Subst.Rel X Γ.toOb a.subst.toPair.1.2.1 a.1.2.1
  := by
  obtain ⟨Ξ⟩ := X
  obtain ⟨⟨⟨⟨_, _, _⟩, τ, hτ⟩, σ⟩, ⟨rfl, hwf, heq⟩⟩ := a
  have hl := Subst.copair_left σ.1 τ
  have hwfσ := Wf_t.ofEq_t Ξ.wf hwf heq
  have hτσ := Wf_s.ofEq_t Ξ.wf hτ.2 heq
  constructor
  · use rfl
    constructor
    · apply Eq.mpr (congrArg (fun s => Ob.Tele.Eq ⟦Ξ⟧ (dTel.actBase s Θ.telescope) _) hl)
      exact ⟨hwfσ, Eq_t.symm Ξ.wf heq⟩
    · apply Eq.mpr (congrArg₂ (fun s (t : _root_.Subst Θ.arity Ξ.arity) =>
        Ob.Fill.Eq ⟦Ξ⟧ (dTel.actBase s Θ.telescope) t τ) hl (Subst.copair_right σ.1 τ))
      exact ⟨hwfσ, hτσ, Eq_s.refl hτσ⟩
  · convert Ob.Subst.Rel.refl σ using 2
    apply Subtype.ext hl

theorem Ob.Pair.subst_congr
    (a b : Ob.Pair X Γ Θ)
    (h : Ob.Term.Rel a.1.1 b.1.1 ∧ Ob.Subst.Rel X Γ.toOb a.1.2.1 b.1.2.1) :
  Ob.Subst.Rel X (extend Γ Θ) a.subst.1 b.subst.1
  := by
  obtain ⟨Ξ⟩ := X
  obtain ⟨⟨⟨⟨_, _, _⟩, τ, hτ⟩, σ⟩, ⟨rfl, hwfa, heqa⟩⟩ := a
  obtain ⟨⟨⟨⟨_, _, _⟩, τ', _⟩, σ'⟩, ⟨rfl, _, _⟩⟩ := b
  obtain ⟨⟨_, ⟨_, _⟩, _, _, hst⟩, hσσ⟩ := h
  apply (splitEquiv_rel _ Γ Θ _ _).mpr
  constructor
  · convert hσσ using 2
    · apply Subtype.ext (Subst.copair_left σ.1 τ)
    · apply Subtype.ext (Subst.copair_left σ'.1 τ')
  · have hττ' : Ob.Fill.Eq ⟦Ξ⟧ (dTel.actBase σ.1 Θ.telescope) τ τ' := by
      use Wf_t.ofEq_t Ξ.wf hwfa heqa, Wf_s.ofEq_t Ξ.wf hτ.2 heqa
      apply Eq_s.ofEq_t Ξ.wf hst hτ.2 heqa
    convert hττ' using 2
    · apply Subst.copair_left
    · apply Subst.copair_right
    · apply Subst.copair_right

theorem Ob.Subst.toPair_congr
    (κ κ' : Ob.Subst X (extend Γ Θ))
    (h : Ob.Subst.Rel X (extend Γ Θ) κ.1 κ'.1) :
  Ob.Term.Rel κ.toPair.1.1 κ'.toPair.1.1
    ∧ Ob.Subst.Rel X Γ.toOb κ.toPair.1.2.1 κ'.toPair.1.2.1
  := by
  obtain ⟨hσ, hfill⟩ := (splitEquiv_rel X Γ Θ κ κ').mp h
  obtain ⟨_, htele⟩ := Ob.Tele.Rel.subst hσ (Ob.Tele.Rel.refl Θ)
  exact ⟨⟨rfl, htele, hfill⟩, hσ⟩

/-- Classes of pairs in `Ob.Pair X Γ Θ` correspond to morphisms from `X` to `Γ`
extended by `Θ`. -/
def pairEquiv (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    Quotient (Ob.Pair.setoid X Γ Θ) ≃ (X ⟶ extend Γ Θ) where
  toFun := Quotient.map Ob.Pair.subst (fun _ _ h => Ob.Pair.subst_congr _ _ h)
  invFun := Quotient.map Ob.Subst.toPair (fun _ _ h => Ob.Subst.toPair_congr _ _ h)
  left_inv := by
    rintro ⟨a⟩
    apply Quotient.sound (Ob.Pair.subst_toPair a)
  right_inv := by
    rintro ⟨κ⟩
    apply congrArg (Quotient.mk _) (Ob.Subst.toPair_subst κ)

end

section

variable (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)

/-- The telescope `Θ` with its base renamed along `Renaming.inl`, as a telescope
over `Γ` extended by `Θ`. -/
def genericTele : Ob.Tele (extend Γ Θ) :=
  ⟨Θ.arity, _, Wf_t.weaken (Ambient.Renaming.weaken Γ.ambient Θ.telescope) Θ.wf⟩

theorem generic_wf :
  Ob.Fill.Wf (extend Γ Θ) (genericTele Γ Θ).telescope (_root_.Subst.instId Γ.arity Θ.arity)
  := ⟨(genericTele Γ Θ).wf, Wf_s.eta Γ.ambient Θ.telescope Θ.wf⟩

/-- The telescope `genericTele Γ Θ` with the filling `Subst.instId Γ.arity Θ.arity`,
which sends each slot `z` of `Θ` to the η-expansion of `C.inr z`. -/
def generic : Ob.Term (extend Γ Θ) :=
  ⟨genericTele Γ Θ, _root_.Subst.instId Γ.arity Θ.arity, generic_wf Γ Θ⟩

theorem generic_tele :
  Ob.Term.tele (Quotient.mk (Ob.Term.setoid (extend Γ Θ)) (generic Γ Θ))
    = Ty.map (projection Γ Θ).op ⟦Θ⟧
  := by
  apply congrArg (Quotient.mk _)
  symm
  apply Ob.Tele.ext (Θ' := (genericTele Γ Θ).telescope)
  apply dTel.actBase_ofRenaming

end

section

variable (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)

/-- For a class of pairs `(t, σ)` of a telescope with a filling over `X` and a
filling from `X` to `Γ`, the telescope of `t` is equal to `Θ` with `σ`
substituted. -/
def fibrePred :
    Quotient ((Ob.Term.setoid X).prod (Ob.Subst.setoid X Γ.toOb)) → Prop :=
  Quotient.lift (fun s => Ob.Tele.Rel s.1.1 (Ob.Tele.subst s.2 Θ))
    (by
      rintro _ _ ⟨hs, hσ⟩
      have hΘ := Ob.Tele.Rel.subst hσ (Ob.Tele.Rel.refl Θ)
      apply propext
      constructor
      · intro h
        apply Ob.Tele.Rel.trans (Ob.Tele.Rel.symm (Ob.Term.Rel.tele hs))
        apply Ob.Tele.Rel.trans h hΘ
      · intro h
        apply Ob.Tele.Rel.trans (Ob.Term.Rel.tele hs)
        apply Ob.Tele.Rel.trans h (Ob.Tele.Rel.symm hΘ))

theorem fibrePred_iff (p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb)) :
  (Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧)
    ↔ fibrePred X Γ Θ (Setoid.prodQuotientEquiv _ _ p)
  := by
  obtain ⟨⟨_⟩, ⟨_⟩⟩ := p
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- Pairs of a class `t` of telescopes with a filling over `X` and a morphism `σ`
from `X` to `Γ` such that `q` sends `t` to the restriction of `Θ` along `σ`
correspond to classes of `Ob.Pair X Γ Θ`. -/
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

/-- Pairs of a class `t` of telescopes with a filling over `X` and a morphism `σ`
from `X` to `Γ` such that `q` sends `t` to the restriction of `Θ` along `σ`
correspond to morphisms from `X` to `Γ` extended by `Θ`. -/
def homEquiv :
    { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }
      ≃ (X ⟶ extend Γ Θ) :=
  (fibreEquiv X Γ Θ).trans (pairEquiv X Γ Θ)

end

/-- `homEquiv` sends the restriction of `(t, s)` along `g` to `g` followed by the
image of `(t, s)`. -/
theorem homEquiv_naturality
    {X Y : Ob} (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (t : Tm.obj (Opposite.op X)) (s : X ⟶ Γ.toOb) (g : Y ⟶ X)
    (hp : Ob.Term.tele t = Ty.map s.op ⟦Θ⟧)
    (hq : Ob.Term.tele (Tm.map g.op t) = Ty.map (g ≫ s).op ⟦Θ⟧) :
  homEquiv Y Γ Θ ⟨(Tm.map g.op t, g ≫ s), hq⟩ = g ≫ homEquiv X Γ Θ ⟨(t, s), hp⟩
  := by
  obtain ⟨⟨⟨_, _, _⟩, _, _⟩⟩ := t
  obtain ⟨_⟩ := s
  obtain ⟨_⟩ := g
  obtain ⟨rfl, _⟩ := Quotient.exact hp
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  symm
  apply Subst.applyEach_copair

/-- If `q` sends `t` to the restriction of `Θ` along `s`, it sends the restriction
of `t` along `g` to the restriction of `Θ` along `g ≫ s`. -/
theorem tele_map
    {X Y : Ob} (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (t : Tm.obj (Opposite.op X)) (s : X ⟶ Γ.toOb) (g : Y ⟶ X)
    (h : Ob.Term.tele t = Ty.map s.op ⟦Θ⟧) :
  Ob.Term.tele (Tm.map g.op t) = Ty.map (g ≫ s).op ⟦Θ⟧
  := by
  calc Ob.Term.tele (Tm.map g.op t)
      = Ty.map g.op (Ob.Term.tele t) := NatTrans.naturality_apply q g.op t
    _ = _ := by rw [h, op_comp, Functor.map_comp_apply]

/-- `homEquiv X Γ Θ p` followed by the projection is the second component of
`p`. -/
theorem homEquiv_projection
    (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (p : { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }) :
  homEquiv X Γ Θ p ≫ projection Γ Θ = p.1.2
  := by
  obtain ⟨⟨⟨_⟩, ⟨σ⟩⟩, _⟩ := p
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  funext Λ w
  apply Eq.trans (act_η _ Λ (C.inl w))
  apply Subst.copair_inl

/-- Induction on a context class through its representatives. -/
theorem Ob.ind {motive : Ob → Prop} (h : ∀ Γ : Ctx, motive Γ.toOb) (X : Ob) :
  motive X
  := Quotient.ind h X

/-- `Tm` restricts the generic telescope with a filling along `homEquiv X Γ Θ p`
to the first component of `p`. -/
theorem homEquiv_generic
    (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
    (p : { p : Tm.obj (Opposite.op X) × (X ⟶ Γ.toOb) //
        Ob.Term.tele p.1 = Ty.map p.2.op ⟦Θ⟧ }) :
  Tm.map (homEquiv X Γ Θ p).op ⟦generic Γ Θ⟧ = p.1.1
  := by
  obtain ⟨⟨⟨t⟩, ⟨σ⟩⟩, hp⟩ := p
  apply Eq.trans _ (Quotient.sound (Ob.Term.fibre_left ⟨t, Quotient.exact hp⟩))
  apply congrArg (Quotient.mk _)
  apply Ob.Term.ext
  · apply Eq.trans (dTel.actBase_square (Renaming.inl Γ.arity Θ.arity) (𝟙ʳ _) _ σ.1 _ _)
    · apply dTel.rename_id
    · intro α u
      rw [Renaming.extend_id, Renaming.act_id]
      apply Subst.copair_inl
  · funext Λ z
    apply Eq.trans (act_η _ Λ (C.inr z))
    apply Subst.copair_inr

/-- The square with sides `⟦generic Γ Θ⟧`, the projection, `q` and `⟦Θ⟧`
commutes. -/
theorem q_commSq (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
  CommSq (yonedaEquiv.symm ⟦generic Γ Θ⟧)
    (yoneda.map (projection Γ Θ)) q (yonedaEquiv.symm ⟦Θ⟧)
  := by
  constructor
  ext Y κ
  apply tele_map Γ Θ ⟦generic Γ Θ⟧ (projection Γ Θ) κ (generic_tele Γ Θ)

theorem homEquiv_symm_apply
    (X : Ob) (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) (κ : X ⟶ extend Γ Θ) :
  ((homEquiv X Γ Θ).symm κ).1 = (Tm.map κ.op ⟦generic Γ Θ⟧, κ ≫ projection Γ Θ)
  := by
  have h₁ := homEquiv_generic X Γ Θ ((homEquiv X Γ Θ).symm κ)
  have h₂ := homEquiv_projection X Γ Θ ((homEquiv X Γ Θ).symm κ)
  rw [Equiv.apply_symm_apply] at h₁ h₂
  rw [h₁, h₂]

section

variable (Γ : Ctx) (Θ : Ob.Tele Γ.toOb)
  (s : Limits.PullbackCone q (yonedaEquiv.symm ⟦Θ⟧))

theorem q_cone_condition (Y : Obᵒᵖ) (x : s.pt.obj Y) :
  Ob.Term.tele (s.fst.app Y x) = Ty.map (s.snd.app Y x).op ⟦Θ⟧
  := ConcreteCategory.congr_hom (NatTrans.congr_app s.condition Y) x

/-- The lift of the cone `s` into the representable presheaf of `Γ` extended by
`Θ`, given pointwise by `homEquiv`. -/
def q_lift : s.pt ⟶ yoneda.obj (extend Γ Θ) where
  app Y := TypeCat.ofHom (fun x => homEquiv (Opposite.unop Y) Γ Θ
    ⟨(s.fst.app Y x, s.snd.app Y x), q_cone_condition Γ Θ s Y x⟩)
  naturality Y Z g := by
    ext x
    have hx := q_cone_condition Γ Θ s Y x
    apply Eq.trans _ (homEquiv_naturality Γ Θ _ _ g.unop hx (tele_map Γ Θ _ _ g.unop hx))
    apply congrArg (homEquiv (Opposite.unop Z) Γ Θ)
    apply Subtype.ext
    apply Prod.ext
    · apply ConcreteCategory.congr_hom (s.fst.naturality g) x
    · apply ConcreteCategory.congr_hom (s.snd.naturality g) x

theorem q_fac_left :
  q_lift Γ Θ s ≫ yonedaEquiv.symm ⟦generic Γ Θ⟧ = s.fst
  := by
  ext Y x
  apply homEquiv_generic

theorem q_fac_right :
  q_lift Γ Θ s ≫ yoneda.map (projection Γ Θ) = s.snd
  := by
  ext Y x
  apply homEquiv_projection

theorem q_uniq
    (m : s.pt ⟶ yoneda.obj (extend Γ Θ))
    (h₁ : m ≫ yonedaEquiv.symm ⟦generic Γ Θ⟧ = s.fst)
    (h₂ : m ≫ yoneda.map (projection Γ Θ) = s.snd) :
  m = q_lift Γ Θ s
  := by
  ext Y x
  simp only [TypeCat.Fun.toFun_apply]
  rw [← Equiv.apply_symm_apply (homEquiv (Opposite.unop Y) Γ Θ) (m.app Y x)]
  apply congrArg (homEquiv (Opposite.unop Y) Γ Θ)
  apply Subtype.ext
  rw [homEquiv_symm_apply]
  apply Prod.ext
  · apply ConcreteCategory.congr_hom (NatTrans.congr_app h₁ Y) x
  · apply ConcreteCategory.congr_hom (NatTrans.congr_app h₂ Y) x

end

/-- The square with sides `⟦generic Γ Θ⟧`, the projection, `q` and `⟦Θ⟧` is a
pullback. -/
theorem q_isPullback (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
  IsPullback (yonedaEquiv.symm ⟦generic Γ Θ⟧)
    (yoneda.map (projection Γ Θ)) q (yonedaEquiv.symm ⟦Θ⟧)
  := by
  apply IsPullback.of_isLimit' (q_commSq Γ Θ)
  apply Limits.PullbackCone.IsLimit.mk (q_commSq Γ Θ).w (q_lift Γ Θ) (q_fac_left Γ Θ)
    (q_fac_right Γ Θ)
  apply q_uniq Γ Θ

/-- `q` is relatively representable with respect to `yoneda`. -/
theorem q_representable :
  yoneda.relativelyRepresentable q
  := by
  intro a g
  obtain ⟨Γ⟩ := a
  obtain ⟨Θ, rfl⟩ := yonedaEquiv.symm.surjective g
  obtain ⟨Θ⟩ := Θ
  exact ⟨extend Γ Θ, projection Γ Θ, _, q_isPullback Γ Θ⟩

end Ctx
