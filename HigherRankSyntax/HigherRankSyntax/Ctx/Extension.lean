import HigherRankSyntax.Ctx.NaturalModel

/-!
# Extension on context classes

`Ctx.extend`, `Ctx.projection` and `Ctx.generic` are stated for a representative
`Γ : Ctx`.  Here they are stated for the class `X : Ob`, and compute on `Γ.toOb`
to the representative versions.

Each is `Quotient.hrecOn` with a motive depending on the class only through its
arity and through a well-formedness proposition.  The heterogeneous equality
the recursor asks for then reduces, once the arities are identified, to
`Function.hfunext` over the proposition and to the representative-level
congruence.  Where the value is itself a class, `Ob.Subst.heq_mk` and
`Ob.Term.heq_mk` compare two classes over equal objects by their
representatives.
-/

open CategoryTheory

namespace Ctx

/-! ## Classes over equal objects -/

/-- Classes of substitutions over equal objects, with heterogeneously equal
representatives, are heterogeneously equal. -/
theorem Ob.Subst.heq_mk {X X' Y Y' : Ob} (eX : X = X') (eY : Y = Y')
    (σ : Ob.Subst X Y) (σ' : Ob.Subst X' Y') (hσ : HEq σ.1 σ'.1) :
    HEq (Quotient.mk (Ob.Subst.setoid X Y) σ)
      (Quotient.mk (Ob.Subst.setoid X' Y') σ') := by
  subst eX
  subst eY
  obtain rfl : σ = σ' := Subtype.ext (eq_of_heq hσ)
  rfl

/-- Classes of terms over equal objects, with heterogeneously equal telescopes
and fillings, are heterogeneously equal. -/
theorem Ob.Term.heq_mk {X X' : Ob} (e : X = X') {Λ : C.Arity}
    {Θ : dTel X.arity Λ} {Θ' : dTel X'.arity Λ} (hΘ : HEq Θ Θ')
    {τ : _root_.Subst Λ X.arity} {τ' : _root_.Subst Λ X'.arity} (hτ : HEq τ τ')
    (wΘ : Ob.Tele.Wf X Θ) (wΘ' : Ob.Tele.Wf X' Θ')
    (wτ : Ob.Fill.Wf X Θ τ) (wτ' : Ob.Fill.Wf X' Θ' τ') :
    HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, Θ, wΘ⟩, τ, wτ⟩)
      (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, Θ', wΘ'⟩, τ', wτ'⟩) := by
  subst e
  cases hΘ
  cases hτ
  rfl


/-- Classes of terms over equal objects whose representatives, once the arities
are identified, are related, are heterogeneously equal. -/
theorem Ob.Term.heq_mk_of_rel {X X' : Ob} (e : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {T' : dTel X'.arity Λ}
    {τ : _root_.Subst Λ X.arity} {τ' : _root_.Subst Λ X'.arity}
    (wT : Ob.Tele.Wf X T) (wT' : Ob.Tele.Wf X' T')
    (wτ : Ob.Fill.Wf X T τ) (wτ' : Ob.Fill.Wf X' T' τ')
    (h : ∀ e' : X.arity = X'.arity,
      Ob.Tele.Eq X' (e' ▸ T) T' ∧ Ob.Fill.Eq X' (e' ▸ T) (e' ▸ τ) τ') :
    HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, T, wT⟩, τ, wτ⟩)
      (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, T', wT'⟩, τ', wτ'⟩) := by
  subst e
  exact heq_of_eq (Quotient.sound ⟨rfl, h rfl⟩)

theorem Ob.Term.eq_of_heq_mk {X X' : Ob} (h : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {wT : Ob.Tele.Wf X T} {σ : _root_.Subst Λ X.arity}
    {wσ : Ob.Fill.Wf X T σ} {T' : dTel X'.arity Λ} {wT' : Ob.Tele.Wf X' T'}
    {σ' : _root_.Subst Λ X'.arity} {wσ' : Ob.Fill.Wf X' T' σ'}
    (hh : HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, T, wT⟩, σ, wσ⟩)
      (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, T', wT'⟩, σ', wσ'⟩)) :
    ∀ e : X.arity = X'.arity,
      Ob.Tele.Eq X' (e ▸ T) T' ∧ Ob.Fill.Eq X' (e ▸ T) (e ▸ σ) σ' := by
  subst h
  intro _
  obtain ⟨hΛ, hrel⟩ := Quotient.exact (eq_of_heq hh)
  exact hrel

/-! ## Extension -/

namespace Ob

/-- The class extended by a telescope, given with its well-formedness. -/
def extendRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → Ob.Tele.Wf X Θ.2 → Ob :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → Ob.Tele.Wf X Θ.2 → Ob)
    X (fun Γ Θ h => Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩)
    (by
      intro Γ Γ' hΓ
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, hAA⟩ := hΓ
      apply Function.hfunext rfl
      intro Θ Θ' hΘ
      cases hΘ
      apply Function.hfunext
        (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h h' _
      exact heq_of_eq (Ctx.extend_congr hAA (Wf_t.refl h)))

/-- Extension respects equality of telescopes. -/
theorem extend_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
    extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf
      = extendRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf := by
  refine Ob.ind (motive := fun X => ∀ Θ Θ' : Ob.Tele X, Ob.Tele.Rel Θ Θ' →
    extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf
      = extendRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf) ?_ X Θ Θ' h
  intro Γ Θ Θ' h
  obtain ⟨Λ, T, hT⟩ := Θ
  obtain ⟨Λ', T', hT'⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  exact Ctx.extend_congr (Wf_t.refl Γ.wf) hTT'

/-- 10.4 on a context class: the class extended by a telescope. -/
def extend (X : Ob) (a : Ty.obj (Opposite.op X)) : Ob :=
  Quotient.liftOn a (fun Θ => extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (extend_congr X)

theorem extend_mk (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    extend Γ.toOb (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ) = Ctx.extend Γ Θ :=
  rfl

/-! ## Projection -/

/-- The projection off an extension, given the telescope with its
well-formedness. -/
def projectionRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Ob.Tele.Wf X Θ.2) →
      (extendRaw X Θ h ⟶ X) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Ob.Tele.Wf X Θ.2) →
        (extendRaw X Θ h ⟶ X))
    X (fun Γ Θ h => Ctx.projection Γ ⟨Θ.1, Θ.2, h⟩)
    (by
      intro Γ Γ' hΓ
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, hAA⟩ := hΓ
      apply Function.hfunext rfl
      intro Θ Θ' hΘ
      cases hΘ
      apply Function.hfunext
        (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h h' _
      have eY : Ctx.toOb ⟨Ω, A, hA⟩ = Ctx.toOb ⟨Ω, A', hA'⟩ :=
        Quotient.sound ⟨rfl, hAA⟩
      exact Ob.Subst.heq_mk (Ctx.extend_congr hAA (Wf_t.refl h)) eY _ _ HEq.rfl)

/-- The projection respects equality of telescopes. -/
theorem projection_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
    HEq (projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
      (projectionRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf) := by
  refine Ob.ind (motive := fun X => ∀ Θ Θ' : Ob.Tele X, Ob.Tele.Rel Θ Θ' →
    HEq (projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
      (projectionRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf)) ?_ X Θ Θ' h
  intro Γ Θ Θ' h
  obtain ⟨Λ, T, hT⟩ := Θ
  obtain ⟨Λ', T', hT'⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  exact Ob.Subst.heq_mk (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT') rfl _ _ HEq.rfl

/-- 10.4 on a context class: the projection off an extension. -/
def projection (X : Ob) (a : Ty.obj (Opposite.op X)) : extend X a ⟶ X :=
  Quotient.hrecOn (motive := fun a => extend X a ⟶ X) a
    (fun Θ => projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf) (projection_congr X)

theorem projection_mk (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    projection Γ.toOb (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ) = Ctx.projection Γ Θ :=
  rfl

/-! ## The generic term -/

/-- The generic term of an extension, given the telescope with its
well-formedness. -/
def genericRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Ob.Tele.Wf X Θ.2) →
      Tm.obj (Opposite.op (extendRaw X Θ h)) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Ob.Tele.Wf X Θ.2) →
        Tm.obj (Opposite.op (extendRaw X Θ h)))
    X (fun Γ Θ h => Quotient.mk (Ob.Term.setoid (Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩))
      (Ctx.generic Γ ⟨Θ.1, Θ.2, h⟩))
    (by
      intro Γ Γ' hΓ
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, hAA⟩ := hΓ
      apply Function.hfunext rfl
      intro Θ Θ' hΘ
      cases hΘ
      apply Function.hfunext
        (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h h' _
      exact Ob.Term.heq_mk (Ctx.extend_congr hAA (Wf_t.refl h)) HEq.rfl HEq.rfl
        _ _ _ _)

/-- The generic term respects equality of telescopes. -/
theorem generic_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
    HEq (genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
      (genericRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf) := by
  refine Ob.ind (motive := fun X => ∀ Θ Θ' : Ob.Tele X, Ob.Tele.Rel Θ Θ' →
    HEq (genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
      (genericRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf)) ?_ X Θ Θ' h
  intro Γ Θ Θ' h
  obtain ⟨Λ, T, hT⟩ := Θ
  obtain ⟨Λ', T', hT'⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  have hcat : Eq_t (.nil : Ambient 1) (Γ.ambient ⋈ T) (Γ.ambient ⋈ T') :=
    Eq_t.concatenate (Wf_t.refl Γ.wf) hTT'
  have hwf : Wf_t (Γ.ambient ⋈ T') (dTel.rename (Renaming.inl Γ.arity Λ) T) :=
    Wf_t.ofEq hcat (genericTele Γ ⟨Λ, T, hT⟩).wf
  have hfill : Wf_s (Γ.ambient ⋈ T') (dTel.rename (Renaming.inl Γ.arity Λ) T)
      (_root_.Subst.instId Γ.arity Λ) :=
    Wf_s.ofEq hcat (generic_wf Γ ⟨Λ, T, hT⟩).2 (Wf_t.refl (genericTele Γ ⟨Λ, T, hT⟩).wf)
  refine Ob.Term.heq_mk_of_rel (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT') _ _ _ _ ?_
  intro _
  exact ⟨⟨hwf, Eq_t.weaken (Ambient.Renaming.weaken Γ.ambient T') hTT'⟩,
    hwf, hfill, Eq_s.refl hfill⟩

/-- 13.2 on a context class: the generic term of an extension. -/
def generic (X : Ob) (a : Ty.obj (Opposite.op X)) : Tm.obj (Opposite.op (extend X a)) :=
  Quotient.hrecOn (motive := fun a => Tm.obj (Opposite.op (extend X a))) a
    (fun Θ => genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf) (generic_congr X)

theorem generic_mk (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) :
    generic Γ.toOb (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ)
      = Quotient.mk (Ob.Term.setoid (Ctx.extend Γ Θ)) (Ctx.generic Γ Θ) :=
  rfl

/-! ## Pairing -/

/-- A filling of the base paired with a term lying over the telescope, given the
telescope and the base filling with their well-formedness. -/
def pairRaw (X : Ob) (t : Ob.Term X) (Y : Ob) :
    (Θ : Σ Ω : C.Arity, dTel Y.arity Ω) → (h : Ob.Tele.Wf Y Θ.2) →
      (σ : _root_.Subst Y.arity X.arity) → (hσ : Ob.Subst.Wf X Y σ) →
      Ob.Tele.Rel t.1 (Ob.Tele.subst ⟨σ, hσ⟩ ⟨Θ.1, Θ.2, h⟩) →
      (X ⟶ extendRaw Y Θ h) :=
  Quotient.hrecOn (motive := fun Y =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity Y) Ω) → (h : Ob.Tele.Wf Y Θ.2) →
      (σ : _root_.Subst (Ob.arity Y) X.arity) → (hσ : Ob.Subst.Wf X Y σ) →
      Ob.Tele.Rel t.1 (Ob.Tele.subst ⟨σ, hσ⟩ ⟨Θ.1, Θ.2, h⟩) →
      (X ⟶ extendRaw Y Θ h))
    Y (fun Γ Θ h σ hσ rel =>
      Quotient.mk (Ob.Subst.setoid X (Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩))
        (Ob.Pair.subst (Γ := Γ) (Θ := ⟨Θ.1, Θ.2, h⟩) ⟨(t, ⟨σ, hσ⟩), rel⟩))
    (by
      obtain ⟨Ψ, E, hE⟩ := X
      intro Γ Γ' hΓ
      obtain ⟨Ω, A, hA⟩ := Γ
      obtain ⟨Ω', A', hA'⟩ := Γ'
      obtain ⟨rfl, hAA⟩ := hΓ
      apply Function.hfunext rfl
      intro Θ Θ' hΘ
      cases hΘ
      apply Function.hfunext
        (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h h' _
      apply Function.hfunext rfl
      intro σ σ' hσσ
      cases hσσ
      apply Function.hfunext (propext (wf_hom_iff (Wf_t.refl hE) hAA σ))
      intro hσ hσ' _
      apply Function.hfunext rfl
      intro rel rel' _
      exact Ob.Subst.heq_mk rfl (Ctx.extend_congr hAA (Wf_t.refl h)) _ _ HEq.rfl)

/-- A filling of the base paired with a term lying over the class of a
telescope. -/
def pairTele (X : Ob) (t : Ob.Term X) (Y : Ob) (a : Ty.obj (Opposite.op Y))
    (σ : Ob.Subst X Y)
    (ht : Ob.Term.tele (Quotient.mk (Ob.Term.setoid X) t)
      = Ty.map (Quiver.Hom.op (Quotient.mk (Ob.Subst.setoid X Y) σ : X ⟶ Y)) a) :
    X ⟶ extend Y a :=
  Quotient.hrecOn (motive := fun a =>
      Ob.Term.tele (Quotient.mk (Ob.Term.setoid X) t)
        = Ty.map (Quiver.Hom.op (Quotient.mk (Ob.Subst.setoid X Y) σ : X ⟶ Y)) a →
      (X ⟶ extend Y a))
    a (fun Θ ht => pairRaw X t Y ⟨Θ.arity, Θ.telescope⟩ Θ.wf σ.1 σ.2 (Quotient.exact ht))
    (by
      intro Θ Θ' h
      apply Function.hfunext (congrArg (fun a => Ob.Term.tele (Quotient.mk (Ob.Term.setoid X) t)
        = Ty.map (Quiver.Hom.op (Quotient.mk (Ob.Subst.setoid X Y) σ : X ⟶ Y)) a)
        (Quotient.sound h))
      intro ht ht' _
      obtain ⟨Γ⟩ := Y
      obtain ⟨Λ, T, hT⟩ := Θ
      obtain ⟨Λ', T', hT'⟩ := Θ'
      obtain ⟨rfl, _, hTT'⟩ := h
      exact Ob.Subst.heq_mk rfl (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT') _ _ HEq.rfl)
    ht

/-- 13.2: a filling of the base paired with a term lying over the reindexed
telescope, as a filling of the extension. -/
def pair {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y) (t : Tm.obj (Opposite.op X))
    (ht : Ob.Term.tele t = Ty.map σ.op a) : X ⟶ extend Y a :=
  Quotient.hrecOn₂ (φ := fun (t : Tm.obj (Opposite.op X)) (σ : X ⟶ Y) =>
      Ob.Term.tele t = Ty.map σ.op a → (X ⟶ extend Y a))
    t σ (fun t σ ht => pairTele X t Y a σ ht)
    (by
      intro t σ t' σ' htt hσσ
      apply Function.hfunext (congrArg₂ (fun (t : Tm.obj (Opposite.op X)) (σ : X ⟶ Y) =>
        Ob.Term.tele t = Ty.map σ.op a) (Quotient.sound htt) (Quotient.sound hσσ))
      intro ht ht' _
      apply heq_of_eq
      obtain ⟨Γ⟩ := Y
      obtain ⟨Θ⟩ := a
      exact Quotient.sound (Ob.Pair.subst_congr _ _ ⟨htt, hσσ⟩))
    ht

theorem pair_mk {X : Ob} (Γ : Ctx) (Θ : Ob.Tele Γ.toOb) (σ : Ob.Subst X Γ.toOb)
    (t : Ob.Term X)
    (ht : Ob.Term.tele (Quotient.mk (Ob.Term.setoid X) t)
      = Ty.map (Quiver.Hom.op (Quotient.mk (Ob.Subst.setoid X Γ.toOb) σ : X ⟶ Γ.toOb))
          (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ)) :
    pair (Quotient.mk (Ob.Subst.setoid X Γ.toOb) σ) (Quotient.mk (Ob.Term.setoid X) t) ht
      = homEquiv X Γ Θ ⟨(Quotient.mk (Ob.Term.setoid X) t,
          Quotient.mk (Ob.Subst.setoid X Γ.toOb) σ), ht⟩ := rfl

/-! ## Laws of pairing -/

/-- 13.1 is natural: the telescope of a reindexed term is the reindexed telescope. -/
theorem Term.tele_map {X Y : Ob} (σ : X ⟶ Y) (t : Tm.obj (Opposite.op Y)) :
    Ob.Term.tele (Tm.map σ.op t) = Ty.map σ.op (Ob.Term.tele t) :=
  ConcreteCategory.congr_hom (q.naturality σ.op) t

theorem generic_tele (X : Ob) (a : Ty.obj (Opposite.op X)) :
    Ob.Term.tele (generic X a) = Ty.map (projection X a).op a := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Θ⟩ := a
  exact Ctx.generic_tele Γ Θ

/-- 13.2: a pair projects to its filling of the base. -/
theorem pair_projection {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Ob.Term.tele t = Ty.map σ.op a) :
    pair σ t ht ≫ projection Y a = σ := by
  obtain ⟨Γ⟩ := Y
  obtain ⟨Θ⟩ := a
  obtain ⟨σ⟩ := σ
  obtain ⟨t⟩ := t
  exact homEquiv_projection X Γ Θ ⟨(_, _), ht⟩

/-- 13.2: the generic term reindexed along a pair is its term. -/
theorem pair_generic {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Ob.Term.tele t = Ty.map σ.op a) :
    Tm.map (pair σ t ht).op (generic Y a) = t := by
  obtain ⟨Γ⟩ := Y
  obtain ⟨Θ⟩ := a
  obtain ⟨σ⟩ := σ
  obtain ⟨t⟩ := t
  exact homEquiv_generic X Γ Θ ⟨(_, _), ht⟩

/-- 13.2: the projection paired with the generic term is the identity. -/
theorem pair_eta (X : Ob) (a : Ty.obj (Opposite.op X)) :
    pair (projection X a) (generic X a) (generic_tele X a) = 𝟙 (extend X a) := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Θ⟩ := a
  have h : (homEquiv (Ctx.extend Γ Θ) Γ Θ).symm (𝟙 (Ctx.extend Γ Θ))
      = ⟨(Quotient.mk (Ob.Term.setoid (Ctx.extend Γ Θ)) (Ctx.generic Γ Θ),
          Ctx.projection Γ Θ), Ctx.generic_tele Γ Θ⟩ := by
    apply Subtype.ext
    rw [homEquiv_symm_apply, op_id, Functor.map_id_apply, Category.id_comp]
  have h' := congrArg (homEquiv (Ctx.extend Γ Θ) Γ Θ) h
  rw [Equiv.apply_symm_apply] at h'
  exact h'.symm

/-- 10.4 on classes: a filling extended past a telescope, as the pair of the
composite with the projection and the generic term. -/
def lift {X Y : Ob} (a : Ty.obj (Opposite.op Y)) (σ : X ⟶ Y) :
    extend X (Ty.map σ.op a) ⟶ extend Y a :=
  pair (projection X (Ty.map σ.op a) ≫ σ) (generic X (Ty.map σ.op a))
    (by rw [generic_tele, op_comp, Functor.map_comp_apply])

theorem lift_mk {Ξ Γ : Ctx} (σ : Ob.Subst Ξ.toOb Γ.toOb) (Θ : Ob.Tele Γ.toOb) :
    lift (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ)
        (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)
      = Ctx.lift σ Θ := by
  refine congrArg (Quotient.mk (Ob.Subst.setoid
    (Ctx.extend Ξ (Ob.Tele.subst σ Θ)) (Ctx.extend Γ Θ))) (Subtype.ext ?_)
  funext Λ x
  rcases C.cover Γ.arity Θ.arity x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · refine Eq.trans (Subst.copair_inl _ _ y) ?_
    exact (act_ofRenaming (Renaming.inl Ξ.arity Θ.arity) (σ.1 y)).trans
      (Subst.lift_inl σ.1 y).symm
  · refine Eq.trans (Subst.copair_inr _ _ z) ?_
    exact (Subst.lift_inr σ.1 z).symm

end Ob

end Ctx
