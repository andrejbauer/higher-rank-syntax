import HigherRankSyntax.Ctx.NaturalModel

/-!
# Extension on context classes

The extension of a context class by a telescope class, the projection off it,
its generic term, pairing a substitution with a term lying over the reindexed
telescope class, the laws of pairing, and the lift of a substitution past a
telescope class.  On the class of a context `Γ` and the class of a telescope `Θ`
over it, the extension, projection and generic term are `Ctx.extend Γ Θ`,
`Ctx.projection Γ Θ` and the class of `Ctx.generic Γ Θ`, and the lift of the
class of a filling `σ` is `Ctx.lift σ Θ`.
-/

open CategoryTheory

namespace Ctx

/-! ## Classes over equal objects -/

/-- Classes of fillings between equal objects with heterogeneously equal
underlying substitutions are heterogeneously equal. -/
theorem Ob.Subst.heq_mk
    {X X' Y Y' : Ob} (eX : X = X') (eY : Y = Y')
    (σ : Ob.Subst X Y) (σ' : Ob.Subst X' Y') (hσ : HEq σ.1 σ'.1) :
  HEq (Quotient.mk (Ob.Subst.setoid X Y) σ) (Quotient.mk (Ob.Subst.setoid X' Y') σ')
  := by
  subst eX eY
  rw [Subtype.ext (eq_of_heq hσ)]

/-- Classes of telescopes with a filling over equal objects, with heterogeneously
equal telescopes and heterogeneously equal fillings, are heterogeneously
equal. -/
theorem Ob.Term.heq_mk
    {X X' : Ob} (e : X = X') {Λ : C.Arity}
    {Θ : dTel X.arity Λ} {Θ' : dTel X'.arity Λ} (hΘ : HEq Θ Θ')
    {τ : _root_.Subst Λ X.arity} {τ' : _root_.Subst Λ X'.arity} (hτ : HEq τ τ')
    (wΘ : Ob.Tele.Wf X Θ) (wΘ' : Ob.Tele.Wf X' Θ')
    (wτ : Ob.Fill.Wf X Θ τ) (wτ' : Ob.Fill.Wf X' Θ' τ') :
  HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, Θ, wΘ⟩, τ, wτ⟩)
    (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, Θ', wΘ'⟩, τ', wτ'⟩)
  := by
  subst e
  cases hΘ
  cases hτ
  rfl

/-- Classes of telescopes with a filling over equal objects are heterogeneously
equal when, along every identification of the arities of the objects, the
telescopes are equal and the fillings agree. -/
theorem Ob.Term.heq_mk_of_rel
    {X X' : Ob} (e : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {T' : dTel X'.arity Λ}
    {τ : _root_.Subst Λ X.arity} {τ' : _root_.Subst Λ X'.arity}
    (wT : Ob.Tele.Wf X T) (wT' : Ob.Tele.Wf X' T')
    (wτ : Ob.Fill.Wf X T τ) (wτ' : Ob.Fill.Wf X' T' τ')
    (h : ∀ e' : X.arity = X'.arity,
      Ob.Tele.Eq X' (e' ▸ T) T' ∧ Ob.Fill.Eq X' (e' ▸ T) (e' ▸ τ) τ') :
  HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, T, wT⟩, τ, wτ⟩)
    (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, T', wT'⟩, τ', wτ'⟩)
  := by
  subst e
  apply heq_of_eq
  apply Quotient.sound
  exact ⟨rfl, h rfl⟩

/-- Heterogeneously equal classes of telescopes with a filling over equal
objects have, along every identification of the arities of the objects, equal
telescopes and agreeing fillings. -/
theorem Ob.Term.eq_of_heq_mk
    {X X' : Ob} (h : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {wT : Ob.Tele.Wf X T} {σ : _root_.Subst Λ X.arity}
    {wσ : Ob.Fill.Wf X T σ} {T' : dTel X'.arity Λ} {wT' : Ob.Tele.Wf X' T'}
    {σ' : _root_.Subst Λ X'.arity} {wσ' : Ob.Fill.Wf X' T' σ'}
    (hh : HEq (Quotient.mk (Ob.Term.setoid X) ⟨⟨Λ, T, wT⟩, σ, wσ⟩)
      (Quotient.mk (Ob.Term.setoid X') ⟨⟨Λ, T', wT'⟩, σ', wσ'⟩)) :
  ∀ e : X.arity = X'.arity,
    Ob.Tele.Eq X' (e ▸ T) T' ∧ Ob.Fill.Eq X' (e ▸ T) (e ▸ σ) σ'
  := by
  subst h
  intro _
  obtain ⟨_, hrel⟩ := Quotient.exact (eq_of_heq hh)
  exact hrel

/-! ## Extension -/

namespace Ob

/-- The extension of a context class by a telescope, given with its
well-formedness. -/
def extendRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → Ob.Tele.Wf X Θ.2 → Ob :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → Ob.Tele.Wf X Θ.2 → Ob)
    X (fun Γ Θ h => Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩)
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h _ _
      apply heq_of_eq (Ctx.extend_congr hAA (Wf_t.refl h)))

/-- Extension respects equality of telescopes. -/
theorem extend_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
  extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf
    = extendRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  apply Ctx.extend_congr (Wf_t.refl Γ.wf) hTT'

/-- The extension of a context class by a telescope class. -/
def extend (X : Ob) (a : Ty.obj (Opposite.op X)) : Ob :=
  Quotient.liftOn a (fun Θ => extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (extend_congr X)

/-! ## Projection -/

/-- The projection off the extension of a context class by a telescope, given
with its well-formedness. -/
def projectionRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Ob.Tele.Wf X Θ.2) →
      (extendRaw X Θ h ⟶ X) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Ob.Tele.Wf X Θ.2) →
        (extendRaw X Θ h ⟶ X))
    X (fun Γ Θ h => Ctx.projection Γ ⟨Θ.1, Θ.2, h⟩)
    (by
      rintro ⟨Ω, A, hA⟩ ⟨_, A', hA'⟩ ⟨rfl, hAA⟩
      have eY : Ctx.toOb ⟨Ω, A, hA⟩ = Ctx.toOb ⟨Ω, A', hA'⟩ :=
        Quotient.sound ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h _ _
      apply Ob.Subst.heq_mk (Ctx.extend_congr hAA (Wf_t.refl h)) eY
      rfl)

/-- The projection respects equality of telescopes. -/
theorem projection_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
  HEq (projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (projectionRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf)
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨_, _, _⟩ := Θ
  obtain ⟨_, _, _⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  apply Ob.Subst.heq_mk (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT') rfl
  rfl

/-- The projection off the extension of a context class by a telescope class. -/
def projection (X : Ob) (a : Ty.obj (Opposite.op X)) : extend X a ⟶ X :=
  Quotient.hrecOn (motive := fun a => extend X a ⟶ X) a
    (fun Θ => projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf) (projection_congr X)

/-! ## The generic term -/

/-- The generic term over the extension of a context class by a telescope, given
with its well-formedness. -/
def genericRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Ob.Tele.Wf X Θ.2) →
      Tm.obj (Opposite.op (extendRaw X Θ h)) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Ob.Tele.Wf X Θ.2) →
        Tm.obj (Opposite.op (extendRaw X Θ h)))
    X (fun Γ Θ h => Quotient.mk (Ob.Term.setoid (Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩))
      (Ctx.generic Γ ⟨Θ.1, Θ.2, h⟩))
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h _ _
      apply Term.heq_mk (Ctx.extend_congr hAA (Wf_t.refl h)) HEq.rfl HEq.rfl)

/-- The generic term respects equality of telescopes. -/
theorem generic_congr (X : Ob) (Θ Θ' : Ob.Tele X) (h : Ob.Tele.Rel Θ Θ') :
  HEq (genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (genericRaw X ⟨Θ'.arity, Θ'.telescope⟩ Θ'.wf)
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Λ, T, hT⟩ := Θ
  obtain ⟨_, T', _⟩ := Θ'
  obtain ⟨rfl, _, hTT'⟩ := h
  have hcat := Eq_t.concatenate (Wf_t.refl Γ.wf) hTT'
  obtain ⟨hΘ, hτ⟩ := generic_wf Γ ⟨Λ, T, hT⟩
  have hwf := Wf_t.ofEq hcat hΘ
  have hfill := Wf_s.ofEq hcat hτ (Wf_t.refl hΘ)
  apply Term.heq_mk_of_rel (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT')
  intro _
  constructor
  · exact ⟨hwf, Eq_t.weaken (Ambient.Renaming.weaken Γ.ambient T') hTT'⟩
  · exact ⟨hwf, hfill, Eq_s.refl hfill⟩

/-- The generic term over the extension of a context class by a telescope
class. -/
def generic (X : Ob) (a : Ty.obj (Opposite.op X)) : Tm.obj (Opposite.op (extend X a)) :=
  Quotient.hrecOn (motive := fun a => Tm.obj (Opposite.op (extend X a))) a
    (fun Θ => genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf) (generic_congr X)

/-! ## Pairing -/

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope, as a substitution into the extension of `Y` by the telescope; the
term is a representative, and the telescope and the substitution are given with
their well-formedness. -/
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
      obtain ⟨Ξ⟩ := X
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h _ _
      apply Function.hfunext rfl
      rintro σ _ ⟨⟩
      apply Function.hfunext (propext (wf_hom_iff (Wf_t.refl Ξ.wf) hAA σ))
      intro _ _ _
      apply Function.hfunext rfl
      intro _ _ _
      apply Ob.Subst.heq_mk rfl (Ctx.extend_congr hAA (Wf_t.refl h))
      rfl)

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope class, as a substitution into the extension of `Y` by the telescope
class; the substitution and the term are representatives. -/
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
      apply Function.hfunext (by rw [Quotient.sound h])
      intro _ _ _
      obtain ⟨Γ⟩ := Y
      obtain ⟨_, _, _⟩ := Θ
      obtain ⟨_, _, _⟩ := Θ'
      obtain ⟨rfl, _, hTT'⟩ := h
      apply Ob.Subst.heq_mk rfl (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT')
      rfl)
    ht

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope class, as a substitution into the extension of `Y` by the telescope
class. -/
def pair {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y) (t : Tm.obj (Opposite.op X))
    (ht : Ob.Term.tele t = Ty.map σ.op a) : X ⟶ extend Y a :=
  Quotient.hrecOn₂ (φ := fun (t : Tm.obj (Opposite.op X)) (σ : X ⟶ Y) =>
      Ob.Term.tele t = Ty.map σ.op a → (X ⟶ extend Y a))
    t σ (fun t σ ht => pairTele X t Y a σ ht)
    (by
      intro t σ t' σ' htt hσσ
      apply Function.hfunext (by rw [Quotient.sound htt, Quotient.sound hσσ])
      intro _ _ _
      apply heq_of_eq
      obtain ⟨Γ⟩ := Y
      obtain ⟨Θ⟩ := a
      apply Quotient.sound
      apply Pair.subst_congr
      exact ⟨htt, hσσ⟩)
    ht

/-! ## Laws of pairing -/

/-- The telescope of a reindexed term is the reindexed telescope. -/
theorem Term.tele_map {X Y : Ob} (σ : X ⟶ Y) (t : Tm.obj (Opposite.op Y)) :
  Ob.Term.tele (Tm.map σ.op t) = Ty.map σ.op (Ob.Term.tele t)
  := ConcreteCategory.congr_hom (q.naturality σ.op) t

/-- The generic term lies over the telescope class reindexed along the
projection. -/
theorem generic_tele (X : Ob) (a : Ty.obj (Opposite.op X)) :
  Ob.Term.tele (generic X a) = Ty.map (projection X a).op a
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Θ⟩ := a
  apply Ctx.generic_tele

/-- `pair σ t ht` followed by the projection is `σ`. -/
theorem pair_projection
    {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Ob.Term.tele t = Ty.map σ.op a) :
  pair σ t ht ≫ projection Y a = σ
  := by
  obtain ⟨Γ⟩ := Y
  obtain ⟨Θ⟩ := a
  obtain ⟨σ⟩ := σ
  obtain ⟨t⟩ := t
  apply homEquiv_projection X Γ Θ ⟨(_, _), ht⟩

/-- The generic term reindexed along `pair σ t ht` is `t`. -/
theorem pair_generic
    {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Ob.Term.tele t = Ty.map σ.op a) :
  Tm.map (pair σ t ht).op (generic Y a) = t
  := by
  obtain ⟨Γ⟩ := Y
  obtain ⟨Θ⟩ := a
  obtain ⟨σ⟩ := σ
  obtain ⟨t⟩ := t
  apply homEquiv_generic X Γ Θ ⟨(_, _), ht⟩

/-- The projection paired with the generic term is the identity. -/
theorem pair_eta (X : Ob) (a : Ty.obj (Opposite.op X)) :
  pair (projection X a) (generic X a) (generic_tele X a) = 𝟙 (extend X a)
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Θ⟩ := a
  have h : (homEquiv _ Γ Θ).symm (𝟙 _)
      = ⟨(⟦Ctx.generic Γ Θ⟧, Ctx.projection Γ Θ), Ctx.generic_tele Γ Θ⟩ := by
    apply Subtype.ext
    rw [homEquiv_symm_apply, op_id, Functor.map_id_apply, Category.id_comp]
  rw [Equiv.symm_apply_eq] at h
  symm
  exact h

/-- `pair σ t` after `θ` is `θ ≫ σ` paired with `t` reindexed along `θ`. -/
theorem pair_comp
    {X Y Z : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Ob.Term.tele t = Ty.map σ.op a) (θ : Z ⟶ X)
    (ht' : Ob.Term.tele (Tm.map θ.op t) = Ty.map (θ ≫ σ).op a) :
  θ ≫ pair σ t ht = pair (θ ≫ σ) (Tm.map θ.op t) ht'
  := by
  obtain ⟨Γ⟩ := Y
  obtain ⟨Θ⟩ := a
  obtain ⟨σ⟩ := σ
  obtain ⟨t⟩ := t
  obtain ⟨θ⟩ := θ
  symm
  exact homEquiv_naturality Γ Θ _ _ _ ht ht'

/-- The lift of `σ` past the telescope class `a`: the pair of the projection
followed by `σ` with the generic term. -/
def lift {X Y : Ob} (a : Ty.obj (Opposite.op Y)) (σ : X ⟶ Y) :
    extend X (Ty.map σ.op a) ⟶ extend Y a :=
  pair (projection X (Ty.map σ.op a) ≫ σ) (generic X (Ty.map σ.op a))
    (by rw [generic_tele, op_comp, Functor.map_comp_apply])

/-- On the classes of a substitution and a telescope, `lift` is `Ctx.lift`. -/
theorem lift_mk {Ξ Γ : Ctx} (σ : Ob.Subst Ξ.toOb Γ.toOb) (Θ : Ob.Tele Γ.toOb) :
  lift (Quotient.mk (Ob.Tele.setoid Γ.toOb) Θ) (Quotient.mk (Ob.Subst.setoid Ξ.toOb Γ.toOb) σ)
    = Ctx.lift σ Θ
  := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  funext Λ x
  rcases C.cover Γ.arity Θ.arity x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · apply Eq.trans (Subst.copair_inl _ _ y)
    apply Eq.trans (act_ofRenaming (Renaming.inl Ξ.arity Θ.arity) (σ.1 y))
    symm
    apply Subst.lift_inl
  · apply Eq.trans (Subst.copair_inr _ _ z)
    symm
    apply Subst.lift_inr

end Ob

end Ctx
