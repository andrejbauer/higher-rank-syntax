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

namespace Ob

/-! ## Classes over equal objects -/

/-- Classes of fillings between equal objects with heterogeneously equal
underlying substitutions are heterogeneously equal. -/
theorem Subst.heq_mk
    {X X' Y Y' : Ob} (eX : X = X') (eY : Y = Y')
    (σ : Subst X Y) (σ' : Subst X' Y') (hσ : HEq σ.1 σ'.1) :
  HEq (Quotient.mk (Subst.setoid X Y) σ) (Quotient.mk (Subst.setoid X' Y') σ')
  := by
  subst eX eY
  rw [Subtype.ext (eq_of_heq hσ)]

/-- Classes of telescopes with a filling over equal objects are heterogeneously
equal when, along every identification of the arities of the objects, the
telescopes are equal and the fillings agree. -/
theorem Term.heq_mk_of_rel
    {X X' : Ob} (e : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {T' : dTel X'.arity Λ}
    {τ : _root_.Subst Λ X.arity} {τ' : _root_.Subst Λ X'.arity}
    (wT : Tele.Wf X T) (wT' : Tele.Wf X' T')
    (wτ : Fill.Wf X T τ) (wτ' : Fill.Wf X' T' τ')
    (h : ∀ e' : X.arity = X'.arity,
      Tele.Eq X' (e' ▸ T) T' ∧ Fill.Eq X' (e' ▸ T) (e' ▸ τ) τ') :
  HEq (Quotient.mk (Term.setoid X) ⟨⟨Λ, T, wT⟩, τ, wτ⟩)
    (Quotient.mk (Term.setoid X') ⟨⟨Λ, T', wT'⟩, τ', wτ'⟩)
  := by
  subst e
  apply heq_of_eq
  apply Quotient.sound
  exact ⟨rfl, h rfl⟩

/-- Heterogeneously equal classes of telescopes with a filling over equal
objects have, along every identification of the arities of the objects, equal
telescopes and agreeing fillings. -/
theorem Term.eq_of_heq_mk
    {X X' : Ob} (h : X = X') {Λ : C.Arity}
    {T : dTel X.arity Λ} {wT : Tele.Wf X T} {σ : _root_.Subst Λ X.arity}
    {wσ : Fill.Wf X T σ} {T' : dTel X'.arity Λ} {wT' : Tele.Wf X' T'}
    {σ' : _root_.Subst Λ X'.arity} {wσ' : Fill.Wf X' T' σ'}
    (hh : HEq (Quotient.mk (Term.setoid X) ⟨⟨Λ, T, wT⟩, σ, wσ⟩)
      (Quotient.mk (Term.setoid X') ⟨⟨Λ, T', wT'⟩, σ', wσ'⟩)) :
  ∀ e : X.arity = X'.arity,
    Tele.Eq X' (e ▸ T) T' ∧ Fill.Eq X' (e ▸ T) (e ▸ σ) σ'
  := by
  subst h
  intro _
  exact (Quotient.exact (eq_of_heq hh)).2

/-! ## Extension -/

/-- The extension of a context class by a telescope, given with its
well-formedness. -/
def extendRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → Tele.Wf X Θ.2 → Ob :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → Tele.Wf X Θ.2 → Ob)
    X (fun Γ Θ h => Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩)
    (by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h _ _
      apply heq_of_eq (Ctx.extend_congr hAA (Wf_t.refl h)))

/-- The extension of a context class by a telescope class. -/
def extend (X : Ob) (a : Ty.obj (Opposite.op X)) : Ob :=
  Quotient.liftOn a (fun Θ => extendRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (by
      obtain ⟨Γ⟩ := X
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, _, hTT'⟩
      apply Ctx.extend_congr (Wf_t.refl Γ.wf) hTT')

/-! ## Projection -/

/-- The projection off the extension of a context class by a telescope, given
with its well-formedness. -/
def projectionRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Tele.Wf X Θ.2) →
      (extendRaw X Θ h ⟶ X) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Tele.Wf X Θ.2) →
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
      apply Subst.heq_mk (Ctx.extend_congr hAA (Wf_t.refl h)) eY
      rfl)

/-- The projection off the extension of a context class by a telescope class. -/
def projection (X : Ob) (a : Ty.obj (Opposite.op X)) : extend X a ⟶ X :=
  Quotient.hrecOn (motive := fun a => extend X a ⟶ X) a
    (fun Θ => projectionRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (by
      obtain ⟨Γ⟩ := X
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨rfl, _, hTT'⟩
      apply Subst.heq_mk (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT') rfl
      rfl)

/-! ## The generic term -/

/-- The generic term over the extension of a context class by a telescope, given
with its well-formedness. -/
def genericRaw (X : Ob) :
    (Θ : Σ Ω : C.Arity, dTel X.arity Ω) → (h : Tele.Wf X Θ.2) →
      Tm.obj (Opposite.op (extendRaw X Θ h)) :=
  Quotient.hrecOn (motive := fun X =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity X) Ω) → (h : Tele.Wf X Θ.2) →
        Tm.obj (Opposite.op (extendRaw X Θ h)))
    X (fun Γ Θ h => Quotient.mk (Term.setoid (Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩))
      (Ctx.generic Γ ⟨Θ.1, Θ.2, h⟩))
    (by
      rintro ⟨_, _, _⟩ ⟨_, A', hA'⟩ ⟨rfl, hAA⟩
      apply Function.hfunext rfl
      rintro Θ _ ⟨⟩
      apply Function.hfunext (propext ⟨Wf_t.ofEq hAA, Wf_t.ofEq (Eq_t.symm Wf_t.nil hAA)⟩)
      intro h h' _
      apply Term.heq_mk_of_rel (Ctx.extend_congr hAA (Wf_t.refl h))
      intro _
      obtain ⟨hΘ, hτ⟩ := generic_wf ⟨_, A', hA'⟩ ⟨_, _, h'⟩
      exact ⟨⟨hΘ, Wf_t.refl hΘ⟩, hΘ, hτ, Eq_s.refl hτ⟩)

/-- The generic term over the extension of a context class by a telescope
class. -/
def generic (X : Ob) (a : Ty.obj (Opposite.op X)) : Tm.obj (Opposite.op (extend X a)) :=
  Quotient.hrecOn (motive := fun a => Tm.obj (Opposite.op (extend X a))) a
    (fun Θ => genericRaw X ⟨Θ.arity, Θ.telescope⟩ Θ.wf)
    (by
      obtain ⟨Γ⟩ := X
      rintro ⟨Λ, T, hT⟩ ⟨_, T', _⟩ ⟨rfl, _, hTT'⟩
      have hcat := Eq_t.concatenate (Wf_t.refl Γ.wf) hTT'
      obtain ⟨hΘ, hτ⟩ := generic_wf Γ ⟨Λ, T, hT⟩
      have hwf := Wf_t.ofEq hcat hΘ
      have hfill := Wf_s.ofEq hcat hτ (Wf_t.refl hΘ)
      apply Term.heq_mk_of_rel (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT')
      intro _
      constructor
      · exact ⟨hwf, Eq_t.weaken (Ambient.Renaming.weaken Γ.ambient T') hTT'⟩
      · exact ⟨hwf, hfill, Eq_s.refl hfill⟩)

/-! ## Pairing -/

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope, as a substitution into the extension of `Y` by the telescope; the
term is a representative, and the telescope and the substitution are given with
their well-formedness. -/
def pairRaw (X : Ob) (t : Term X) (Y : Ob) :
    (Θ : Σ Ω : C.Arity, dTel Y.arity Ω) → (h : Tele.Wf Y Θ.2) →
      (σ : _root_.Subst Y.arity X.arity) → (hσ : Subst.Wf X Y σ) →
      Tele.Rel t.1 (Tele.subst ⟨σ, hσ⟩ ⟨Θ.1, Θ.2, h⟩) →
      (X ⟶ extendRaw Y Θ h) :=
  Quotient.hrecOn (motive := fun Y =>
      (Θ : Σ Ω : C.Arity, dTel (Ob.arity Y) Ω) → (h : Tele.Wf Y Θ.2) →
      (σ : _root_.Subst (Ob.arity Y) X.arity) → (hσ : Subst.Wf X Y σ) →
      Tele.Rel t.1 (Tele.subst ⟨σ, hσ⟩ ⟨Θ.1, Θ.2, h⟩) →
      (X ⟶ extendRaw Y Θ h))
    Y (fun Γ Θ h σ hσ rel =>
      Quotient.mk (Subst.setoid X (Ctx.extend Γ ⟨Θ.1, Θ.2, h⟩))
        (Pair.subst (Γ := Γ) (Θ := ⟨Θ.1, Θ.2, h⟩) ⟨(t, ⟨σ, hσ⟩), rel⟩))
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
      apply Subst.heq_mk rfl (Ctx.extend_congr hAA (Wf_t.refl h))
      rfl)

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope class, as a substitution into the extension of `Y` by the telescope
class; the substitution and the term are representatives. -/
def pairTele (X : Ob) (t : Term X) (Y : Ob) (a : Ty.obj (Opposite.op Y))
    (σ : Subst X Y)
    (ht : Term.tele (Quotient.mk (Term.setoid X) t)
      = Ty.map (Quiver.Hom.op (Quotient.mk (Subst.setoid X Y) σ : X ⟶ Y)) a) :
    X ⟶ extend Y a :=
  Quotient.hrecOn (motive := fun a =>
      Term.tele (Quotient.mk (Term.setoid X) t)
        = Ty.map (Quiver.Hom.op (Quotient.mk (Subst.setoid X Y) σ : X ⟶ Y)) a →
      (X ⟶ extend Y a))
    a (fun Θ ht => pairRaw X t Y ⟨Θ.arity, Θ.telescope⟩ Θ.wf σ.1 σ.2 (Quotient.exact ht))
    (by
      obtain ⟨Γ⟩ := Y
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
      apply Function.hfunext (by rw [Quotient.sound h])
      intro _ _ _
      obtain ⟨rfl, _, hTT'⟩ := h
      apply Subst.heq_mk rfl (Ctx.extend_congr (Wf_t.refl Γ.wf) hTT')
      rfl)
    ht

/-- A substitution into `Y` paired with a term lying over the reindexed
telescope class, as a substitution into the extension of `Y` by the telescope
class. -/
def pair {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y) (t : Tm.obj (Opposite.op X))
    (ht : Term.tele t = Ty.map σ.op a) : X ⟶ extend Y a :=
  Quotient.hrecOn₂ (φ := fun (t : Tm.obj (Opposite.op X)) (σ : X ⟶ Y) =>
      Term.tele t = Ty.map σ.op a → (X ⟶ extend Y a))
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
  Term.tele (Tm.map σ.op t) = Ty.map σ.op (Term.tele t)
  := ConcreteCategory.congr_hom (q.naturality σ.op) t

/-- The generic term lies over the telescope class reindexed along the
projection. -/
theorem generic_tele (X : Ob) (a : Ty.obj (Opposite.op X)) :
  Term.tele (generic X a) = Ty.map (projection X a).op a
  := by
  obtain ⟨Γ⟩ := X
  obtain ⟨Θ⟩ := a
  apply Ctx.generic_tele

/-- `pair σ t ht` followed by the projection is `σ`. -/
theorem pair_projection
    {X Y : Ob} {a : Ty.obj (Opposite.op Y)} (σ : X ⟶ Y)
    (t : Tm.obj (Opposite.op X)) (ht : Term.tele t = Ty.map σ.op a) :
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
    (t : Tm.obj (Opposite.op X)) (ht : Term.tele t = Ty.map σ.op a) :
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
    (t : Tm.obj (Opposite.op X)) (ht : Term.tele t = Ty.map σ.op a) (θ : Z ⟶ X)
    (ht' : Term.tele (Tm.map θ.op t) = Ty.map (θ ≫ σ).op a) :
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
theorem lift_mk {Ξ Γ : Ctx} (σ : Subst Ξ.toOb Γ.toOb) (Θ : Tele Γ.toOb) :
  lift (Quotient.mk (Tele.setoid Γ.toOb) Θ) (Quotient.mk (Subst.setoid Ξ.toOb Γ.toOb) σ)
    = Ctx.lift σ Θ
  := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  funext Λ x
  rcases C.cover Γ.arity Θ.arity x with ⟨y, rfl⟩ | ⟨z, rfl⟩
  · apply Eq.trans (Subst.copair_inl _ _ y)
    apply Eq.trans (act_ofRenaming _ _)
    symm
    apply Subst.lift_inl
  · apply Eq.trans (Subst.copair_inr _ _ z)
    symm
    apply Subst.lift_inr

end Ob

end Ctx
