import HigherRankSyntax.Equations.DecorationQuotient

/-!
# Quotient decorated telescopes as an internal monoid

Quotient syntax admits coherent extension by a raw suffix.  A quotient
substitution is lifted by weakening the images of its old slots into the
extended context and mapping every new suffix slot to the quotient unit.  This
gives the context-extension tensor on arity-shaped modules over the quotient
relative monad.

The module of quotient decorated telescopes remembers the same literal raw
shape as before quotienting.  Empty decoration and dependent concatenation
respect pointwise classifier equality, so they descend to the quotient and
form the unit and multiplication of an internal monoid.  Equations identify
classifier annotations; they do not assert that a classifier is well formed or
that a slot inhabits it.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A} {S : C.Arity}

namespace Equations

namespace QExpr

variable {E : EquationPresentation C S}

theorem act_unit {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ) :
    act E σ (E.quotientMonad.η Γ Λ τ x) = σ Λ τ x := by
  have h := E.quotientMonad.unit_left σ
  exact congrArg (fun f => f Λ τ x) h.symm

theorem act_identity {Γ Φ : C.Arity} {τ : C.Ty}
    (e : QExpr E Γ Φ τ) :
    act E (E.quotientMonad.η Γ) e = e := by
  have h := E.quotientMonad.unit_right Γ
  exact congrArg (fun f => f Φ τ e) h

theorem act_composition {Γ Δ Ξ Φ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (θ : RelativeMonad.Kleisli.of E.quotientMonad Δ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Ξ)
    {τ : C.Ty} (e : QExpr E Γ Φ τ) :
    act E (σ ≫ θ) e = act E θ (act E σ e) := by
  have h := E.quotientMonad.comp_lift σ θ
  exact congrArg (fun f => f Φ τ e) h

/-- Reassociate a fixed local suffix into the local index of quotient syntax. -/
def reassociate {Γ Φ Ψ : C.Arity} {τ : C.Ty} :
    QExpr E (Γ ⋈ Φ) Ψ τ → QExpr E Γ (Φ ⋈ Ψ) τ :=
  fun e => e

theorem reassociate_injective {Γ Φ Ψ : C.Arity} {τ : C.Ty} :
    Function.Injective
      (reassociate (E := E) (Γ := Γ) (Φ := Φ) (Ψ := Ψ) (τ := τ)) :=
  fun _ _ h => h

/-- The eta-expansion of a slot in a context extended by a local suffix. -/
noncomputable def depthEta {Γ Φ Λ : C.Arity} {τ : C.Ty}
    (x : Γ ⋈ Φ ∋[τ] Λ) :
    QExpr E Γ (Φ ⋈ Λ) τ :=
  reassociate (E.quotientMonad.η (Γ ⋈ Φ) Λ τ x)

/-- Reassociate two consecutive suffixes into the local index. -/
def reassociateTwice {Γ Φ Ψ Λ : C.Arity} {τ : C.Ty} :
    QExpr E ((Γ ⋈ Φ) ⋈ Ψ) Λ τ →
      QExpr E Γ (Φ ⋈ (Ψ ⋈ Λ)) τ :=
  fun e => e

theorem reassociateTwice_injective {Γ Φ Ψ Λ : C.Arity} {τ : C.Ty} :
    Function.Injective
      (reassociateTwice (E := E) (Γ := Γ) (Φ := Φ) (Ψ := Ψ)
        (Λ := Λ) (τ := τ)) :=
  fun _ _ h => h

theorem depthEta_assoc {Γ Φ Ψ Λ : C.Arity} {τ : C.Ty}
    (x : Γ ⋈ (Φ ⋈ Ψ) ∋[τ] Λ) :
    reassociate (E := E) (Γ := Γ) (Φ := Φ) (Ψ := Ψ ⋈ Λ)
        (depthEta (E := E) (Γ := Γ ⋈ Φ) (Φ := Ψ) x) =
      depthEta (E := E) (Γ := Γ) (Φ := Φ ⋈ Ψ) x := rfl

end QExpr

namespace QuotientSubstitution

variable {E : EquationPresentation C S}

noncomputable section

/-- Extend a quotient substitution by lifting selected raw representatives and
then taking their equation classes. -/
def lift (E : EquationPresentation C S) {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (Φ : C.Arity) :
    RelativeMonad.Kleisli.of E.quotientMonad (Γ ⋈ Φ) ⟶
      RelativeMonad.Kleisli.of E.quotientMonad (Δ ⋈ Φ) :=
  fun _ _ x => QExpr.mk E
    (Subst.liftPrefixed (QExpr.representatives E σ) Φ x)

/-- Acting by a lifted quotient substitution is action below its fixed
suffix. -/
theorem action_lift {Γ Δ Φ Ψ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    {τ : C.Ty} (e : QExpr E (Γ ⋈ Φ) Ψ τ) :
    QExpr.reassociate (QExpr.act E (lift E σ Φ) e) =
      QExpr.act E σ (QExpr.reassociate e) := by
  induction e using Quotient.inductionOn with
  | _ e =>
      apply QExpr.sound
      have hFill : ∀ {Λ : C.Arity} {υ : C.Ty}
          (x : Γ ⋈ Φ ∋[υ] Λ),
          DerivEq E (QExpr.representatives E (lift E σ Φ) x)
            (Subst.liftPrefixed (QExpr.representatives E σ) Φ x) := by
        intro Λ υ x
        apply QExpr.representative_related_raw
        rfl
      have h := DerivEq.substitute_fillers E e
        (QExpr.representatives E (lift E σ Φ))
        (Subst.liftPrefixed (QExpr.representatives E σ) Φ) hFill
      have hRaw := Subst.act_liftPrefixed
        (QExpr.representatives E σ) e
      exact h.trans (hRaw ▸ DerivEq.refl _)

/-- A lifted filler is action on the eta-expansion of the extended slot. -/
theorem lift_apply {Γ Δ Φ Λ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    {τ : C.Ty} (x : Γ ⋈ Φ ∋[τ] Λ) :
    QExpr.reassociate (E := E) (lift E σ Φ Λ τ x) =
      QExpr.act E σ (QExpr.depthEta (E := E) x) := by
  calc
    QExpr.reassociate (E := E) (lift E σ Φ Λ τ x) =
        QExpr.reassociate (E := E)
          (QExpr.act E (lift E σ Φ)
            (E.quotientMonad.η (Γ ⋈ Φ) Λ τ x)) :=
      congrArg (QExpr.reassociate (E := E))
        (QExpr.act_unit (E := E) (lift E σ Φ) x).symm
    _ = QExpr.act E σ
          (QExpr.reassociate (E := E)
            (E.quotientMonad.η (Γ ⋈ Φ) Λ τ x)) :=
      action_lift (E := E) σ
        (E.quotientMonad.η (Γ ⋈ Φ) Λ τ x)
    _ = QExpr.act E σ (QExpr.depthEta (E := E) x) := rfl

theorem lift_id (E : EquationPresentation C S) (Γ Φ : C.Arity) :
    lift E (𝟙 (RelativeMonad.Kleisli.of E.quotientMonad Γ)) Φ =
      𝟙 (RelativeMonad.Kleisli.of E.quotientMonad (Γ ⋈ Φ)) := by
  funext Λ τ x
  apply QExpr.reassociate_injective (E := E)
  have hLift := lift_apply (E := E)
    (𝟙 (RelativeMonad.Kleisli.of E.quotientMonad Γ)) x
  have hIdentity := QExpr.act_identity (E := E) (Γ := Γ)
    (Φ := Φ ⋈ Λ) (τ := τ) (QExpr.depthEta (E := E) x)
  exact hLift.trans hIdentity

theorem lift_one {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ) :
    lift E σ 1 = σ := by
  funext Λ τ x
  have hLift := lift_apply (E := E) (Γ := Γ) (Δ := Δ)
    (Φ := 1) (Λ := Λ) σ x
  have hUnit := QExpr.act_unit (E := E) σ x
  exact hLift.trans hUnit

theorem lift_comp {Γ Δ Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (θ : RelativeMonad.Kleisli.of E.quotientMonad Δ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Ξ)
    (Φ : C.Arity) :
    lift E (σ ≫ θ) Φ = lift E σ Φ ≫ lift E θ Φ := by
  funext Λ τ x
  apply QExpr.reassociate_injective (E := E)
  have hComposite := lift_apply (E := E) (σ ≫ θ) x
  have hAct := QExpr.act_composition (E := E) σ θ
    (QExpr.depthEta (E := E) x)
  have hFirst := congrArg (QExpr.act E θ)
    (lift_apply (E := E) σ x).symm
  have hSecond := (action_lift (E := E) (Γ := Δ) (Δ := Ξ)
    (Φ := Φ) (Ψ := Λ) θ (lift E σ Φ Λ τ x)).symm
  exact hComposite.trans (hAct.trans (hFirst.trans hSecond))

theorem lift_assoc {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (Φ Ψ : C.Arity) :
    lift E σ (Φ ⋈ Ψ) = lift E (lift E σ Φ) Ψ := by
  funext Λ τ x
  apply QExpr.reassociateTwice_injective (E := E)
  have hLeft := lift_apply (E := E) (Γ := Γ) (Δ := Δ)
    (Φ := Φ ⋈ Ψ) (Λ := Λ) σ x
  have hNested := lift_apply (E := E) (Γ := Γ ⋈ Φ)
    (Δ := Δ ⋈ Φ) (Φ := Ψ) (Λ := Λ) (lift E σ Φ) x
  have hNested' := congrArg
    (QExpr.reassociate (E := E) (Γ := Δ) (Φ := Φ)
      (Ψ := Ψ ⋈ Λ)) hNested
  have hAction := action_lift (E := E) (Γ := Γ) (Δ := Δ)
    (Φ := Φ) (Ψ := Ψ ⋈ Λ) σ
    (QExpr.depthEta (E := E) (Γ := Γ ⋈ Φ) (Φ := Ψ) x)
  have hDepth := congrArg (QExpr.act E σ)
    (QExpr.depthEta_assoc (E := E) (Γ := Γ) (Φ := Φ)
      (Ψ := Ψ) x)
  exact hLeft.trans (hNested'.trans (hAction.trans hDepth)).symm

end

end QuotientSubstitution

/-- Quotient syntax has coherent extension by raw suffix arities. -/
noncomputable instance quotientMonadKleisliArityAction
    (E : EquationPresentation C S) :
    KleisliArityAction E.quotientMonad where
  lift := QuotientSubstitution.lift E
  lift_id := QuotientSubstitution.lift_id E
  lift_comp := QuotientSubstitution.lift_comp
  lift_one := QuotientSubstitution.lift_one
  lift_assoc := QuotientSubstitution.lift_assoc

namespace DecorationEq

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

end DecorationEq

namespace ClassifierEq

variable {E : EquationPresentation C S} {bd : C.Ty → Option C.Ty}

/-- Quotient lifting and fixed-prefix substitution give equal classifier
classes. -/
theorem substitute_lift {Γ Δ Φ Ψ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    {τ : C.Ty} (a : ClassifierAt bd (S ⋈ (Γ ⋈ Φ) ⋈ Ψ) τ) :
    ClassifierEq E bd
      (ClassifierAt.substitute (Φ := Φ ⋈ Ψ)
        (QExpr.representatives E σ) a)
      (ClassifierAt.substitute (Φ := Ψ)
        (QExpr.representatives E (QuotientSubstitution.lift E σ Φ)) a) := by
  have hFill : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ⋈ Φ ∋[υ] Λ),
      DerivEq E
        (QExpr.representatives E (QuotientSubstitution.lift E σ Φ) x)
        (Subst.liftPrefixed (QExpr.representatives E σ) Φ x) := by
    intro Λ υ x
    apply QExpr.representative_related_raw
    rfl
  have hRelated := ClassifierEq.substitute
    (QExpr.representatives E (QuotientSubstitution.lift E σ Φ))
    (Subst.liftPrefixed (QExpr.representatives E σ) Φ)
    hFill (ClassifierEq.refl a)
  have hRaw := ClassifierAt.substitute_liftPrefixed
    (QExpr.representatives E σ) a
  exact ClassifierEq.trans (ClassifierEq.of_eq hRaw.symm)
    (ClassifierEq.symm hRelated)

end ClassifierEq

namespace Decoration

variable [Precedence C] {bd : C.Ty → Option C.Ty}

/-- Transport a decoration along an equality of external bases. -/
def castBase {Γ Δ Ξ : C.Arity} (h : Γ = Δ) :
    Decoration bd Γ Ξ → Decoration bd Δ Ξ :=
  h ▸ fun D => D

private theorem concatenate_congr_right {bd : C.Ty → Option C.Ty}
    {Ω Γ Δ : C.Arity} (D : Decoration bd Ω Γ)
    {F G : Decoration bd (Ω ⋈ Γ) Δ} (h : F = G) :
    Decoration.concatenate D F = Decoration.concatenate D G := by
  subst G
  rfl

end Decoration

namespace DecorationEq

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

theorem castBase {Γ Δ Ξ : C.Arity} (h : Γ = Δ)
    {D F : Decoration bd Γ Ξ} (hD : DecorationEq E bd D F) :
    DecorationEq E bd (Decoration.castBase h D)
      (Decoration.castBase h F) := by
  subst Δ
  exact hD

end DecorationEq

namespace PrefixedDecoratedTelescope

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

/-- The empty rooted decorated telescope. -/
def empty (S : C.Arity) (bd : C.Ty → Option C.Ty) (Γ : C.Arity) :
    PrefixedDecoratedTelescope S bd Γ :=
  DecoratedTelescope.empty bd (S ⋈ Γ)

theorem act_empty {Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    act σ (empty S bd Γ) = empty S bd Δ := by
  rw [DecoratedTelescope.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    funext Φ Λ τ p
    cases p with
    | here x => exact False.elim (C.unit_is_empty x)
    | nested x p => exact False.elim (C.unit_is_empty x)

theorem act_liftPrefixed_decoration {Γ Δ Φ Θ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (D : Decoration bd (S ⋈ (Γ ⋈ Φ)) Θ) :
    Decoration.substitute (Φ := Φ) σ
        (Decoration.castBase (mul_assoc S Γ Φ).symm D) =
      Decoration.castBase (mul_assoc S Δ Φ).symm
        (act (Subst.liftPrefixed σ Φ)
          (⟨Θ, D⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Φ))).decoration := by
  funext Ψ Λ τ p
  simpa only [Decoration.substitute, act, Decoration.castBase] using
    (ClassifierAt.substitute_liftPrefixed
      (Φ := Φ) (Ψ := Ψ ⋈ Λ) σ (D p)).symm

/-- Dependent concatenation of rooted decorated telescopes. -/
def concatenate {Γ : C.Arity}
    (Δ : PrefixedDecoratedTelescope S bd Γ)
    (Ξ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ.arity)) :
    PrefixedDecoratedTelescope S bd Γ where
  arity := Δ.arity ⋈ Ξ.arity
  decoration := Decoration.concatenate Δ.decoration
    (Decoration.castBase (mul_assoc S Γ Δ.arity).symm Ξ.decoration)

theorem concatenate_related {Γ Δ Ξ : C.Arity}
    {D D' : Decoration bd (S ⋈ Γ) Δ}
    {F F' : Decoration bd (S ⋈ (Γ ⋈ Δ)) Ξ}
    (hD : DecorationEq E bd D D')
    (hF : DecorationEq E bd F F') :
    DecorationEq E bd
      (concatenate
        (⟨Δ, D⟩ : PrefixedDecoratedTelescope S bd Γ)
        (⟨Ξ, F⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ))).decoration
      (concatenate
        (⟨Δ, D'⟩ : PrefixedDecoratedTelescope S bd Γ)
        (⟨Ξ, F'⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ))).decoration := by
  unfold concatenate
  apply DecorationEq.concatenate hD
  apply DecorationEq.castBase
  exact hF

theorem act_concatenate {Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : PrefixedDecoratedTelescope S bd Γ)
    (Θ : PrefixedDecoratedTelescope S bd (Γ ⋈ Ξ.arity)) :
    act σ (concatenate Ξ Θ) =
      concatenate (act σ Ξ) (act (Subst.liftPrefixed σ Ξ.arity) Θ) := by
  rcases Ξ with ⟨Ξ, D⟩
  rcases Θ with ⟨Θ, F⟩
  rw [DecoratedTelescope.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    dsimp only [act, concatenate]
    have hConcatenate := Decoration.substitute_concatenate
      (S := S) (Γ := Γ) (Δ := Δ) (Φ := 1) σ D
      (Decoration.castBase (mul_assoc S Γ Ξ).symm F)
    have hLift := act_liftPrefixed_decoration
      (S := S) (bd := bd) σ F
    have hLift' :
        Decoration.substitute (Φ := Ξ) σ
            (Decoration.castBase (mul_assoc S Γ Ξ).symm F) =
          Decoration.castBase (mul_assoc S Δ Ξ).symm
            (Decoration.substitute (Φ := 1)
              (Subst.liftPrefixed σ Ξ) F) := hLift
    exact hConcatenate.trans
      (Decoration.concatenate_congr_right
        (bd := bd) (Ω := S ⋈ Δ) (Γ := Ξ) (Δ := Θ)
        (Decoration.substitute (Φ := 1) σ D) hLift')

theorem concatenate_empty_left {Γ : C.Arity}
    (Δ : PrefixedDecoratedTelescope S bd Γ) :
    concatenate (empty S bd Γ) Δ = Δ := by
  simpa [concatenate, empty, Decoration.castBase,
    DecoratedTelescope.castBase] using
    DecoratedTelescope.concatenate_empty_left Δ

theorem concatenate_empty_right {Γ : C.Arity}
    (Δ : PrefixedDecoratedTelescope S bd Γ) :
    concatenate Δ (empty S bd (Γ ⋈ Δ.arity)) = Δ := by
  simpa [concatenate, empty, Decoration.castBase,
    DecoratedTelescope.castBase] using
    DecoratedTelescope.concatenate_empty_right Δ

theorem concatenate_assoc {Γ : C.Arity}
    (Δ : PrefixedDecoratedTelescope S bd Γ)
    (Ξ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ.arity))
    (Θ : PrefixedDecoratedTelescope S bd
      ((Γ ⋈ Δ.arity) ⋈ Ξ.arity)) :
    concatenate (concatenate Δ Ξ) Θ =
      concatenate Δ (concatenate Ξ Θ) := by
  simpa only [concatenate] using
    DecoratedTelescope.concatenate_assoc Δ
      (DecoratedTelescope.castBase
        (mul_assoc S Γ Δ.arity).symm Ξ)
      (DecoratedTelescope.castBase
        (mul_assoc S (Γ ⋈ Δ.arity) Ξ.arity).symm Θ)

end PrefixedDecoratedTelescope

namespace QDTel

variable [P : Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

/-- The empty quotient decorated telescope. -/
def empty (E : EquationPresentation C S) (bd : C.Ty → Option C.Ty)
    (Γ : C.Arity) : QDTel E bd Γ :=
  mk (PrefixedDecoratedTelescope.empty S bd Γ)

/-- Dependent concatenation of quotient decorated telescopes. -/
def concatenate {Γ : C.Arity} :
    (Δ : QDTel E bd Γ) → QDTel E bd (Γ ⋈ Δ.1) → QDTel E bd Γ
  | ⟨Δ, D⟩, ⟨Ξ, F⟩ =>
      ⟨Δ ⋈ Ξ, Quotient.liftOn₂ D F
        (fun D F => QDecoration.mk
          (PrefixedDecoratedTelescope.concatenate
            (⟨Δ, D⟩ : PrefixedDecoratedTelescope S bd Γ)
            (⟨Ξ, F⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ))).decoration)
        (by
          intro D F D' F' hD hF
          apply QDecoration.sound
          apply PrefixedDecoratedTelescope.concatenate_related hD hF)⟩

@[simp]
theorem concatenate_mk {Γ : C.Arity}
    (Δ : PrefixedDecoratedTelescope S bd Γ)
    (Ξ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ.arity)) :
    concatenate (E := E) (mk (E := E) Δ) (mk (E := E) Ξ) =
      mk (E := E) (PrefixedDecoratedTelescope.concatenate Δ Ξ) := rfl

theorem act_empty {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ) :
    act σ (empty E bd Γ) = empty E bd Δ := by
  rw [empty, act_mk]
  exact congrArg (mk (E := E))
    (PrefixedDecoratedTelescope.act_empty
      (S := S) (bd := bd) (QExpr.representatives E σ))

theorem concatenate_empty_left {Γ : C.Arity} (Δ : QDTel E bd Γ) :
    concatenate (empty E bd Γ) Δ = Δ := by
  rcases Δ with ⟨Ξ, D⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      simpa only [empty, concatenate_mk] using congrArg
        (mk (E := E))
        (PrefixedDecoratedTelescope.concatenate_empty_left
          (⟨Ξ, D⟩ : PrefixedDecoratedTelescope S bd Γ))

theorem concatenate_empty_right {Γ : C.Arity} (Δ : QDTel E bd Γ) :
    concatenate Δ (empty E bd (Γ ⋈ Δ.1)) = Δ := by
  rcases Δ with ⟨Ξ, D⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      simpa only [empty, concatenate_mk] using congrArg
        (mk (E := E))
        (PrefixedDecoratedTelescope.concatenate_empty_right
          (⟨Ξ, D⟩ : PrefixedDecoratedTelescope S bd Γ))

theorem concatenate_assoc {Γ : C.Arity}
    (Δ : QDTel E bd Γ)
    (Ξ : QDTel E bd (Γ ⋈ Δ.1))
    (Θ : QDTel E bd ((Γ ⋈ Δ.1) ⋈ Ξ.1)) :
    concatenate (concatenate Δ Ξ) Θ =
      concatenate Δ (concatenate Ξ Θ) := by
  rcases Δ with ⟨Δ, D⟩
  rcases Ξ with ⟨Ξ, F⟩
  rcases Θ with ⟨Θ, G⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      induction F using Quotient.inductionOn with
      | _ F =>
          induction G using Quotient.inductionOn with
          | _ G =>
              simpa only [concatenate_mk] using congrArg
                (mk (E := E))
                (PrefixedDecoratedTelescope.concatenate_assoc
                  (⟨Δ, D⟩ : PrefixedDecoratedTelescope S bd Γ)
                  (⟨Ξ, F⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Δ))
                  (⟨Θ, G⟩ : PrefixedDecoratedTelescope S bd
                    ((Γ ⋈ Δ) ⋈ Ξ)))

theorem act_concatenate {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (Ξ : QDTel E bd Γ) (Θ : QDTel E bd (Γ ⋈ Ξ.1)) :
    act σ (concatenate Ξ Θ) =
      concatenate (act σ Ξ)
        (act (QuotientSubstitution.lift E σ Ξ.1) Θ) := by
  rcases Ξ with ⟨Ξ, D⟩
  rcases Θ with ⟨Θ, F⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      induction F using Quotient.inductionOn with
      | _ F =>
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Quotient.sound
            let κ := Subst.liftPrefixed (QExpr.representatives E σ) Ξ
            let θ := QExpr.representatives E
              (QuotientSubstitution.lift E σ Ξ)
            have hFill : ∀ {Λ : C.Arity} {υ : C.Ty}
                (x : Γ ⋈ Ξ ∋[υ] Λ), DerivEq E (κ x) (θ x) := by
              intro Λ υ x
              apply DerivEq.symm
              apply QExpr.representative_related_raw
              rfl
            have hF := PrefixedDecoratedTelescope.act_related
              (E := E) κ θ hFill (DecorationEq.refl F)
            have hConcatenate :=
              PrefixedDecoratedTelescope.concatenate_related
                (E := E)
                (DecorationEq.refl
                  (PrefixedDecoratedTelescope.act
                    (QExpr.representatives E σ)
                    (⟨Ξ, D⟩ : PrefixedDecoratedTelescope S bd Γ)).decoration)
                hF
            have hRaw := PrefixedDecoratedTelescope.act_concatenate
              (S := S) (bd := bd) (QExpr.representatives E σ)
              (⟨Ξ, D⟩ : PrefixedDecoratedTelescope S bd Γ)
              (⟨Θ, F⟩ : PrefixedDecoratedTelescope S bd (Γ ⋈ Ξ))
            have hRawParts := DecoratedTelescope.mk.inj hRaw
            have hRawDecoration := eq_of_heq hRawParts.2
            have hRawRelation := DecorationEq.of_eq (E := E) hRawDecoration
            exact DecorationEq.trans hRawRelation hConcatenate

end QDTel

open ArityMod MonoidalCategory

noncomputable section

variable [Precedence C]

private def qdtelShape (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    QDTelModule E bd ⟶ arityConst E.quotientMonad where
  app _ := ↾fun Ξ => Ξ.1
  naturality := by
    intros
    rfl

/-- Quotient decorated telescopes with their substitution-invariant raw
shape. -/
def QDTelArityMod (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) : ArityMod E.quotientMonad :=
  Over.mk (qdtelShape E bd)

@[simp]
theorem QDTelArityMod_module (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    module (QDTelArityMod E bd) = QDTelModule E bd := rfl

@[simp]
theorem QDTelArityMod_shape (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) {Γ : C.Arity} (Ξ : QDTel E bd Γ) :
    shape (QDTelArityMod E bd) Ξ = Ξ.1 := rfl

private def qdtelUnitNat (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    module (tensorUnit (C := C) (T := E.quotientMonad)) ⟶
      module (QDTelArityMod E bd) where
  app Γ := ↾fun _ => QDTel.empty E bd Γ
  naturality {Γ Δ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    simp only [ConcreteCategory.comp_apply]
    exact (QDTel.act_empty (E := E) (bd := bd) σ).symm

/-- The empty quotient decorated telescope as a shape-preserving morphism. -/
def QDTelOne (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    tensorUnit (C := C) (T := E.quotientMonad) ⟶ QDTelArityMod E bd :=
  Over.homMk (qdtelUnitNat E bd) (by
    apply NatTrans.ext
    funext Γ
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

private def qdtelMulNat (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    module (ArityMod.tensorObj (QDTelArityMod E bd)
      (QDTelArityMod E bd)) ⟶
      module (QDTelArityMod E bd) where
  app _ := ↾fun ⟨Ξ, Θ⟩ => QDTel.concatenate Ξ Θ
  naturality {Γ Δ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Ξ, Θ⟩
    simp only [ConcreteCategory.comp_apply]
    exact (QDTel.act_concatenate (E := E) (bd := bd) σ Ξ Θ).symm

/-- Dependent concatenation of quotient telescopes as a shape-preserving
morphism. -/
def QDTelMul (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    ArityMod.tensorObj (QDTelArityMod E bd) (QDTelArityMod E bd) ⟶
      QDTelArityMod E bd :=
  Over.homMk (qdtelMulNat E bd) (by
    apply NatTrans.ext
    funext Γ
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Ξ, Θ⟩
    rfl)

private theorem qdtel_one_mul (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    tensorMap (QDTelOne E bd) (𝟙 (QDTelArityMod E bd)) ≫
        QDTelMul E bd =
      (tensorLeftUnitor (QDTelArityMod E bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨u, Ξ⟩
  cases u
  simp [QDTelOne, QDTelMul, qdtelUnitNat, qdtelMulNat, tensorMap,
    tensorLeftUnitor]
  exact QDTel.concatenate_empty_left Ξ

private theorem qdtel_mul_one (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    tensorMap (𝟙 (QDTelArityMod E bd)) (QDTelOne E bd) ≫
        QDTelMul E bd =
      (tensorRightUnitor (QDTelArityMod E bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Ξ, u⟩
  cases u
  simp [QDTelOne, QDTelMul, qdtelUnitNat, qdtelMulNat, tensorMap,
    tensorRightUnitor]
  exact QDTel.concatenate_empty_right Ξ

private theorem qdtel_mul_assoc (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    tensorMap (QDTelMul E bd) (𝟙 (QDTelArityMod E bd)) ≫
        QDTelMul E bd =
      (tensorAssociator (QDTelArityMod E bd) (QDTelArityMod E bd)
          (QDTelArityMod E bd)).hom ≫
        tensorMap (𝟙 (QDTelArityMod E bd)) (QDTelMul E bd) ≫
          QDTelMul E bd := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Ξ, Θ⟩, Ω⟩
  simp [QDTelMul, qdtelMulNat, tensorMap, tensorAssociator]
  exact QDTel.concatenate_assoc Ξ Θ Ω

instance (E : EquationPresentation C S) (bd : C.Ty → Option C.Ty) :
    MonObj (QDTelArityMod E bd) where
  one := QDTelOne E bd
  mul := QDTelMul E bd
  one_mul := qdtel_one_mul E bd
  mul_one := qdtel_mul_one E bd
  mul_assoc := qdtel_mul_assoc E bd

/-- Quotient decorated telescopes form a monoid object in arity-shaped
modules over quotient syntax. -/
def QDTelMon (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) : CategoryTheory.Mon (ArityMod E.quotientMonad) :=
  CategoryTheory.Mon.mk (QDTelArityMod E bd)

@[simp]
theorem QDTelMon_one (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    MonObj.one (X := (QDTelMon E bd).X) = QDTelOne E bd := rfl

@[simp]
theorem QDTelMon_mul (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) :
    MonObj.mul (X := (QDTelMon E bd).X) = QDTelMul E bd := rfl

end

end Equations
