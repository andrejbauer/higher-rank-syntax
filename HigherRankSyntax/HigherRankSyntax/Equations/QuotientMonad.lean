import HigherRankSyntax.Equations.Derivation

/-!
# Quotient syntax and its relative monad

Derivable equality is bundled locally as a setoid only to form Lean's ordinary
`Quotient`.  Raw slots and the source functor `J C` remain set-valued and
unchanged.  Objectwise quotient elimination needs no choice.

Kleisli extension receives quotient-valued fillers.  Its implementation
selects one raw representative of each filler, performs raw fixed-prefix
substitution, and returns the resulting equivalence class.  Two-sided
substitution congruence proves independence from both expression and filler
representatives.  Representative selection is the only noncomputable part of
the construction.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A} {S : C.Arity}

namespace Equations

namespace DerivEq

/-- The setoid locally presenting derivable equality on one expression fibre. -/
def setoid (E : EquationPresentation C S) (Ω : C.Arity) (τ : C.Ty) :
    Setoid (Expr Ω τ) where
  r := DerivEq E
  iseqv := ⟨.refl, .symm, .trans⟩

end DerivEq

/-- Fixed-signature expressions modulo derivable equality. -/
def QExpr (E : EquationPresentation C S) (Γ Φ : C.Arity) (τ : C.Ty) :=
  Quotient (DerivEq.setoid E (S ⋈ Γ ⋈ Φ) τ)

namespace QExpr

/-- The equivalence class of a raw fixed-signature expression. -/
def mk (E : EquationPresentation C S) {Γ Φ : C.Arity} {τ : C.Ty}
    (e : STerm S Γ Φ τ) : QExpr E Γ Φ τ :=
  Quotient.mk _ e

/-- Derivably equal raw expressions define equal quotient expressions. -/
theorem sound (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} {e e' : STerm S Γ Φ τ}
    (h : DerivEq E e e') : mk E e = mk E e' :=
  Quotient.sound h

/-- Equality of raw expression classes reflects derivable equality. -/
theorem exact (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} {e e' : STerm S Γ Φ τ}
    (h : mk E e = mk E e') : DerivEq E e e' :=
  Quotient.exact h

/-- Eliminate one quotient expression into a type when the function on raw
representatives respects derivable equality. -/
def lift (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} {X : Sort _}
    (f : STerm S Γ Φ τ → X)
    (h : ∀ e e', DerivEq E e e' → f e = f e') :
    QExpr E Γ Φ τ → X :=
  Quotient.lift f h

@[simp]
theorem lift_mk (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} {X : Sort _}
    (f : STerm S Γ Φ τ → X)
    (h : ∀ e e', DerivEq E e e' → f e = f e')
    (e : STerm S Γ Φ τ) :
    lift E f h (mk E e) = f e := rfl

noncomputable section

/-- A selected raw representative used to build a raw substitution. -/
private def representative (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} (e : QExpr E Γ Φ τ) :
    STerm S Γ Φ τ :=
  Quotient.out e

/-- The selected representative belongs to the selected quotient class. -/
private theorem mk_representative (E : EquationPresentation C S)
    {Γ Φ : C.Arity} {τ : C.Ty} (e : QExpr E Γ Φ τ) :
    mk E (representative E e) = e :=
  Quotient.out_eq e

/-- Select a raw filler for every quotient-valued filler. -/
def representatives (E : EquationPresentation C S) {Γ Δ : C.Arity}
    (σ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ) :
    Subst Γ (S ⋈ Δ) :=
  fun ⦃Λ⦄ ⦃τ⦄ x => representative E (σ Λ τ x)

/-- Quotienting a selected filler recovers the original quotient filler. -/
theorem mk_representatives (E : EquationPresentation C S) {Γ Δ : C.Arity}
    (σ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ)
    {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ) :
    mk E (representatives E σ x) = σ Λ τ x :=
  mk_representative E _

/-- Pointwise equal quotient substitutions have derivably equal selected raw
fillers. -/
theorem representatives_related (E : EquationPresentation C S)
    {Γ Δ : C.Arity}
    (σ θ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ)
    (h : ∀ {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ),
      σ Λ τ x = θ Λ τ x)
    {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ) :
    DerivEq E (representatives E σ x) (representatives E θ x) :=
  exact E ((mk_representatives E σ x).trans
    ((h x).trans (mk_representatives E θ x).symm))

/-- A selected filler is derivably equal to any raw representative of its
quotient class. -/
theorem representative_related_raw (E : EquationPresentation C S)
    {Γ Δ : C.Arity}
    (σ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ)
    {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ)
    (e : STerm S Δ Λ τ) (h : σ Λ τ x = mk E e) :
    DerivEq E (representatives E σ x) e :=
  exact E ((mk_representatives E σ x).trans h)

/-- Action of a quotient-valued substitution on a quotient expression. -/
def act (E : EquationPresentation C S) {Γ Δ : C.Arity}
    (σ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ)
    {Φ : C.Arity} {τ : C.Ty} : QExpr E Γ Φ τ → QExpr E Δ Φ τ :=
  lift E
    (fun e => mk E (Subst.act (Γ := S) (representatives E σ) Φ e))
    (fun _ _ h => sound E (DerivEq.substitute_same E h (representatives E σ)))

@[simp]
theorem act_mk (E : EquationPresentation C S) {Γ Δ Φ : C.Arity}
    {τ : C.Ty}
    (σ : ∀ Λ υ, Γ ∋[υ] Λ → QExpr E Δ Λ υ)
    (e : STerm S Γ Φ τ) :
    act E σ (mk E e) =
      mk E (Subst.act (Γ := S) (representatives E σ) Φ e) := rfl

/-- Quotient substitution is independent of pointwise-equal quotient-valued
fillers. -/
theorem act_congr (E : EquationPresentation C S) {Γ Δ : C.Arity}
    (σ θ : ∀ Λ τ, Γ ∋[τ] Λ → QExpr E Δ Λ τ)
    (h : ∀ {Λ : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] Λ),
      σ Λ τ x = θ Λ τ x)
    {Φ : C.Arity} {τ : C.Ty} (e : QExpr E Γ Φ τ) :
    act E σ e = act E θ e := by
  induction e using Quotient.inductionOn with
  | _ e =>
      apply sound
      apply DerivEq.substitute_fillers
      exact representatives_related E σ θ h

end

end QExpr

namespace EquationPresentation

noncomputable section

/-- The relative monad of fixed-signature expressions modulo the equations of
`E`. -/
def quotientMonad (E : EquationPresentation C S) : RelativeMonad (J C) where
  map Γ := ⟨fun Φ τ => QExpr E Γ Φ τ⟩

  η Γ Λ τ x := QExpr.mk E (Expr.η (C.inr x))

  lift f Φ τ e := QExpr.act E f e

  unit_right := by
    intro Γ
    funext Φ τ e
    induction e using Quotient.inductionOn with
    | _ e =>
        apply QExpr.sound
        let σ : Subst Γ (S ⋈ Γ) :=
          fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr x)
        have hfill : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
            DerivEq E
              (QExpr.representatives E
                (fun Λ τ x => QExpr.mk E (Expr.η (C.inr x))) x)
              (σ x) := by
          intro Λ υ x
          apply QExpr.representative_related_raw
          rfl
        have h := DerivEq.substitute_fillers E e
          (QExpr.representatives E
            (fun Λ τ x => QExpr.mk E (Expr.η (C.inr x)))) σ hfill
        have hraw : Subst.act (Γ := S) σ Φ e = e := by
          apply act_idOfη
          intro Λ υ x
          rfl
        rw [hraw] at h
        exact h

  unit_left := by
    intro Γ Δ f
    funext Λ τ x
    symm
    calc
      QExpr.act E f (QExpr.mk E (Expr.η (C.inr x))) =
          QExpr.mk E
            (Subst.act (Γ := S) (QExpr.representatives E f) Λ
              (Expr.η (C.inr x))) := QExpr.act_mk E f _
      _ = QExpr.mk E (QExpr.representatives E f x) :=
        congrArg (QExpr.mk E) (act_η_prefixed (QExpr.representatives E f) Λ x)
      _ = f Λ τ x := QExpr.mk_representatives E f x

  comp_lift := by
    intro Γ Δ Ξ f g
    funext Φ τ e
    induction e using Quotient.inductionOn with
    | _ e =>
        apply QExpr.sound
        let σ := QExpr.representatives E f
        let θ := QExpr.representatives E g
        let κ : Subst Γ (S ⋈ Ξ) := Subst.comp σ θ
        let κ' := fun Λ υ (x : Γ ∋[υ] Λ) => QExpr.act E g (f Λ υ x)
        have hfill : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
            DerivEq E (QExpr.representatives E κ' x)
              (κ x) := by
          intro Λ υ x
          apply QExpr.exact
          calc
            QExpr.mk E
                (QExpr.representatives E κ' x) =
                κ' Λ υ x :=
              QExpr.mk_representatives E _ x
            _ = QExpr.act E g (f Λ υ x) := rfl
            _ = QExpr.act E g (QExpr.mk E (σ x)) :=
              congrArg (QExpr.act E g) (QExpr.mk_representatives E f x).symm
            _ = QExpr.mk E (Subst.act (Γ := S) θ Λ (σ x)) :=
              QExpr.act_mk E g _
            _ = QExpr.mk E (κ x) := rfl
        have h := DerivEq.substitute_fillers E e
          (QExpr.representatives E κ') κ hfill
        have hraw := act_comp σ θ Φ e
        rw [hraw] at h
        exact h

/-- The quotient map from raw fixed-prefix syntax to quotient syntax. -/
def quotientHom (E : EquationPresentation C S) :
    RelativeMonad.Hom (PrefixedSyntaxMonad C S) E.quotientMonad where
  map_hom Φ τ e := QExpr.mk E e
  hom_unit := rfl
  hom_lift f := by
    funext Φ τ e
    apply QExpr.sound
    apply DerivEq.substitute_fillers
    intro Λ υ x
    apply DerivEq.symm
    apply QExpr.representative_related_raw
    rfl

/-- The identity-on-context functor from raw fixed-prefix substitutions to
quotient substitutions. -/
def quotientKleisliFunctor (E : EquationPresentation C S) :
    RelativeMonad.Kleisli (PrefixedSyntaxMonad C S) ⥤
      RelativeMonad.Kleisli E.quotientMonad :=
  E.quotientHom.kleisliFunctor

end

end EquationPresentation

end Equations
