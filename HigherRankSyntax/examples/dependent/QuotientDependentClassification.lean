import DependentClassification
import HigherRankSyntax.Equations.QuotientTelescopeMonoid

/-!
# Dependent classifiers modulo equations

The presentation below equates two raw type variables `A` and `B`.  Its
quotient identifies the one-slot telescope `x : A` with `x : B`, while the raw
one-slot shape remains unchanged.  Substitution instantiates the equation, and
application congruence carries it into a larger classifier `P(A) = P(B)`.

These checks concern equality of raw classifier annotations only.  They do not
assert formation, typing, or conversion judgments.
-/

namespace QuotientDependentClassification

open CategoryTheory
open Equations
open ListCarrier
open T1

noncomputable section

abbrev typePair : depCarrier.Arity := oneCtx .ty ⋈ oneCtx .ty

inductive TypeEquation :
    {Γ Φ : depCarrier.Arity} → {τ : RawClass} →
      STerm binSig Γ Φ τ → STerm binSig Γ Φ τ → Prop where
  | variables : TypeEquation (Γ := typePair) (Φ := 1) extTy priorTy

def equationPresentation : EquationPresentation depCarrier binSig where
  axioms := TypeEquation

theorem variables_derivable :
    DerivEq equationPresentation extTy priorTy := by
  apply DerivEq.of_axiom (Γ := typePair) (Φ := 1)
  exact TypeEquation.variables

def xAtExt : Decoration bd (binSig ⋈ typePair) (oneCtx .tm) :=
  oneDec (binSig ⋈ typePair) .tm extTy

def xAtPrior : Decoration bd (binSig ⋈ typePair) (oneCtx .tm) :=
  oneDec (binSig ⋈ typePair) .tm priorTy

theorem classifier_variables :
    ClassifierEq equationPresentation bd (Ω := extPrior) (τ := .tm)
      extTy priorTy := by
  unfold ClassifierEq
  apply Quotient.sound
  exact variables_derivable

private theorem emptyPath {Φ Λ : depCarrier.Arity} {τ : RawClass} :
    DecorationPath (C := depCarrier) 1 Φ Λ τ → False
  | .here x => depCarrier.unit_is_empty x
  | .nested x _ => depCarrier.unit_is_empty x

theorem xAtExt_equivalent_xAtPrior :
    DecorationEq equationPresentation bd xAtExt xAtPrior := by
  intro Φ Λ τ p
  cases p with
  | here x =>
      apply oneSlot_cases .tm
        (motive := fun {Λ} {τ} x =>
          ClassifierEq equationPresentation bd
            (xAtExt (.here x)) (xAtPrior (.here x)))
      exact classifier_variables
  | nested x p =>
      have h := oneSlot_arity .tm x
      cases h
      exact False.elim (emptyPath p)

def extTelescope :
    PrefixedDecoratedTelescope binSig bd typePair :=
  ⟨oneCtx .tm, xAtExt⟩

def priorTelescope :
    PrefixedDecoratedTelescope binSig bd typePair :=
  ⟨oneCtx .tm, xAtPrior⟩

def quotientExt : QDTel equationPresentation bd typePair :=
  QDTel.mk extTelescope

example :
    QDTel.mk (E := equationPresentation) extTelescope =
      QDTel.mk (E := equationPresentation) priorTelescope := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply QDecoration.sound
    exact xAtExt_equivalent_xAtPrior

def identitySubstitution : Subst typePair (binSig ⋈ typePair) :=
  fun {_} {_} x => Expr.η (depCarrier.inr x)

example :
    QDTel.mk (E := equationPresentation)
        (PrefixedDecoratedTelescope.act identitySubstitution extTelescope) =
      QDTel.act
        (fun _ _ x => QExpr.mk equationPresentation (identitySubstitution x))
        quotientExt :=
  QDTel.mk_act identitySubstitution extTelescope

def repeatedType : Expr (C := depCarrier) (binSig ⋈ oneCtx .ty) .ty :=
  .ap (depCarrier.inl binSlot)
    (fun {_} {_} x =>
      binArg_cases
        (motive := fun {Δ} {τ} _ =>
          Expr (binSig ⋈ oneCtx .ty ⋈ Δ) τ)
        replacementTy replacementTy x)

def equationSubstitution :
    Subst typePair (binSig ⋈ oneCtx .ty) :=
  fun {Δ} {τ} x =>
    depCarrier.copair (oneCtx .ty) (oneCtx .ty)
      (Expr (binSig ⋈ oneCtx .ty ⋈ Δ) τ)
      (fun y => oneSlot_cases .ty
        (motive := fun {Δ} {τ} _ =>
          Expr (binSig ⋈ oneCtx .ty ⋈ Δ) τ)
        replacementTy y)
      (fun y => oneSlot_cases .ty
        (motive := fun {Δ} {τ} _ =>
          Expr (binSig ⋈ oneCtx .ty ⋈ Δ) τ)
        repeatedType y)
      x

example :
    DerivEq equationPresentation
      (Subst.act (Γ := binSig) equationSubstitution 1 extTy)
      (Subst.act (Γ := binSig) equationSubstitution 1 priorTy) :=
  DerivEq.axiom_instance equationPresentation TypeEquation.variables
    equationSubstitution

def binApplication (a b : Expr (C := depCarrier) extPrior .ty) :
    Expr (C := depCarrier) extPrior .ty :=
  .ap (depCarrier.inl (depCarrier.inl binSlot))
    (fun {_} {_} x =>
      binArg_cases
        (motive := fun {Δ} {τ} _ => Expr (extPrior ⋈ Δ) τ)
        a b x)

theorem application_congruence :
    DerivEq equationPresentation
      (binApplication extTy extTy) (binApplication priorTy extTy) := by
  unfold binApplication
  apply DerivEq.application
  intro Δ τ x
  let args : Expr.Args extPrior binArgs :=
    fun {_} {_} x => binArg_cases
      (motive := fun {Δ} {τ} _ => Expr (extPrior ⋈ Δ) τ)
      extTy extTy x
  let args' : Expr.Args extPrior binArgs :=
    fun {_} {_} x => binArg_cases
      (motive := fun {Δ} {τ} _ => Expr (extPrior ⋈ Δ) τ)
      priorTy extTy x
  apply binArg_cases
    (motive := fun {Δ} {τ} x => DerivEq equationPresentation
      (args x) (args' x))
  · dsimp [args, args']
    exact variables_derivable
  · exact DerivEq.refl extTy

def appliedExt : Decoration bd extPrior (oneCtx .tm) :=
  oneDec extPrior .tm (binApplication extTy extTy)

def appliedPrior : Decoration bd extPrior (oneCtx .tm) :=
  oneDec extPrior .tm (binApplication priorTy extTy)

theorem applied_classifier_equivalent :
    DecorationEq equationPresentation bd appliedExt appliedPrior := by
  intro Φ Λ τ p
  cases p with
  | here x =>
      apply oneSlot_cases .tm
        (motive := fun {Λ} {τ} x =>
          ClassifierEq equationPresentation bd
            (appliedExt (.here x)) (appliedPrior (.here x)))
      unfold ClassifierEq
      exact Quotient.sound application_congruence
  | nested x p =>
      have h := oneSlot_arity .tm x
      cases h
      exact False.elim (emptyPath p)

example : CategoryTheory.Mon
    (ArityMod equationPresentation.quotientMonad) :=
  QDTelMon equationPresentation bd

example :
    ArityMod.shape (QDTelArityMod equationPresentation bd) quotientExt =
      oneCtx .tm := rfl

example :
    (QDTelOne equationPresentation bd).left.app
        (RelativeMonad.Kleisli.of equationPresentation.quotientMonad typePair)
        PUnit.unit =
      QDTel.empty equationPresentation bd typePair := rfl

example :
    QDTel.concatenate quotientExt
        (QDTel.empty equationPresentation bd (typePair ⋈ quotientExt.1)) =
      quotientExt :=
  QDTel.concatenate_empty_right quotientExt

example :
    MonObj.one (X := (QDTelMon equationPresentation bd).X) =
      QDTelOne equationPresentation bd :=
  QDTelMon_one equationPresentation bd

example :
    MonObj.mul (X := (QDTelMon equationPresentation bd).X) =
      QDTelMul equationPresentation bd :=
  QDTelMon_mul equationPresentation bd

end

end QuotientDependentClassification
