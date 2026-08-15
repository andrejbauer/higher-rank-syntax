import HigherRankSyntax.Equations.QuotientMonad
import MagmaSignature

/-!
# Monoids as an equational presentation

This example extends the one-sorted magma signature by a nullary unit symbol.
Associativity and the two unit laws are declared as equation schemas.  Their
simultaneous substitution instances and structural congruence are derivable,
and therefore become ordinary equalities in quotient syntax.
-/

namespace Monoids

open ListCarrier
open Equations
open Magmas

/-- The one-sorted carrier used by the monoid presentation. -/
abbrev monoidCarrier := magmaCarrier

/-- The monoid signature consists of a nullary unit and binary multiplication. -/
def monoidSignature : monoidCarrier.Arity :=
  ofList [nullaryEntry, binaryEntry]

/-- The unit-operation slot. -/
def unitSlot : monoidSignature ∋[()] (1 : monoidCarrier.Arity) :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

/-- The multiplication-operation slot. -/
def multiplicationSlot : monoidSignature ∋[()] variableContext 2 :=
  ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩

@[simp]
theorem monoidArity_right_unit (Γ : monoidCarrier.Arity) :
    Γ ⋈ (1 : monoidCarrier.Arity) = Γ := rfl

/-- Raw monoid terms in `n` metavariables. -/
abbrev MonoidTerm (n : ℕ) := STerm monoidSignature (variableContext n) 1 ()

/-- The `j`-th metavariable as a monoid term. -/
def variableTerm (n : ℕ) (j : Fin n) : MonoidTerm n :=
  Expr.η (monoidCarrier.inr (variableSlot n j))

/-- The nullary unit term. -/
def unit (n : ℕ) : MonoidTerm n :=
  .ap (monoidCarrier.inl (monoidCarrier.inl unitSlot))
    (fun ⦃_⦄ ⦃_⦄ i => False.elim (monoidCarrier.unit_is_empty i))

/-- The two arguments of a multiplication term. -/
def multiplicationArguments (n : ℕ) (e f : MonoidTerm n) :
    Expr.Args (monoidSignature ⋈ variableContext n) (variableContext 2) :=
  fun ⦃_⦄ {τ} i =>
    match τ with
    | () => multiplicationArgument_cases
        (motive := fun {Δ} _ =>
          Expr (monoidSignature ⋈ variableContext n ⋈ Δ) ())
        e f i

/-- Binary multiplication of raw monoid terms. -/
def multiplication (n : ℕ) (e f : MonoidTerm n) : MonoidTerm n :=
  .ap (monoidCarrier.inl (monoidCarrier.inl multiplicationSlot))
    (multiplicationArguments n e f)

@[simp]
theorem multiplicationArguments_left (n : ℕ) (e f : MonoidTerm n) :
    multiplicationArguments n e f (variableSlot 2 ⟨0, by decide⟩) = e := rfl

@[simp]
theorem multiplicationArguments_right (n : ℕ) (e f : MonoidTerm n) :
    multiplicationArguments n e f (variableSlot 2 ⟨1, by decide⟩) = f := rfl

/-- The left side of the associativity schema. -/
def associativityLeft : MonoidTerm 3 :=
  multiplication 3
    (multiplication 3 (variableTerm 3 ⟨0, by decide⟩) (variableTerm 3 ⟨1, by decide⟩))
    (variableTerm 3 ⟨2, by decide⟩)

/-- The right side of the associativity schema. -/
def associativityRight : MonoidTerm 3 :=
  multiplication 3 (variableTerm 3 ⟨0, by decide⟩)
    (multiplication 3 (variableTerm 3 ⟨1, by decide⟩) (variableTerm 3 ⟨2, by decide⟩))

/-- The left side of the left-unit schema. -/
def leftUnitLeft : MonoidTerm 1 :=
  multiplication 1 (unit 1) (variableTerm 1 ⟨0, by decide⟩)

/-- The right side of the left-unit schema. -/
def leftUnitRight : MonoidTerm 1 := variableTerm 1 ⟨0, by decide⟩

/-- The left side of the right-unit schema. -/
def rightUnitLeft : MonoidTerm 1 :=
  multiplication 1 (variableTerm 1 ⟨0, by decide⟩) (unit 1)

/-- The right side of the right-unit schema. -/
def rightUnitRight : MonoidTerm 1 := variableTerm 1 ⟨0, by decide⟩

/-- The three defining equation schemas of monoids. -/
inductive MonoidAxiom :
    {Γ Φ : monoidCarrier.Arity} → {τ : monoidCarrier.Ty} →
      STerm monoidSignature Γ Φ τ →
      STerm monoidSignature Γ Φ τ → Prop where
  | associativity : MonoidAxiom associativityLeft associativityRight
  | leftUnit : MonoidAxiom leftUnitLeft leftUnitRight
  | rightUnit : MonoidAxiom rightUnitLeft rightUnitRight

/-- The equational presentation of monoids. -/
def monoidEquations : EquationPresentation monoidCarrier monoidSignature where
  axioms := MonoidAxiom

theorem associativity_generator :
    DerivEq monoidEquations associativityLeft associativityRight :=
  .of_axiom .associativity

theorem leftUnit_generator :
    DerivEq monoidEquations leftUnitLeft leftUnitRight :=
  .of_axiom .leftUnit

theorem rightUnit_generator :
    DerivEq monoidEquations rightUnitLeft rightUnitRight :=
  .of_axiom .rightUnit

/-- The three fillers used in the associativity instance. -/
def associativityFiller : Fin 3 → MonoidTerm 2 :=
  Fin.cases
    (multiplication 2 (variableTerm 2 ⟨0, by decide⟩) (variableTerm 2 ⟨1, by decide⟩))
    (fun j => Fin.cases (unit 2)
      (fun j => Fin.cases
        (multiplication 2 (variableTerm 2 ⟨1, by decide⟩)
          (variableTerm 2 ⟨0, by decide⟩))
        (fun j => Fin.elim0 j) j) j)

/-- A nontrivial simultaneous substitution for the three associativity
metavariables. -/
def associativitySubstitution :
    Subst (variableContext 3) (monoidSignature ⋈ variableContext 2) :=
  fun {_} {τ} x =>
    match τ with
    | () => variableSlot_cases 3
        (motive := fun {Λ} _ =>
          Expr (monoidSignature ⋈ variableContext 2 ⋈ Λ) ())
        associativityFiller x

/-- The nontrivial simultaneous-substitution instance of associativity. -/
theorem associativity_instance :
    DerivEq monoidEquations
      (Subst.act (Γ := monoidSignature) associativitySubstitution 1
        associativityLeft)
      (Subst.act (Γ := monoidSignature) associativitySubstitution 1
        associativityRight) :=
  DerivEq.axiom_instance monoidEquations .associativity associativitySubstitution

/-- Multiplication respects derivable equality in both arguments. -/
theorem multiplication_congr {n : ℕ} {e e' f f' : MonoidTerm n}
    (he : DerivEq monoidEquations e e')
    (hf : DerivEq monoidEquations f f') :
    DerivEq monoidEquations
      (multiplication n e f) (multiplication n e' f') := by
  apply DerivEq.application
  intro Δ τ i
  exact match τ with
    | () => multiplicationArgument_cases
        (motive := fun {Δ} i =>
          DerivEq monoidEquations
            (multiplicationArguments n e f i)
            (multiplicationArguments n e' f' i))
        he hf i

theorem multiplication_congruence_example :
    DerivEq monoidEquations
      (multiplication 1 leftUnitLeft (variableTerm 1 ⟨0, by decide⟩))
      (multiplication 1 leftUnitRight (variableTerm 1 ⟨0, by decide⟩)) :=
  multiplication_congr leftUnit_generator (.refl _)

/-- Quotient monoid terms in `n` metavariables. -/
abbrev QuotientMonoidTerm (n : ℕ) :=
  QExpr monoidEquations (variableContext n) 1 ()

theorem quotient_associativity :
    QExpr.mk monoidEquations associativityLeft =
      QExpr.mk monoidEquations associativityRight :=
  QExpr.sound monoidEquations associativity_generator

theorem quotient_left_unit :
    QExpr.mk monoidEquations leftUnitLeft =
      QExpr.mk monoidEquations leftUnitRight :=
  QExpr.sound monoidEquations leftUnit_generator

theorem quotient_right_unit :
    QExpr.mk monoidEquations rightUnitLeft =
      QExpr.mk monoidEquations rightUnitRight :=
  QExpr.sound monoidEquations rightUnit_generator

theorem quotient_associativity_instance :
    QExpr.mk monoidEquations
        (Subst.act (Γ := monoidSignature) associativitySubstitution 1
          associativityLeft) =
      QExpr.mk monoidEquations
        (Subst.act (Γ := monoidSignature) associativitySubstitution 1
          associativityRight) :=
  QExpr.sound monoidEquations associativity_instance

theorem quotient_multiplication_congruence :
    QExpr.mk monoidEquations
        (multiplication 1 leftUnitLeft (variableTerm 1 ⟨0, by decide⟩)) =
      QExpr.mk monoidEquations
        (multiplication 1 leftUnitRight (variableTerm 1 ⟨0, by decide⟩)) :=
  QExpr.sound monoidEquations multiplication_congruence_example

example (n : ℕ) (j : Fin n) :
    monoidEquations.quotientMonad.η (variableContext n) 1 () (variableSlot n j) =
      QExpr.mk monoidEquations (variableTerm n j) := rfl

/-- The quotient Kleisli extension computes by raw fixed-prefix substitution,
up to the quotient equality that removes the selected representatives. -/
theorem quotient_kleisli_computation (e : MonoidTerm 3) :
    QExpr.mk monoidEquations
        (Subst.act (Γ := monoidSignature) associativitySubstitution 1 e) =
      monoidEquations.quotientMonad.lift
        (fun _ _ x => QExpr.mk monoidEquations (associativitySubstitution x))
        1 () (QExpr.mk monoidEquations e) := by
  exact congrArg (fun k => k 1 () e)
    (monoidEquations.quotientHom.hom_lift associativitySubstitution)

end Monoids
