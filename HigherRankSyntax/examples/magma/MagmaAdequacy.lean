import MagmaTerm

/-!
# Adequacy of magma expressions

The ground expressions over `magmaSignature ⋈ variableContext n` are ordinary
binary trees in `n` variables.
-/

namespace Magmas

/-- Translate an expression known to be a ground magma expression. -/
noncomputable def toMagmaTermAux (n : ℕ) {Γ : magmaCarrier.Arity} {τ : magmaCarrier.Ty}
    (e : Expr (C := magmaCarrier) Γ τ)
    (hΓ : Γ = magmaSignature ⋈ variableContext n) (hτ : τ = ()) : MagmaTerm n :=
  Expr.rec
    (motive := fun Γ τ _ =>
      Γ = magmaSignature ⋈ variableContext n → τ = () → MagmaTerm n)
    (fun {Γ α τ} x args ih hΓ hτ => by
      subst Γ
      cases hτ
      exact match (magmaCarrier.slotAt_mul magmaSignature (variableContext n) α ()).symm x with
      | .inl y =>
        signatureSlot_cases
          (motive := fun {α} _ =>
            Expr.Args (magmaSignature ⋈ variableContext n) α →
              (∀ {Δ} {σ} (i : α ∋[σ] Δ),
                magmaSignature ⋈ variableContext n ⋈ Δ = magmaSignature ⋈ variableContext n →
                σ = () → MagmaTerm n) → MagmaTerm n)
          (fun args ih =>
            .multiplication
              (ih (variableSlot 2 ⟨0, by decide⟩) rfl rfl)
              (ih (variableSlot 2 ⟨1, by decide⟩) rfl rfl))
          y args (fun {Δ} {σ} i hΓ hτ => ih i hΓ hτ)
      | .inr y =>
        .variable (variableSlotIndex n y))
    e hΓ hτ

/-- Translate a ground magma expression to its ordinary binary tree. -/
noncomputable def toMagmaTerm (n : ℕ)
    (e : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) : MagmaTerm n :=
  toMagmaTermAux n e rfl rfl

theorem toMagmaTerm_variableHead (n : ℕ) (j : Fin n)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) 1) :
    toMagmaTerm n (.ap (magmaCarrier.inr (variableSlot n j)) args) = .variable j := by
  unfold toMagmaTerm toMagmaTermAux
  simp

theorem toMagmaTerm_multiplication (n : ℕ)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) (variableContext 2)) :
    toMagmaTerm n (.ap (magmaCarrier.inl multiplicationSlot) args) =
      .multiplication
        (toMagmaTerm n (args (variableSlot 2 ⟨0, by decide⟩)))
        (toMagmaTerm n (args (variableSlot 2 ⟨1, by decide⟩))) := by
  rfl

theorem toMagmaTermAux_multiplication (n : ℕ)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) (variableContext 2)) :
    toMagmaTermAux n (.ap (magmaCarrier.inl multiplicationSlot) args) rfl rfl =
      .multiplication
        (toMagmaTermAux n (args (variableSlot 2 ⟨0, by decide⟩)) rfl rfl)
        (toMagmaTermAux n (args (variableSlot 2 ⟨1, by decide⟩)) rfl rfl) := by
  rfl

theorem toMagmaTermAux_variableHead (n : ℕ) {α : magmaCarrier.Arity}
    (y : variableContext n ∋[()] α)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) α) :
    toMagmaTermAux n (.ap (magmaCarrier.inr y) args) rfl rfl =
      .variable (variableSlotIndex n y) := by
  unfold toMagmaTermAux
  simp

theorem toMagmaTerm_variableExpression (n : ℕ) (j : Fin n) :
    toMagmaTerm n (variableExpression n j) = .variable j := by
  rw [variableExpression, Expr.η.eq_1, magmaCarrier.unit_right]
  apply toMagmaTerm_variableHead

/-- Translate a binary tree to the corresponding ground magma expression. -/
def ofMagmaTerm (n : ℕ) : MagmaTerm n →
    Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()
  | .variable j => variableExpression n j
  | .multiplication e f => multiplicationExpression n (ofMagmaTerm n e) (ofMagmaTerm n f)

/-- Translating a binary tree to an expression and back is the identity. -/
theorem toMagmaTerm_ofMagmaTerm (n : ℕ) :
    ∀ e : MagmaTerm n, toMagmaTerm n (ofMagmaTerm n e) = e
  | .variable j => toMagmaTerm_variableExpression n j
  | .multiplication e f => by
    rw [ofMagmaTerm]
    unfold multiplicationExpression
    rw [toMagmaTerm_multiplication,
      multiplicationArguments_left, multiplicationArguments_right,
      toMagmaTerm_ofMagmaTerm n e, toMagmaTerm_ofMagmaTerm n f]

theorem variableHead_eq_variableExpression (n : ℕ)
    {α : magmaCarrier.Arity} (y : variableContext n ∋[()] α)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) α) :
    .ap (magmaCarrier.inr y) args = variableExpression n (variableSlotIndex n y) := by
  have hα := variableSlot_arity n y
  subst α
  rw [variableSlot_eq_variableSlotIndex n y, variableExpression, Expr.η.eq_1,
    magmaCarrier.unit_right]
  simp only [variableSlotIndex_variableSlot]
  congr 1
  funext Δ σ i
  exact (magmaCarrier.unit_is_empty i).elim

theorem multiplicationHead_eq_multiplicationExpression (n : ℕ)
    (args : Expr.Args (magmaSignature ⋈ variableContext n) (variableContext 2)) :
    .ap (magmaCarrier.inl multiplicationSlot) args =
      multiplicationExpression n
        (args (variableSlot 2 ⟨0, by decide⟩))
        (args (variableSlot 2 ⟨1, by decide⟩)) := by
  unfold multiplicationExpression
  congr 1
  funext Δ σ i
  cases σ
  apply multiplicationArgument_cases
    (motive := fun {Δ} i =>
      args i = multiplicationArguments n
        (args (variableSlot 2 ⟨0, by decide⟩))
        (args (variableSlot 2 ⟨1, by decide⟩)) i)
  · simpa using (multiplicationArguments_left n
      (args (variableSlot 2 ⟨0, by decide⟩))
      (args (variableSlot 2 ⟨1, by decide⟩))).symm
  · simpa using (multiplicationArguments_right n
      (args (variableSlot 2 ⟨0, by decide⟩))
      (args (variableSlot 2 ⟨1, by decide⟩))).symm

theorem ofMagmaTerm_toMagmaTermAux (n : ℕ)
    {Γ : magmaCarrier.Arity} {τ : magmaCarrier.Ty}
    (e : Expr (C := magmaCarrier) Γ τ)
    (hΓ : Γ = magmaSignature ⋈ variableContext n) (hτ : τ = ()) :
    ofMagmaTerm n (toMagmaTermAux n e hΓ hτ) = hτ ▸ hΓ ▸ e := by
  induction e with
  | ap x args ih =>
    cases hΓ
    cases hτ
    refine magmaCarrier.coverCasesEq
      (motive := fun x =>
        ofMagmaTerm n (toMagmaTermAux n (.ap x args) rfl rfl) = .ap x args)
      magmaSignature (variableContext n) x ?_ ?_
    · intro y h
      rw [h]
      have hα := signatureSlot_arity y
      cases hα
      rw [signatureSlot_eq y]
      rw [toMagmaTermAux_multiplication, ofMagmaTerm,
        ih (variableSlot 2 ⟨0, by decide⟩) rfl rfl,
        ih (variableSlot 2 ⟨1, by decide⟩) rfl rfl]
      symm
      apply multiplicationHead_eq_multiplicationExpression
    · intro y h
      rw [h]
      rw [toMagmaTermAux_variableHead, ofMagmaTerm]
      symm
      apply variableHead_eq_variableExpression

/-- Translating a ground magma expression to a binary tree and back is the identity. -/
theorem ofMagmaTerm_toMagmaTerm (n : ℕ)
    (e : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    ofMagmaTerm n (toMagmaTerm n e) = e :=
  ofMagmaTerm_toMagmaTermAux n e rfl rfl

/-- The expression substitution induced by a simultaneous magma substitution. -/
def magmaExpressionSubstitution {n m : ℕ}
    (σ : Fin n → MagmaTerm m) :
    Subst (variableContext n) (magmaSignature ⋈ variableContext m) :=
  fun {α} {τ} x => by
    have hα := variableSlot_arity n x
    subst α
    cases τ
    exact ofMagmaTerm m (σ (variableSlotIndex n x))

@[simp] theorem magmaExpressionSubstitution_variableSlot {n m : ℕ}
    (σ : Fin n → MagmaTerm m) (j : Fin n) :
    magmaExpressionSubstitution σ (variableSlot n j) = ofMagmaTerm m (σ j) := by
  unfold magmaExpressionSubstitution
  simp

theorem act_variableExpression {n m : ℕ}
    (σ : Fin n → MagmaTerm m) (j : Fin n) :
    Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
      (variableExpression n j) = ofMagmaTerm m (σ j) := by
  unfold variableExpression
  rw [act_η_prefixed (Γ := magmaSignature) (magmaExpressionSubstitution σ) 1]
  apply magmaExpressionSubstitution_variableSlot

theorem act_multiplicationExpression {n m : ℕ}
    (σ : Fin n → MagmaTerm m)
    (e f : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
      (multiplicationExpression n e f) =
      multiplicationExpression m
        (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
        (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f) := by
  unfold multiplicationExpression
  rw [← magmaCarrier.unit_right
    (magmaSignature ⋈ variableContext n) (magmaCarrier.inl multiplicationSlot)]
  conv_lhs => unfold Subst.act
  simp
  rw [magmaCarrier.unit_right
    (magmaSignature ⋈ variableContext m) (magmaCarrier.inl multiplicationSlot)]
  constructor
  · rfl
  · funext Δ τ i
    apply multiplicationArgument_cases
      (motive := fun {Δ} i =>
        Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) (1 ⋈ Δ)
          (multiplicationArguments n e f i) =
        multiplicationArguments m
          (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
          (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f) i)
    · simpa only [magmaArity_right_unit] using
        (calc
          Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
              (multiplicationArguments n e f (variableSlot 2 ⟨0, by decide⟩)) =
              Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e :=
            congrArg (fun g =>
              Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 g)
              (multiplicationArguments_left n e f)
          _ = multiplicationArguments m
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f)
              (variableSlot 2 ⟨0, by decide⟩) :=
            (multiplicationArguments_left m
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f)).symm)
    · simpa only [magmaArity_right_unit] using
        (calc
          Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
              (multiplicationArguments n e f (variableSlot 2 ⟨1, by decide⟩)) =
              Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f :=
            congrArg (fun g =>
              Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 g)
              (multiplicationArguments_right n e f)
          _ = multiplicationArguments m
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f)
              (variableSlot 2 ⟨1, by decide⟩) :=
            (multiplicationArguments_right m
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e)
              (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 f)).symm)

theorem act_ofMagmaTerm {n m : ℕ} (σ : Fin n → MagmaTerm m) :
    ∀ e : MagmaTerm n,
      Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
        (ofMagmaTerm n e) = ofMagmaTerm m (magmaSubstitution σ e)
  | .variable j => by
    exact act_variableExpression σ j
  | .multiplication e f => by
    rw [ofMagmaTerm, act_multiplicationExpression, magmaSubstitution,
      act_ofMagmaTerm σ e, act_ofMagmaTerm σ f, ofMagmaTerm]

/-- Fixed-prefix syntax substitution agrees with simultaneous tree substitution. -/
theorem toMagmaTerm_act_magmaExpressionSubstitution {n m : ℕ}
    (σ : Fin n → MagmaTerm m)
    (e : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext n) ()) :
    toMagmaTerm m
      (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e) =
      magmaSubstitution σ (toMagmaTerm n e) := by
  calc
    toMagmaTerm m
        (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1 e) =
        toMagmaTerm m
          (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
            (ofMagmaTerm n (toMagmaTerm n e))) := by
          rw [ofMagmaTerm_toMagmaTerm]
    _ = toMagmaTerm m (ofMagmaTerm m (magmaSubstitution σ (toMagmaTerm n e))) := by
          rw [act_ofMagmaTerm]
    _ = magmaSubstitution σ (toMagmaTerm n e) := by
          apply toMagmaTerm_ofMagmaTerm

theorem magmaExpressionSubstitution_identity (n : ℕ) :
    magmaExpressionSubstitution (fun j : Fin n => MagmaTerm.variable j) =
      fun {_} {_} x => Expr.η (magmaCarrier.inr x) := by
  funext α τ x
  have hα := variableSlot_arity n x
  subst α
  cases τ
  unfold magmaExpressionSubstitution
  dsimp
  rw [variableSlot_eq_variableSlotIndex n x]
  simp only [variableSlotIndex_variableSlot]
  rfl

theorem magmaExpressionSubstitution_composition {n m k : ℕ}
    (σ : Fin n → MagmaTerm m) (θ : Fin m → MagmaTerm k) :
    magmaExpressionSubstitution (fun j => magmaSubstitution θ (σ j)) =
      Subst.comp (magmaExpressionSubstitution σ) (magmaExpressionSubstitution θ) := by
  funext α τ x
  have hα := variableSlot_arity n x
  subst α
  cases τ
  have hleft :
      magmaExpressionSubstitution (fun j => magmaSubstitution θ (σ j)) x =
        ofMagmaTerm k (magmaSubstitution θ (σ (variableSlotIndex n x))) := by
    unfold magmaExpressionSubstitution
    dsimp
  have hright :
      Subst.comp (magmaExpressionSubstitution σ) (magmaExpressionSubstitution θ) x =
        Subst.act (magmaExpressionSubstitution θ) (Γ := magmaSignature) 1
          (ofMagmaTerm m (σ (variableSlotIndex n x))) := by
    unfold Subst.comp
    congr 1
  rw [hleft, hright]
  simpa only [magmaArity_right_unit] using
    (act_ofMagmaTerm θ (σ (variableSlotIndex n x))).symm

/-- Simultaneous substitution by variables is the identity. -/
theorem magmaSubstitution_identity (n : ℕ) (e : MagmaTerm n) :
    magmaSubstitution (fun j : Fin n => MagmaTerm.variable j) e = e := by
  calc
    magmaSubstitution (fun j : Fin n => MagmaTerm.variable j) e =
        magmaSubstitution (fun j : Fin n => MagmaTerm.variable j)
          (toMagmaTerm n (ofMagmaTerm n e)) := by
          rw [toMagmaTerm_ofMagmaTerm]
    _ = toMagmaTerm n
          (Subst.act (magmaExpressionSubstitution (fun j : Fin n => MagmaTerm.variable j))
            (Γ := magmaSignature) 1 (ofMagmaTerm n e)) := by
          symm
          apply toMagmaTerm_act_magmaExpressionSubstitution
    _ = toMagmaTerm n (ofMagmaTerm n e) := by
          apply congrArg (toMagmaTerm n)
          rw [magmaExpressionSubstitution_identity]
          apply act_idOfη (Γ := magmaSignature)
          intro β τ x
          rfl
    _ = e := by
          apply toMagmaTerm_ofMagmaTerm

/-- Simultaneous substitutions compose by substituting into their components. -/
theorem magmaSubstitution_composition {n m k : ℕ}
    (σ : Fin n → MagmaTerm m) (θ : Fin m → MagmaTerm k) (e : MagmaTerm n) :
    magmaSubstitution θ (magmaSubstitution σ e) =
      magmaSubstitution (fun j => magmaSubstitution θ (σ j)) e := by
  calc
    magmaSubstitution θ (magmaSubstitution σ e) =
        magmaSubstitution θ
          (toMagmaTerm m
            (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
              (ofMagmaTerm n e))) := by
          congr 1
          calc
            magmaSubstitution σ e =
                magmaSubstitution σ (toMagmaTerm n (ofMagmaTerm n e)) := by
                  rw [toMagmaTerm_ofMagmaTerm]
            _ = toMagmaTerm m
                (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
                  (ofMagmaTerm n e)) := by
                  symm
                  apply toMagmaTerm_act_magmaExpressionSubstitution
    _ = toMagmaTerm k
          (Subst.act (magmaExpressionSubstitution θ) (Γ := magmaSignature) 1
            (Subst.act (magmaExpressionSubstitution σ) (Γ := magmaSignature) 1
              (ofMagmaTerm n e))) := by
          symm
          apply toMagmaTerm_act_magmaExpressionSubstitution
    _ = toMagmaTerm k
          (Subst.act (Subst.comp (magmaExpressionSubstitution σ)
            (magmaExpressionSubstitution θ)) (Γ := magmaSignature) 1 (ofMagmaTerm n e)) := by
          apply congrArg (toMagmaTerm k)
          symm
          apply act_comp
    _ = toMagmaTerm k
          (Subst.act (magmaExpressionSubstitution
            (fun j => magmaSubstitution θ (σ j))) (Γ := magmaSignature) 1
              (ofMagmaTerm n e)) := by
          rw [magmaExpressionSubstitution_composition]
    _ = magmaSubstitution (fun j => magmaSubstitution θ (σ j))
          (toMagmaTerm n (ofMagmaTerm n e)) := by
          apply toMagmaTerm_act_magmaExpressionSubstitution
    _ = magmaSubstitution (fun j => magmaSubstitution θ (σ j)) e := by
          rw [toMagmaTerm_ofMagmaTerm]

def nestedMagmaTerm : MagmaTerm 2 :=
  .multiplication (.multiplication (.variable 0) (.variable 1)) (.variable 0)

def nontrivialMagmaSubstitution : Fin 2 → MagmaTerm 2 :=
  Fin.cases (.multiplication (.variable 0) (.variable 1))
    (fun j => Fin.cases (.variable 0) (fun j => Fin.elim0 j) j)

def substitutedNestedMagmaTerm : MagmaTerm 2 :=
  .multiplication
    (.multiplication (.multiplication (.variable 0) (.variable 1)) (.variable 0))
    (.multiplication (.variable 0) (.variable 1))

example (e : Expr (C := magmaCarrier) (magmaSignature ⋈ variableContext 0) ()) : False :=
  isEmptyElim (toMagmaTerm 0 e)

example :
    toMagmaTerm 1 (ofMagmaTerm 1 (.variable 0)) = (.variable 0 : MagmaTerm 1) :=
  toMagmaTerm_ofMagmaTerm 1 (.variable 0)

example : toMagmaTerm 2 (ofMagmaTerm 2 nestedMagmaTerm) = nestedMagmaTerm :=
  toMagmaTerm_ofMagmaTerm 2 nestedMagmaTerm

example : magmaSubstitution nontrivialMagmaSubstitution nestedMagmaTerm =
    substitutedNestedMagmaTerm := rfl

example :
    toMagmaTerm 2
      (Subst.act (magmaExpressionSubstitution nontrivialMagmaSubstitution)
        (Γ := magmaSignature) 1 (ofMagmaTerm 2 nestedMagmaTerm)) =
      substitutedNestedMagmaTerm := by
  rw [toMagmaTerm_act_magmaExpressionSubstitution]
  rw [toMagmaTerm_ofMagmaTerm]
  rfl

end Magmas
