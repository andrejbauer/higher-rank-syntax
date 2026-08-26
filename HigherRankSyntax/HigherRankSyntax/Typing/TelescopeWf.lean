import HigherRankSyntax.Typing.Judgement

/-!
# Well-formed telescopes, and equality of telescopes

Both are recursions on nesting, well-founded by `C.subWf`.  They use the
judgements but are not mutual with them: the premises at a slot are stated over
the ambient built from the entries strictly preceding it and the entries it
binds, never from the slot itself.
-/

variable {A : Type} {C : Carrier A}

/-- A telescope over an ambient is well formed. -/
def Wf_t : (Ξ : Ambient C) → dTel Ξ.arity → Prop
  | Ξ, Θ => ∀ {Λ : C.Arity} (z : Θ.arity ∋ Λ),
      Wf_t (Ξ.extend (Θ.before z)) (Θ.binding z) ∧
      (match Θ.boundary z with
        | .sort => True
        | .of S =>
            Wf_e ((Ξ.extend (Θ.before z)).extend (Θ.binding z)) S ∧
            Eq_bd ((Ξ.extend (Θ.before z)).extend (Θ.binding z))
              (((Ξ.extend (Θ.before z)).extend (Θ.binding z)).boundaryOf S) .sort
        | .eq l r =>
            Wf_e ((Ξ.extend (Θ.before z)).extend (Θ.binding z)) l ∧
            Wf_e ((Ξ.extend (Θ.before z)).extend (Θ.binding z)) r ∧
            Eq_bd ((Ξ.extend (Θ.before z)).extend (Θ.binding z))
              (((Ξ.extend (Θ.before z)).extend (Θ.binding z)).boundaryOf l)
              (((Ξ.extend (Θ.before z)).extend (Θ.binding z)).boundaryOf r))
termination_by Ξ Θ => Θ.arity
decreasing_by exact ⟨z⟩

/-- Equality of two decorations of a common arity, over an ambient. -/
def Eq_d : (Ξ : Ambient C) → (Δ : C.Arity) →
    Decoration Ξ.arity Δ → Decoration Ξ.arity Δ → Prop
  | Ξ, Δ, D, D' => ∀ {Λ : C.Arity} (z : Δ ∋ Λ),
      Eq_d (Ξ.extend (dTel.before ⟨Δ, D⟩ z)) Λ (D.nested z) (D'.nested z) ∧
      Eq_bd ((Ξ.extend (dTel.before ⟨Δ, D⟩ z)).extend (dTel.binding ⟨Δ, D⟩ z))
        (D.boundary z) (D'.boundary z)
termination_by Ξ Δ _ _ => Δ
decreasing_by exact ⟨z⟩

/-- Equality of telescopes: the same arity, strictly, and equal decorations. -/
def Eq_t {Ξ : Ambient C} (Θ Θ' : dTel Ξ.arity) : Prop :=
  ∃ h : Θ.arity = Θ'.arity,
    Eq_d Ξ Θ.arity Θ.decoration (Decoration.castArity h.symm Θ'.decoration)

/-- Well-formedness restricts to the entries preceding a slot. -/
theorem Wf_t.before {Ξ : Ambient C} {Θ : dTel Ξ.arity} {Λ : C.Arity}
    (h : Wf_t Ξ Θ) (z : Θ.arity ∋ Λ) : Wf_t Ξ (Θ.before z) := sorry

@[inherit_doc Wf_t] notation:50 Ξ " ⊢ " Θ:51 => Wf_t Ξ Θ
@[inherit_doc Eq_t] notation:50 Ξ " ⊢ " Θ:51 " ≈ " Θ':51 => Eq_t (Ξ := Ξ) Θ Θ'

/-- An ambient is well formed when it is well formed over the empty ambient. -/
def Ambient.Wf (Ξ : Ambient C) : Prop :=
  Wf_t (dTel.empty 1) Ξ

section SmokeTests

variable (Ξ : Ambient C) (Θ Θ' : dTel Ξ.arity) (e e' : Expr Ξ.arity)

example : Prop := Ξ ⊢ Θ
example : Prop := Ξ ⊢ Θ ≈ Θ'
example : Prop := Ξ ⊢ e
example : Prop := Ξ ⊢ e ≈ e'

end SmokeTests
