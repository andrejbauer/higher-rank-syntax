import HigherRankSyntax.Typing.DecoratedTelescopeMonoid
import HigherRankSyntax.Typing.ExprBoundary

/-!
# The judgements

Four relations over an arbitrary ambient, well formed or not, defined by one
simultaneous induction: an expression is well formed, two expressions are equal,
two boundaries are equal, and a substitution fills a telescope.
-/

variable {A : Type} {C : Carrier A}

mutual

/-- An expression over an ambient is well formed. -/
inductive Wf_e : (Ξ : Ambient C) → Expr Ξ.arity → Prop where
  | ap {Ξ : Ambient C} {α : C.Arity} (x : Ξ.arity ∋ α) (args : Subst α Ξ.arity)
      (head : ¬ (Ξ.boundary x).isEq)
      (fill : Wf_s Ξ ((Ξ.binding x).rename (Ξ.inclusion x)) args) :
      Wf_e Ξ (.ap x args)

/-- Two expressions over an ambient are equal. -/
inductive Eq_e : (Ξ : Ambient C) → Expr Ξ.arity → Expr Ξ.arity → Prop where
  | refl {Ξ : Ambient C} {e : Expr Ξ.arity} (h : Wf_e Ξ e) : Eq_e Ξ e e
  | symm {Ξ : Ambient C} {e e' : Expr Ξ.arity} (h : Eq_e Ξ e e') : Eq_e Ξ e' e
  | trans {Ξ : Ambient C} {e e' e'' : Expr Ξ.arity}
      (h : Eq_e Ξ e e') (h' : Eq_e Ξ e' e'') : Eq_e Ξ e e''
  | hyp {Ξ : Ambient C} {Λ : C.Arity} (q : Ξ.arity ∋ Λ)
      (l r : Expr ((Ξ.before q).arity ⋈ Λ))
      (decl : Ξ.boundary q = .eq l r)
      (hl : Wf_e (Ξ.extend ((Ξ.binding q).rename (Ξ.inclusion q)))
        (⟦ Ξ.inclusion q ⇑ʳ Λ ⟧ʳ l))
      (hr : Wf_e (Ξ.extend ((Ξ.binding q).rename (Ξ.inclusion q)))
        (⟦ Ξ.inclusion q ⇑ʳ Λ ⟧ʳ r)) :
      Eq_e (Ξ.extend ((Ξ.binding q).rename (Ξ.inclusion q)))
        (⟦ Ξ.inclusion q ⇑ʳ Λ ⟧ʳ l) (⟦ Ξ.inclusion q ⇑ʳ Λ ⟧ʳ r)
  | subst {Ψ Ξ : Ambient C} {e e' : Expr Ψ.arity}
      (σ θ : Subst Ψ.arity Ξ.arity)
      (hσ : Wf_s Ξ (Ψ.weaken Ξ.arity) σ)
      (hθ : Wf_s Ξ (Ψ.weaken Ξ.arity) θ)
      (agree : ∀ {Λ : C.Arity} (z : Ψ.arity ∋ Λ),
          ¬ (Bd.act (Ξ := 1) (σ ↾ z) Λ ((Ψ.weaken Ξ.arity).boundary z)).isEq →
          Eq_e (Ξ.extend (dTel.instantiate (σ ↾ z) ((Ψ.weaken Ξ.arity).binding z)))
            (σ z) (θ z))
      (h : Eq_e Ψ e e') :
      Eq_e Ξ
        (Subst.act (Γ := Ξ.arity) (Ξ := 1) σ 1
          (⟦ Renaming.inr Ξ.arity Ψ.arity ⟧ʳ e))
        (Subst.act (Γ := Ξ.arity) (Ξ := 1) θ 1
          (⟦ Renaming.inr Ξ.arity Ψ.arity ⟧ʳ e'))

/-- Two boundaries over an ambient are equal. -/
inductive Eq_bd : (Ξ : Ambient C) → Bd Ξ.arity → Bd Ξ.arity → Prop where
  | sort {Ξ : Ambient C} : Eq_bd Ξ .sort .sort
  | of {Ξ : Ambient C} {S S' : Expr Ξ.arity} (h : Eq_e Ξ S S') :
      Eq_bd Ξ (.of S) (.of S')
  | eq {Ξ : Ambient C} {l r l' r' : Expr Ξ.arity}
      (hl : Eq_e Ξ l l') (hr : Eq_e Ξ r r') : Eq_bd Ξ (.eq l r) (.eq l' r')

/-- A substitution fills a telescope over an ambient. -/
inductive Wf_s : (Ξ : Ambient C) → (Θ : dTel Ξ.arity) → Subst Θ.arity Ξ.arity → Prop where
  | mk {Ξ : Ambient C} {Θ : dTel Ξ.arity} {σ : Subst Θ.arity Ξ.arity}
      (equation : ∀ {Λ : C.Arity} (z : Θ.arity ∋ Λ) (l r : Expr (Ξ.arity ⋈ Λ)),
          Bd.act (Ξ := 1) (σ ↾ z) Λ (Θ.boundary z) = .eq l r →
          Eq_e (Ξ.extend (dTel.instantiate (σ ↾ z) (Θ.binding z))) l r)
      (filler : ∀ {Λ : C.Arity} (z : Θ.arity ∋ Λ),
          ¬ (Bd.act (Ξ := 1) (σ ↾ z) Λ (Θ.boundary z)).isEq →
          Wf_e (Ξ.extend (dTel.instantiate (σ ↾ z) (Θ.binding z))) (σ z))
      (declared : ∀ {Λ : C.Arity} (z : Θ.arity ∋ Λ),
          ¬ (Bd.act (Ξ := 1) (σ ↾ z) Λ (Θ.boundary z)).isEq →
          Eq_bd (Ξ.extend (dTel.instantiate (σ ↾ z) (Θ.binding z)))
            ((Ξ.extend (dTel.instantiate (σ ↾ z) (Θ.binding z))).boundaryOf (σ z))
            (Bd.act (Ξ := 1) (σ ↾ z) Λ (Θ.boundary z))) :
      Wf_s Ξ Θ σ

end

/-! ### Notation

One turnstile, overloaded on what stands to the right of it: an expression, a
substitution, or a telescope.  The arguments parse above `≈` so that
`Ξ ⊢ e ≈ e'` is not read as `Ξ ⊢ (e ≈ e')`. -/

@[inherit_doc Wf_e] notation:50 Ξ " ⊢ " e:51 => Wf_e Ξ e
@[inherit_doc Eq_e] notation:50 Ξ " ⊢ " e:51 " ≈ " e':51 => Eq_e Ξ e e'
@[inherit_doc Eq_bd] notation:50 Ξ " ⊢ " β:51 " ≈ " β':51 => Eq_bd Ξ β β'
@[inherit_doc Wf_s] notation:50 Ξ " ⊢ " σ:51 " : " Θ:51 => Wf_s Ξ Θ σ

/-- An expression is well formed and its computed boundary is equal to the given
one. -/
notation:50 Ξ " ⊢ " e:51 " : " β:51 =>
  And (Wf_e Ξ e) (Eq_bd Ξ (dTel.boundaryOf Ξ e) β)

section SmokeTests

variable (Ξ : Ambient C) (e e' : Expr Ξ.arity) (β β' : Bd Ξ.arity)
  (Θ : dTel Ξ.arity) (σ : Subst Θ.arity Ξ.arity)

example : Prop := Ξ ⊢ e
example : Prop := Ξ ⊢ e ≈ e'
example : Prop := Ξ ⊢ β ≈ β'
example : Prop := Ξ ⊢ σ : Θ
example : Prop := Ξ ⊢ e : β

end SmokeTests
