import HigherRankSyntax.SyntaxMonad

/-!
# Syntax with a fixed prefix as a relative monad

`PrefixedSyntaxMonad C S` keeps the arity `S` fixed while substituting the
remaining slots.  Its object map is
`Γ ↦ (α, τ) ↦ Expr (S ⋈ Γ ⋈ α) τ`.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A}

/-- **`act_η_prefixed`** — acting at a fixed prefix on an η-expanded domain
slot applies the substitution. -/
theorem act_η_prefixed
    {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Θ : C.Arity) {τ : C.Ty} (x : Δ ∋[τ] Θ) :
  σ.act (Γ := Γ) Θ (Expr.η (C.inr x)) = σ x
  := by
  rw [Expr.η.eq_1]
  trans
  · apply act_middle
  · calc
      _ = Subst.act (Subst.instId (Γ ⋈ Ξ) Θ) 1 (σ x) := by
            congr 1
            funext Ω υ i
            apply act_η_right
      _ = σ x := by apply act_inst_id

/-- The relative monad of expressions with the prefix `S` left unchanged by
Kleisli extension. -/
def PrefixedSyntaxMonad (C : Carrier A) (S : C.Arity) : RelativeMonad (J C) where
  map Γ := ⟨fun α τ => Expr (S ⋈ Γ ⋈ α) τ⟩

  η Γ _ _ x := Expr.η (C.inr x)

  lift {Γ Δ} f α _ e :=
    Subst.act f (Γ := S) α e

  unit_right := by
    intro Γ
    funext α τ e
    apply act_idOfη (Γ := S) (fun ⦃β⦄ ⦃υ⦄ z => Expr.η (C.inr z))
    · intro β υ z
      rfl

  unit_left := by
    intro Γ Δ f
    funext α τ x
    symm
    apply act_η_prefixed (Γ := S) f

  comp_lift := by
    intro Γ Δ Ξ f g
    funext α τ e
    apply act_comp f g
