import HigherRankSyntax.MonadLaws

/-!
# Boundaries

A boundary over `Ω` is either `sort`, declaring its slot to be a sort, or
`of S` for an expression `S` over `Ω`, declaring its slot to be an object of the
sort `S`.

Renaming and substitution act on a boundary by acting on that expression, and
instantiating a boundary written over a declaration's arity by arguments for
that arity is the substitution action at the unit depth.
-/

variable {A : Type} {C : Carrier A}

/-- The boundary of a slot over `Ω`. -/
inductive Boundary (Ω : C.Arity) : Type where
  /-- The slot is a sort. -/
  | sort : Boundary Ω
  /-- The slot is an object of the sort denoted by the expression. -/
  | of : Expr Ω → Boundary Ω

namespace Boundary

/-- Action of a renaming on a boundary. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Boundary Γ → Boundary Δ
  | .sort => .sort
  | .of S => .of (⟦ ρ ⟧ʳ S)

@[simp] theorem rename_sort {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
  rename ρ .sort = .sort := rfl

@[simp] theorem rename_of {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (S : Expr Γ) :
  rename ρ (.of S) = .of (⟦ ρ ⟧ʳ S) := rfl

/-- Action of a substitution on a boundary at depth `Φ`. -/
def act {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
    Boundary (Γ ⋈ Δ ⋈ Φ) → Boundary (Γ ⋈ Ξ ⋈ Φ)
  | .sort => .sort
  | .of S => .of (σ.act Φ S)

@[simp] theorem act_sort {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
  act σ Φ .sort = .sort := rfl

@[simp] theorem act_of {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    (S : Expr (Γ ⋈ Δ ⋈ Φ)) :
  act σ Φ (.of S) = .of (σ.act Φ S) := rfl

/-- A boundary written over a declaration's arity, instantiated by arguments for
that arity. -/
def instantiate {Γ Δ : C.Arity} (σ : Subst Δ Γ) :
    Boundary (Γ ⋈ Δ) → Boundary Γ :=
  act (Ξ := 1) σ 1

/-! ### Functoriality -/

theorem rename_id {Γ : C.Arity} (β : Boundary Γ) :
  rename (𝟙ʳ Γ) β = β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Boundary.of (Renaming.act_id S)

theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (θ : Δ →ʳ Ξ)
    (β : Boundary Γ) :
  rename (θ ∘ʳ ρ) β = rename θ (rename ρ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Boundary.of (Renaming.act_comp ρ θ S)

/-- The identity substitution acts as the identity. -/
theorem act_id (Γ Φ : C.Arity) (β : Boundary (Γ ⋈ Φ)) :
  act (Subst.id Γ) (Γ := 1) Φ β = β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Boundary.of (_root_.act_id Γ Φ S)

/-- Action by a composite factors. -/
theorem act_comp {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ))
    (Φ : C.Arity) (β : Boundary (Γ ⋈ Δ ⋈ Φ)) :
  act (Subst.comp σ θ) Φ β = act θ Φ (act σ Φ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Boundary.of (_root_.act_comp σ θ Φ S)

end Boundary
