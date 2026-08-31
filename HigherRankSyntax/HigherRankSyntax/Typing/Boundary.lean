import HigherRankSyntax.MonadLaws

/-!
# Boundaries

A boundary over `Ω` is `sort`, declaring its slot to be a sort; `of S` for an
expression `S` over `Ω`, declaring its slot to be an object of the sort `S`; or
`eq l r` for expressions `l`, `r` over `Ω`, declaring its slot to assert the
equation between them.

Renaming and substitution act on a boundary by acting on those expressions, and
instantiating a boundary written over a declaration's arity by arguments for
that arity is the substitution action at the unit depth.  Both actions preserve
the constructor, so `isEq` is invariant under them.
-/

/-- The boundary of a slot over `Ω`. -/
inductive Bd (Ω : C.Arity) : Type where
  /-- The slot is a sort. -/
  | sort : Bd Ω
  /-- The slot is an object of the sort denoted by the expression. -/
  | of : Expr Ω → Bd Ω
  /-- The slot asserts the equation between the two expressions. -/
  | eq : Expr Ω → Expr Ω → Bd Ω

namespace Bd

/-- Action of a renaming on a boundary. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Bd Γ → Bd Δ
  | .sort => .sort
  | .of S => .of (⟦ ρ ⟧ʳ S)
  | .eq l r => .eq (⟦ ρ ⟧ʳ l) (⟦ ρ ⟧ʳ r)

@[simp] theorem rename_sort {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
  rename ρ .sort = .sort := rfl

@[simp] theorem rename_of {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (S : Expr Γ) :
  rename ρ (.of S) = .of (⟦ ρ ⟧ʳ S) := rfl

@[simp] theorem rename_eq {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (l r : Expr Γ) :
  rename ρ (.eq l r) = .eq (⟦ ρ ⟧ʳ l) (⟦ ρ ⟧ʳ r) := rfl

/-- Action of a substitution on a boundary at depth `Φ`. -/
def act {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
    Bd (Γ ⋈ Δ ⋈ Φ) → Bd (Γ ⋈ Ξ ⋈ Φ)
  | .sort => .sort
  | .of S => .of (σ.act Φ S)
  | .eq l r => .eq (σ.act Φ l) (σ.act Φ r)

@[simp] theorem act_sort {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
  act σ Φ .sort = .sort := rfl

@[simp] theorem act_of {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    (S : Expr (Γ ⋈ Δ ⋈ Φ)) :
  act σ Φ (.of S) = .of (σ.act Φ S) := rfl

@[simp] theorem act_eq {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    (l r : Expr (Γ ⋈ Δ ⋈ Φ)) :
  act σ Φ (.eq l r) = .eq (σ.act Φ l) (σ.act Φ r) := rfl

/-- A boundary written over a declaration's arity, instantiated by arguments for
that arity. -/
def instantiate {Γ Δ : C.Arity} (σ : Subst Δ Γ) :
    Bd (Γ ⋈ Δ) → Bd Γ :=
  act (Ξ := 1) σ 1

/-- The boundary asserts an equation. -/
def isEq {Ω : C.Arity} : Bd Ω → Prop
  | .eq _ _ => True
  | _ => False

@[simp] theorem isEq_sort {Ω : C.Arity} : ¬ (Bd.sort : Bd Ω).isEq := id

@[simp] theorem isEq_of {Ω : C.Arity} (S : Expr Ω) : ¬ (Bd.of S).isEq := id

@[simp] theorem isEq_eq {Ω : C.Arity} (l r : Expr Ω) : (Bd.eq l r).isEq := trivial

/-- Instantiating a block under a suffix commutes with a renaming of the base. -/
theorem act_rename {Γ Δ Θ Φ : C.Arity} (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ)
    (β : Bd (Γ ⋈ Θ ⋈ Φ)) :
  act (Ξ := 1) (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) Φ (rename ((ρ ⇑ʳ Θ) ⇑ʳ Φ) β)
    = rename (ρ ⇑ʳ Φ) (act (Ξ := 1) σ Φ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_rename_suffix Γ Δ Θ ρ σ Φ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_rename_suffix Γ Δ Θ ρ σ Φ l)
        (_root_.act_rename_suffix Γ Δ Θ ρ σ Φ r)

/-- A square of substitutions and renamings, on boundaries. -/
theorem act_square {Γ Γ' Δ Δ' : C.Arity} (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ')
    (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x))
    (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
    act (Γ := 1) κ Φ (rename (ρ ⇑ʳ Φ) β) = rename (ρ' ⇑ʳ Φ) (act (Γ := 1) κ' Φ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_square ρ ρ' κ κ' h Φ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_square ρ ρ' κ κ' h Φ l) (_root_.act_square ρ ρ' κ κ' h Φ r)

/-- Acting by `Subst.copair (Subst.id Δ) σ` is acting by `σ` below the fixed
prefix `Δ`. -/
theorem act_copair_prefix {Δ Ω : C.Arity} (σ : Subst Ω Δ) (Φ : C.Arity)
    (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) :
    act (Γ := 1) (Δ := Δ ⋈ Ω) (Ξ := Δ) (Subst.copair (Subst.id Δ) σ) Φ β
      = act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_copair_prefix σ Φ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_copair_prefix σ Φ l)
        (_root_.act_copair_prefix σ Φ r)

/-- Acting by the lift of `Subst.copair (Subst.id Δ) σ` past `Φ` is acting by
`σ` below the prefix `Δ` at depth `Φ ⋈ Ψ`. -/
theorem act_lift_copair {Δ Ω : C.Arity} (σ : Subst Ω Δ) (Φ Ψ : C.Arity)
    (β : Bd (((Δ ⋈ Ω) ⋈ Φ) ⋈ Ψ)) :
    act (Γ := 1) (Δ := (Δ ⋈ Ω) ⋈ Φ) (Ξ := Δ ⋈ Φ)
        (Subst.lift (Subst.copair (Subst.id Δ) σ) Φ) Ψ β
      = act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ (Φ ⋈ Ψ) β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Subst.act_lift_copair σ Φ Ψ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (Subst.act_lift_copair σ Φ Ψ l)
        (Subst.act_lift_copair σ Φ Ψ r)

/-- Acting by a lift with no further depth is acting at the lifted depth. -/
theorem act_lift_depth {Γ Δ Φ : C.Arity} (σ : Subst Γ Δ) (β : Bd (Γ ⋈ Φ)) :
    act (Γ := 1) (Δ := Γ ⋈ Φ) (Ξ := Δ ⋈ Φ) (Subst.lift σ Φ) 1 β
      = act (Γ := 1) (Δ := Γ) (Ξ := Δ) σ Φ β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Subst.act_lift_depth σ S)
  | eq l r => exact congrArg₂ Bd.eq (Subst.act_lift_depth σ l) (Subst.act_lift_depth σ r)

/-- Acting by a lifted substitution and then by the acted fillers is acting by
the fillers and then by the substitution. -/
theorem act_lift_fillers {Γ Γ' Χ Λ : C.Arity} (s : Subst Γ Γ') (τ : Subst Χ Γ)
    (β : Bd (Γ ⋈ Χ ⋈ Λ)) :
    act (Γ := Γ') (Δ := Χ) (Ξ := 1)
        (fun ⦃Λ'⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ' (τ i)) Λ
        (act (Γ := 1) (Δ := Γ ⋈ Χ) (Ξ := Γ' ⋈ Χ) (Subst.lift s Χ) Λ β)
      = act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ
          (act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Subst.act_lift_fillers s τ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (Subst.act_lift_fillers s τ l) (Subst.act_lift_fillers s τ r)

/-- Renaming preserves the constructor. -/
@[simp] theorem isEq_rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (β : Bd Γ) :
  (rename ρ β).isEq ↔ β.isEq := by
  cases β <;> rfl

/-- Substitution preserves the constructor. -/
@[simp] theorem isEq_act {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    (β : Bd (Γ ⋈ Δ ⋈ Φ)) :
  (act σ Φ β).isEq ↔ β.isEq := by
  cases β <;> rfl

/-- Instantiating the fresh block of a weakened boundary by the slots it came from
returns the boundary. -/
theorem instantiate_rename_inl (Γ α : C.Arity) (β : Bd (Γ ⋈ α)) :
  instantiate (Subst.instId Γ α)
      ((rename (Renaming.inl Γ α ⇑ʳ α) β : Bd ((Γ ⋈ α) ⋈ α))) = β := by
  have key : ∀ e : Expr (Γ ⋈ α),
      Subst.act (Γ := Γ ⋈ α) (Δ := α) (Ξ := 1) (Subst.instId Γ α) 1
        (⟦ Renaming.inl Γ α ⇑ʳ α ⟧ʳ e) = e := by
    intro e
    have := act_instId_weaken Γ α (Φ := 1) e
    rwa [Renaming.extend_unit] at this
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (key S)
  | eq l r => exact congrArg₂ Bd.eq (key l) (key r)

/-- Instantiating commutes with weakening on the right, when the arguments are
weakened as well. -/
theorem instantiate_weaken (Γ Δ Θ : C.Arity) (σ : Subst Θ Γ) (β : Bd (Γ ⋈ Θ)) :
    instantiate (fun ⦃Λ⦄ i => ⟦ Renaming.inl Γ Δ ⇑ʳ Λ ⟧ʳ (σ i))
        ((rename (Renaming.inl Γ Δ ⇑ʳ Θ) β : Bd ((Γ ⋈ Δ) ⋈ Θ)))
      = rename (Renaming.inl Γ Δ) (instantiate σ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_rename Γ (Γ ⋈ Δ) Θ (Renaming.inl Γ Δ) σ S)
  | eq l r => exact congrArg₂ Bd.eq (_root_.act_rename Γ (Γ ⋈ Δ) Θ (Renaming.inl Γ Δ) σ l) (_root_.act_rename Γ (Γ ⋈ Δ) Θ (Renaming.inl Γ Δ) σ r)

/-- Filling the fresh block of a weakened boundary by its own slots returns it. -/
theorem act_instId_weaken (Γ α Φ : C.Arity) (β : Bd (Γ ⋈ α ⋈ Φ)) :
  act (Ξ := 1) (Subst.instId Γ α) Φ (rename ((Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ) β) = β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_instId_weaken Γ α S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_instId_weaken Γ α l) (_root_.act_instId_weaken Γ α r)

/-- Substituting into a renamed boundary whose slots the substitution merely
relabels is that relabelling. -/
theorem act_rename_cancel {Γ Δ' Γ' : C.Arity} (ρ : Γ →ʳ Δ') (ρ' : Γ →ʳ Γ')
    (κ : Subst Δ' Γ') (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = Expr.η (ρ' x))
    (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
    act (Γ := 1) κ Φ (rename (ρ ⇑ʳ Φ) β) = rename (ρ' ⇑ʳ Φ) β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_rename_cancel ρ ρ' κ h Φ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_rename_cancel ρ ρ' κ h Φ l)
        (_root_.act_rename_cancel ρ ρ' κ h Φ r)

/-! ### Functoriality -/

theorem rename_id {Γ : C.Arity} (β : Bd Γ) :
  rename (𝟙ʳ Γ) β = β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Renaming.act_id S)
  | eq l r => exact congrArg₂ Bd.eq (Renaming.act_id l) (Renaming.act_id r)

theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (θ : Δ →ʳ Ξ)
    (β : Bd Γ) :
  rename (θ ∘ʳ ρ) β = rename θ (rename ρ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Renaming.act_comp ρ θ S)
  | eq l r => exact congrArg₂ Bd.eq (Renaming.act_comp ρ θ l) (Renaming.act_comp ρ θ r)

/-- The identity substitution acts as the identity. -/
theorem act_id (Γ Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
  act (Subst.id Γ) (Γ := 1) Φ β = β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_id Γ Φ S)
  | eq l r => exact congrArg₂ Bd.eq (_root_.act_id Γ Φ l) (_root_.act_id Γ Φ r)

/-- Action by a composite factors. -/
theorem act_comp {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ))
    (Φ : C.Arity) (β : Bd (Γ ⋈ Δ ⋈ Φ)) :
  act (Subst.comp σ θ) Φ β = act θ Φ (act σ Φ β) := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (_root_.act_comp σ θ Φ S)
  | eq l r =>
      exact congrArg₂ Bd.eq (_root_.act_comp σ θ Φ l) (_root_.act_comp σ θ Φ r)

end Bd
