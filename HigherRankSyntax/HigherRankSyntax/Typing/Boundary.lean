import HigherRankSyntax.MonadLaws

/-!
# Boundaries

A boundary over `Ω` is `sort`, declaring its slot to be a sort; `of S` for an
expression `S` over `Ω`, declaring its slot to be an object of the sort `S`; or
`eq l r` for expressions `l`, `r` over `Ω`, declaring its slot to assert the
equation between them.

`rename` and `act` rename and substitute in the expressions of a boundary;
`instantiate σ` fills the block `Δ` of a boundary over `Γ ⋈ Δ` by
`σ : Subst Δ Γ`, as the action at depth `1`.  Both actions preserve the
constructor, so `isEq` is invariant under them.
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

/-- Action of a substitution on a boundary at depth `Φ`. -/
def act {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
    Bd (Γ ⋈ Δ ⋈ Φ) → Bd (Γ ⋈ Ξ ⋈ Φ)
  | .sort => .sort
  | .of S => .of (σ.act Φ S)
  | .eq l r => .eq (σ.act Φ l) (σ.act Φ r)

/-- Instantiate the block `Δ` of a boundary over `Γ ⋈ Δ` by `σ : Subst Δ Γ`. -/
def instantiate {Γ Δ : C.Arity} (σ : Subst Δ Γ) :
    Bd (Γ ⋈ Δ) → Bd Γ :=
  act (Ξ := 1) σ 1

/-- The boundary is of the form `eq l r`. -/
def isEq {Ω : C.Arity} : Bd Ω → Prop
  | .eq _ _ => True
  | _ => False

/-- Filling the block `Θ` by `σ` at depth `Φ` commutes with renaming the base `Γ`
along `ρ`, when the fillers of `σ` are renamed along `ρ` as well. -/
theorem act_rename
    {Γ Δ Θ Φ : C.Arity}
    (ρ : Γ →ʳ Δ) (σ : Subst Θ Γ) (β : Bd (Γ ⋈ Θ ⋈ Φ)) :
  act (Ξ := 1) (fun ⦃Λ⦄ i => ⟦ ρ ⇑ʳ Λ ⟧ʳ (σ i)) Φ (rename ((ρ ⇑ʳ Θ) ⇑ʳ Φ) β)
    = rename (ρ ⇑ʳ Φ) (act (Ξ := 1) σ Φ β)
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply act_rename_suffix
  | eq l r => apply congrArg₂ eq <;> apply act_rename_suffix

/-- If `κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x)` for every slot `x : Γ ∋ α`, then acting by
`κ` at depth `Φ` after renaming along `ρ ⇑ʳ Φ` is renaming along `ρ' ⇑ʳ Φ` after
acting by `κ'`. -/
theorem act_square
    {Γ Γ' Δ Δ' : C.Arity}
    (ρ : Γ →ʳ Γ') (ρ' : Δ →ʳ Δ') (κ : Subst Γ' Δ') (κ' : Subst Γ Δ)
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = ⟦ ρ' ⇑ʳ α ⟧ʳ (κ' x))
    (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
  act (Γ := 1) κ Φ (rename (ρ ⇑ʳ Φ) β) = rename (ρ' ⇑ʳ Φ) (act (Γ := 1) κ' Φ β)
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_square ρ ρ' κ κ' h
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_square ρ ρ' κ κ' h

/-- Acting by `Subst.copair (Subst.id Δ) σ` is acting by `σ` below the fixed
prefix `Δ`. -/
theorem act_copair_prefix
    {Δ Ω : C.Arity}
    (σ : Subst Ω Δ) (Φ : C.Arity) (β : Bd ((Δ ⋈ Ω) ⋈ Φ)) :
  act (Γ := 1) (Δ := Δ ⋈ Ω) (Ξ := Δ) (Subst.copair (Subst.id Δ) σ) Φ β
    = act (Γ := Δ) (Δ := Ω) (Ξ := 1) σ Φ β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_copair_prefix
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_copair_prefix

/-- Acting by `Subst.ofRenaming ρ` at depth `Φ` is renaming by `ρ ⇑ʳ Φ`. -/
theorem act_ofRenaming {Γ Δ Φ : C.Arity} (ρ : Γ →ʳ Δ) (β : Bd (Γ ⋈ Φ)) :
  act (Γ := 1) (Subst.ofRenaming ρ) Φ β = rename (ρ ⇑ʳ Φ) β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_ofRenaming
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_ofRenaming

/-- Acting by `Subst.lift σ Φ` at depth `Ψ` is acting by `σ` at depth `Φ ⋈ Ψ`. -/
theorem act_lift
    {Γ Δ : C.Arity}
    (σ : Subst Γ Δ) (Φ Ψ : C.Arity) (β : Bd ((Γ ⋈ Φ) ⋈ Ψ)) :
  act (Γ := 1) (Δ := Γ ⋈ Φ) (Ξ := Δ ⋈ Φ) (Subst.lift σ Φ) Ψ β
    = act (Γ := 1) (Δ := Γ) (Ξ := Δ) σ (Φ ⋈ Ψ) β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      exact Subst.act_lift σ Φ Ψ S
  | eq l r => apply congrArg₂ eq <;> exact Subst.act_lift σ Φ Ψ _

/-- Acting by `Subst.lift σ Φ` at depth `1` is acting by `σ` at depth `Φ`. -/
theorem act_lift_depth {Γ Δ Φ : C.Arity} (σ : Subst Γ Δ) (β : Bd (Γ ⋈ Φ)) :
  act (Γ := 1) (Δ := Γ ⋈ Φ) (Ξ := Δ ⋈ Φ) (Subst.lift σ Φ) 1 β
    = act (Γ := 1) (Δ := Γ) (Ξ := Δ) σ Φ β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply Subst.act_lift_depth
  | eq l r => apply congrArg₂ eq <;> apply Subst.act_lift_depth

/-- Acting by `Subst.lift s Χ` and then filling `Χ` by the fillers of `τ` acted on
by `s` is filling `Χ` by `τ` and then acting by `s`. -/
theorem act_lift_fillers
    {Γ Γ' Χ Λ : C.Arity}
    (s : Subst Γ Γ') (τ : Subst Χ Γ) (β : Bd (Γ ⋈ Χ ⋈ Λ)) :
  act (Γ := Γ') (Δ := Χ) (Ξ := 1)
      (fun ⦃Λ'⦄ i => Subst.act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ' (τ i)) Λ
      (act (Γ := 1) (Δ := Γ ⋈ Χ) (Ξ := Γ' ⋈ Χ) (Subst.lift s Χ) Λ β)
    = act (Γ := 1) (Δ := Γ) (Ξ := Γ') s Λ (act (Γ := Γ) (Δ := Χ) (Ξ := 1) τ Λ β)
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply Subst.act_lift_fillers
  | eq l r => apply congrArg₂ eq <;> apply Subst.act_lift_fillers

/-- A renamed boundary is an equation iff the original is. -/
@[simp]
theorem isEq_rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (β : Bd Γ) :
  (rename ρ β).isEq ↔ β.isEq
  := by
  cases β <;> rfl

/-- A boundary acted on by a substitution is an equation iff the original is. -/
@[simp]
theorem isEq_act
    {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) (β : Bd (Γ ⋈ Δ ⋈ Φ)) :
  (act σ Φ β).isEq ↔ β.isEq
  := by
  cases β <;> rfl

/-- Renaming along `(Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ` and then filling the second block
`α` by `Subst.instId Γ α` returns the boundary. -/
theorem act_instId_weaken (Γ α Φ : C.Arity) (β : Bd (Γ ⋈ α ⋈ Φ)) :
  act (Ξ := 1) (Subst.instId Γ α) Φ (rename ((Renaming.inl Γ α ⇑ʳ α) ⇑ʳ Φ) β) = β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_instId_weaken
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_instId_weaken

/-- Renaming along `Renaming.inl Γ α ⇑ʳ α` and then instantiating the second block
`α` by `Subst.instId Γ α` returns the boundary. -/
theorem instantiate_rename_inl (Γ α : C.Arity) (β : Bd (Γ ⋈ α)) :
  instantiate (Subst.instId Γ α) ((rename (Renaming.inl Γ α ⇑ʳ α) β : Bd ((Γ ⋈ α) ⋈ α)))
    = β
  := by
  simpa only [Renaming.extend_unit] using act_instId_weaken Γ α 1 β

/-- A boundary whose renaming along `ρ` is `eq l r` is `eq l₀ r₀` with
`l = ⟦ ρ ⟧ʳ l₀` and `r = ⟦ ρ ⟧ʳ r₀`. -/
theorem rename_eq_inv {Γ Γ' : C.Arity} (ρ : Γ →ʳ Γ') :
  ∀ {β : Bd Γ} {l r : Expr Γ'}, rename ρ β = .eq l r →
    ∃ l₀ r₀, β = .eq l₀ r₀ ∧ l = ⟦ ρ ⟧ʳ l₀ ∧ r = ⟦ ρ ⟧ʳ r₀
  | .eq l₀ r₀, _, _, rfl => ⟨l₀, r₀, rfl, rfl, rfl⟩

/-- A boundary whose action by `σ` at depth `Φ` is `eq l r` is `eq l₀ r₀` with
`l = σ.act Φ l₀` and `r = σ.act Φ r₀`. -/
theorem act_eq_inv {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
  ∀ {β : Bd (Γ ⋈ Δ ⋈ Φ)} {l r : Expr (Γ ⋈ Ξ ⋈ Φ)}, act σ Φ β = .eq l r →
    ∃ l₀ r₀, β = .eq l₀ r₀ ∧ l = σ.act Φ l₀ ∧ r = σ.act Φ r₀
  | .eq l₀ r₀, _, _, rfl => ⟨l₀, r₀, rfl, rfl, rfl⟩

/-- If `κ (ρ x)` is the η-expansion of `ρ' x` for every slot `x`, then acting by `κ`
at depth `Φ` after renaming along `ρ ⇑ʳ Φ` is renaming along `ρ' ⇑ʳ Φ`. -/
theorem act_rename_cancel
    {Γ Δ' Γ' : C.Arity}
    (ρ : Γ →ʳ Δ') (ρ' : Γ →ʳ Γ') (κ : Subst Δ' Γ')
    (h : ∀ ⦃α : C.Arity⦄ (x : Γ ∋ α), κ (ρ x) = Expr.η (ρ' x))
    (Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
  act (Γ := 1) κ Φ (rename (ρ ⇑ʳ Φ) β) = rename (ρ' ⇑ʳ Φ) β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_rename_cancel ρ ρ' κ h
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_rename_cancel ρ ρ' κ h

/-! ### Functoriality -/

/-- Renaming along the identity is the identity. -/
theorem rename_id {Γ : C.Arity} (β : Bd Γ) :
  rename (𝟙ʳ Γ) β = β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply Renaming.act_id
  | eq l r => apply congrArg₂ eq <;> apply Renaming.act_id

/-- Renaming along `θ ∘ʳ ρ` is renaming along `ρ` and then along `θ`. -/
theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (θ : Δ →ʳ Ξ) (β : Bd Γ) :
  rename (θ ∘ʳ ρ) β = rename θ (rename ρ β)
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply Renaming.act_comp
  | eq l r => apply congrArg₂ eq <;> apply Renaming.act_comp

/-- The identity substitution acts as the identity. -/
theorem act_id (Γ Φ : C.Arity) (β : Bd (Γ ⋈ Φ)) :
  act (Subst.id Γ) (Γ := 1) Φ β = β
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_id
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_id

/-- Acting by `Subst.comp σ θ` is acting by `σ` and then by `θ`. -/
theorem act_comp
    {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ)) (θ : Subst Θ (Γ ⋈ Ξ)) (Φ : C.Arity) (β : Bd (Γ ⋈ Δ ⋈ Φ)) :
  act (Subst.comp σ θ) Φ β = act θ Φ (act σ Φ β)
  := by
  cases β with
  | sort => rfl
  | of S =>
      apply congrArg of
      apply _root_.act_comp
  | eq l r => apply congrArg₂ eq <;> apply _root_.act_comp

end Bd
