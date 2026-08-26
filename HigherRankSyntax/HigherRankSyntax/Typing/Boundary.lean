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

variable {A : Type} {C : Carrier A}

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

/-- Transport a boundary along an equality of arities. -/
def cast {Γ Δ : C.Arity} (h : Γ = Δ) : Bd Γ → Bd Δ :=
  h ▸ fun β => β

@[simp] theorem cast_sort {Γ Δ : C.Arity} (h : Γ = Δ) :
  cast h (.sort : Bd Γ) = .sort := by
  subst h; rfl

@[simp] theorem cast_of {Γ Δ : C.Arity} (h : Γ = Δ) (S : Expr Γ) :
  cast h (.of S) = .of (_root_.cast (congrArg Expr h) S) := by
  subst h; rfl

@[simp] theorem cast_eq {Γ Δ : C.Arity} (h : Γ = Δ) (l r : Expr Γ) :
  cast h (.eq l r)
    = .eq (_root_.cast (congrArg Expr h) l) (_root_.cast (congrArg Expr h) r) := by
  subst h; rfl

theorem cast_injective {Γ Δ : C.Arity} (h : Γ = Δ) :
  Function.Injective (cast (C := C) h) := by
  subst h
  intro a b hab
  exact hab

theorem cast_proof_irrel {Γ Δ : C.Arity} (h k : Γ = Δ) (β : Bd Γ) :
  cast h β = cast k β := by
  have hk : h = k := Subsingleton.elim _ _
  subst k
  rfl

/-- A transport is heterogeneously the boundary it transports. -/
theorem cast_heq {Γ Δ : C.Arity} (h : Γ = Δ) (β : Bd Γ) :
  HEq (cast h β) β := by
  subst h
  rfl

/-- Transports of heterogeneously equal boundaries are heterogeneously equal,
whatever their sources and targets. -/
theorem cast_congr_heq {Γ Δ Γ' Δ' : C.Arity} (h : Γ = Δ) (k : Γ' = Δ')
    {β : Bd Γ} {β' : Bd Γ'} (hβ : HEq β β') :
  HEq (cast h β) (cast k β') := by
  subst h
  subst k
  exact hβ

theorem cast_comp {Γ Δ Ξ : C.Arity} (h : Γ = Δ) (k : Δ = Ξ) (β : Bd Γ) :
  cast k (cast h β) = cast (h.trans k) β := by
  subst Δ
  subst Ξ
  rfl

theorem cast_eq_cast_comp {Γ Δ Ξ : C.Arity} (h : Γ = Ξ) (k : Γ = Δ) (l : Δ = Ξ)
    (β : Bd Γ) :
  cast h β = cast l (cast k β) := by
  subst Δ
  subst Ξ
  rfl

/-- Action commutes with transport of a local segment. -/
theorem act_cast_local {S Γ Δ Φ Λ Ξ α : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (h : Λ = Ξ)
    (β : Bd (S ⋈ Γ ⋈ Φ ⋈ Λ ⋈ α)) :
  act σ (Φ ⋈ Ξ ⋈ α) (cast (congrArg (fun Ω => S ⋈ Γ ⋈ Φ ⋈ Ω ⋈ α) h) β)
    = cast (congrArg (fun Ω => S ⋈ Δ ⋈ Φ ⋈ Ω ⋈ α) h) (act σ (Φ ⋈ Λ ⋈ α) β) := by
  subst Ξ
  rfl

/-- Action by a lifted substitution is action below its fixed suffix. -/
theorem act_lift {Γ Δ Φ Ψ : C.Arity} (σ : Subst Γ Δ)
    (β : Bd (Γ ⋈ Φ ⋈ Ψ)) :
  cast (mul_assoc Δ Φ Ψ) (act (Γ := 1) (Ξ := Δ ⋈ Φ) (Subst.lift σ Φ) Ψ β)
    = act (Γ := 1) σ (Φ ⋈ Ψ) β := by
  cases β with
  | sort => rfl
  | of S => exact congrArg Bd.of (Subst.act_lift σ Φ Ψ S)
  | eq l r => exact congrArg₂ Bd.eq (Subst.act_lift σ Φ Ψ l) (Subst.act_lift σ Φ Ψ r)

/-- The boundary asserts an equation. -/
def isEq {Ω : C.Arity} : Bd Ω → Prop
  | .eq _ _ => True
  | _ => False

@[simp] theorem isEq_sort {Ω : C.Arity} : ¬ (Bd.sort : Bd Ω).isEq := id

@[simp] theorem isEq_of {Ω : C.Arity} (S : Expr Ω) : ¬ (Bd.of S).isEq := id

@[simp] theorem isEq_eq {Ω : C.Arity} (l r : Expr Ω) : (Bd.eq l r).isEq := trivial

/-- Renaming preserves the constructor. -/
@[simp] theorem isEq_rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) (β : Bd Γ) :
  (rename ρ β).isEq ↔ β.isEq := by
  cases β <;> rfl

/-- Substitution preserves the constructor. -/
@[simp] theorem isEq_act {Γ Δ Ξ : C.Arity} (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity)
    (β : Bd (Γ ⋈ Δ ⋈ Φ)) :
  (act σ Φ β).isEq ↔ β.isEq := by
  cases β <;> rfl

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
