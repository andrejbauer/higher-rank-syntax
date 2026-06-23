import HigherRankSyntax.Carrier
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The constructor
`ap` takes an arity-typed head slot `p : Γ ∋ α` and a dependent family of children
indexed by the slots of `α`, each child living in `Γ` extended by that slot's arity.
-/


/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {A : Type} {C : Carrier A} : C.Arity → Type where
  /-- An application of a head slot `x : Γ ∋ α` to a dependent family of children, one per position of `α`. -/
  | ap : {Γ α : C.Arity} → (x : Γ ∋ α) → (∀ {Δ} (_i : α ∋ Δ) , Expr (Γ ⋈ Δ)) → Expr Γ

/-- The argument family of an application headed by an `α`-slot in context `Γ`. -/
abbrev Expr.Args {A : Type} {C : Carrier A} (Γ α : C.Arity) :=
  ∀ {Δ} (_i : α ∋ Δ) , Expr (Γ ⋈ Δ)

/-- `Expr.Subterm e' e` holds when `e = ap p args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm {A : Type} {C : Carrier A} : (Σ Γ : C.Arity, Expr Γ) → (Σ Γ : C.Arity, Expr Γ) → Prop where
  | of_arg {Γ α : C.Arity} (x : Γ ∋ α) (args : Args Γ α) {Δ : C.Arity} (j : α ∋ Δ) :
      Subterm ⟨Γ ⋈ Δ, args j⟩ ⟨Γ, ap x args⟩

theorem Expr.Subterm.wf {A : Type} {C : Carrier A} :
    WellFounded (@Expr.Subterm A C) := by
  constructor
  intro ⟨Γ, e⟩
  induction e with
  | ap p args ih =>
    apply Acc.intro
    rintro ⟨_, _⟩ h
    cases h
    apply ih

instance Expr.Subterm.wellFoundedRelation {A : Type} {C : Carrier A} :
    WellFoundedRelation (Σ Γ : C.Arity, Expr Γ) where
  rel := @Expr.Subterm A C
  wf := Expr.Subterm.wf

/-- η-expansion: a variable `p : Γ ∋ α` becomes the fully-applied tree
`ap (C.inl p) (fun i => η (C.inr i))`. -/
def Expr.η {A : Type} {C : Carrier A} {Γ α : C.Arity} : Γ ∋ α → Expr (Γ ⋈ α)
  | x => .ap (C.inl x) (fun {_} i => η (C.inr i))
termination_by _ => α
decreasing_by exact ⟨i⟩

/-- Action of a renaming on an expression. -/
def Renaming.act {A : Type} {C : Carrier A} {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Expr Γ → Expr Δ
  | .ap x args => .ap (ρ x) (fun {Ω} i => act (ρ ⇑ʳ Ω) (args i))

@[inherit_doc Renaming.act]
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.act ρ e

theorem Renaming.act_ap {A : Type} {C : Carrier A} {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (x : Γ ∋ α)
    (args : Expr.Args Γ α) :
  ⟦ ρ ⟧ʳ (.ap x args) = .ap (ρ x) (fun {Ω} i => ⟦ ρ ⇑ʳ Ω ⟧ʳ (args i))
  := rfl

theorem Renaming.act_id {A : Type} {C : Carrier A} {Γ : C.Arity} :
  ∀ (e : Expr Γ), ⟦ 𝟙ʳ Γ ⟧ʳ e = e
  | .ap x args => by
    simp [act_ap]
    funext
    apply act_id

theorem Renaming.act_comp
    {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) :
  ∀ (e : Expr Γ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | .ap x args => by
    rw [act_ap, act_ap, act_ap]
    congr 1
    funext
    rw [Renaming.extend_comp]
    apply act_comp
