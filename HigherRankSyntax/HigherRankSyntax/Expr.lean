import HigherRankSyntax.ListCarrier
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in arity `Γ`.  The constructor `ap` takes a
head slot `x : Γ ∋ α` and, for each slot `i : α ∋ Δ`, an argument in `Expr (Γ ⋈ Δ)`.
-/

/-- Expressions in arity `Γ`. -/
inductive Expr : C.Arity → Type where
  /-- The application of a head slot `x : Γ ∋ α` to one argument in `Expr (Γ ⋈ Δ)` for
  each slot of `α` of arity `Δ`. -/
  | ap : {Γ α : C.Arity} → (x : Γ ∋ α) →
      (∀ ⦃Δ⦄ (_i : α ∋ Δ), Expr (Γ ⋈ Δ)) →
      Expr Γ

/-- The arguments of an application in arity `Γ` headed by a slot of arity `α`. -/
abbrev Expr.Args (Γ α : C.Arity) :=
  ∀ ⦃Δ⦄ (_i : α ∋ Δ), Expr (Γ ⋈ Δ)

/-- `Expr.Subterm e' e` holds when `e = ap x args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm :
    (Σ Γ : C.Arity, Expr Γ) →
    (Σ Γ : C.Arity, Expr Γ) → Prop where
  | of_arg {Γ α : C.Arity} (x : Γ ∋ α) (args : Args Γ α)
      {Δ} (j : α ∋ Δ) : Subterm ⟨Γ ⋈ Δ, args j⟩ ⟨Γ, ap x args⟩

theorem Expr.Subterm.wf :
  WellFounded (@Expr.Subterm)
  := by
  constructor
  intro ⟨Γ, e⟩
  induction e with
  | ap x args ih =>
    apply Acc.intro
    rintro ⟨_, _⟩ h
    cases h
    apply ih

instance Expr.Subterm.wellFoundedRelation :
    WellFoundedRelation (Σ Γ : C.Arity, Expr Γ) where
  rel := @Expr.Subterm
  wf := Expr.Subterm.wf

/-- The η-expansion of a slot `x : Γ ∋ α`: the expression
`ap (C.inl x) (fun i => η (C.inr i))` in `Expr (Γ ⋈ α)`. -/
def Expr.η {Γ α : C.Arity} : Γ ∋ α → Expr (Γ ⋈ α)
  | x => .ap (C.inl x) (fun ⦃_⦄ i => η (C.inr i))
termination_by _ => α
decreasing_by exact ⟨i⟩

/-- The action of a renaming on expressions: `ρ` renames the head, and `ρ ⇑ʳ Ω` acts on
each argument over `Γ ⋈ Ω`. -/
def Renaming.act {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Expr Γ → Expr Δ
  | .ap x args => .ap (ρ x) (fun {Ω} i => act (ρ ⇑ʳ Ω) (args i))

@[inherit_doc Renaming.act]
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.act ρ e

theorem Renaming.act_ap
    {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) {α : C.Arity} (x : Γ ∋ α) (args : Expr.Args Γ α) :
  ⟦ ρ ⟧ʳ (.ap x args) = .ap (ρ x) (fun {Ω} i => ⟦ ρ ⇑ʳ Ω ⟧ʳ (args i))
  := rfl

theorem Renaming.act_id {Γ : C.Arity} :
  ∀ (e : Expr Γ), ⟦ 𝟙ʳ Γ ⟧ʳ e = e
  | .ap x args => by
    simp only [act_ap, extend_id]
    congr 1
    funext Δ i
    apply act_id

theorem Renaming.act_comp
    {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) :
  ∀ (e : Expr Γ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | .ap x args => by
    rw [act_ap]
    congr 1
    funext Ω i
    rw [extend_comp]
    apply act_comp
