import HigherRankSyntax.Carrier
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ τ` is the type of expressions in arity `Γ` and result type `τ` over a
carrier `C`.  The constructor `ap` takes a typed head slot `p : Γ ∋[τ] α` and a
dependent family of children indexed by the typed slots of `α`, each child
living in `Γ` extended by that slot's arity and at that slot's result type.
-/

variable {A : Type} {C : Carrier A}

/-- Expressions in arity `Γ` and result type `τ` over a carrier `C`. -/
inductive Expr : C.Arity → C.Ty → Type where
  /-- An application with a head slot and one child for each position of the head arity. -/
  | ap : {Γ α : C.Arity} → {τ : C.Ty} → (x : Γ ∋[τ] α) →
      (∀ ⦃Δ⦄ ⦃σ⦄ (_i : α ∋[σ] Δ), Expr (Γ ⋈ Δ) σ) →
      Expr Γ τ

/-- The argument family of an application headed by an `α`-slot in context `Γ`. -/
abbrev Expr.Args (Γ α : C.Arity) :=
  ∀ ⦃Δ⦄ ⦃σ⦄ (_i : α ∋[σ] Δ), Expr (Γ ⋈ Δ) σ

/-- `Expr.Subterm e' e` holds when `e = ap p args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm :
    (Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ) →
    (Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ) → Prop where
  | of_arg {Γ α : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] α) (args : Args Γ α)
      {Δ} {σ} (j : α ∋[σ] Δ) : Subterm ⟨Γ ⋈ Δ, σ, args j⟩ ⟨Γ, τ, ap x args⟩

theorem Expr.Subterm.wf :
    WellFounded (@Expr.Subterm A C)
  := by
  constructor
  intro ⟨Γ, τ, e⟩
  induction e with
  | ap p args ih =>
    apply Acc.intro
    rintro ⟨_, _, _⟩ h
    cases h
    apply ih

instance Expr.Subterm.wellFoundedRelation :
    WellFoundedRelation (Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ) where
  rel := @Expr.Subterm A C
  wf := Expr.Subterm.wf

/-- η-expansion: a variable `p : Γ ∋[τ] α` becomes the fully-applied tree
`ap (C.inr p) (fun i => η (C.inl i))`. -/
def Expr.η {Γ α : C.Arity} {τ : C.Ty} : Γ ∋[τ] α → Expr (Γ ⋈ α) τ
  | x => .ap (C.inr x) (fun {_} {_} i => η (C.inl i))
termination_by _ => α
decreasing_by exact ⟨_, ⟨i⟩⟩

/-- Action of a renaming on an expression. -/
def Renaming.act {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) {τ : C.Ty} : Expr Γ τ → Expr Δ τ
  | .ap x args => .ap (ρ x) (fun {Ω} {_} i => act (ρ ⇑ʳ Ω) (args i))

@[inherit_doc Renaming.act]
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.act ρ e

theorem Renaming.act_ap {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    {α : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] α)
    (args : Expr.Args Γ α) :
  ⟦ ρ ⟧ʳ (.ap x args) = .ap (ρ x) (fun {Ω} {_} i => ⟦ ρ ⇑ʳ Ω ⟧ʳ (args i))
  := rfl

theorem Renaming.act_id {Γ : C.Arity} {τ : C.Ty} :
  ∀ (e : Expr Γ τ), ⟦ 𝟙ʳ Γ ⟧ʳ e = e
  | .ap x args => by
    simp [act_ap, Renaming.id]
    funext
    apply act_id

theorem Renaming.act_comp
    {Γ Δ Ξ : C.Arity}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) {τ : C.Ty} :
  ∀ (e : Expr Γ τ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | .ap x args => by
    rw [act_ap]
    congr 1
    funext
    rw [Renaming.extend_comp]
    apply act_comp
