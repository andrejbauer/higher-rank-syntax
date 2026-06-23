import HigherRankSyntax.Shape
import HigherRankSyntax.Renaming

/-!
# Expressions of a higher-rank binding signature

`Expr Γ` is the type of expressions in shape `Γ` over a carrier `C`.  The constructor
`ap` takes an arity-typed head slot `p : Γ ∋ α` and a dependent family of children
indexed by `C.Position α`, each child living in `Γ` extended by the position's sub-arity.
-/


/-- Expressions in shape `Γ` over a carrier `C`. -/
inductive Expr {C : Carrier} : Shape C → Type where
  /-- An application of a head slot `x : Γ ∋ α` to a dependent family of children, one per position of `α`. -/
  | ap : {Γ : Shape C} → {α : C.Arity} → (x : Γ ∋ α) → ((i : C.Position α) → Expr (Γ ∷ i.arity)) → Expr Γ

/-- The argument family of an application headed by an `α`-slot in context `Γ`. -/
abbrev Expr.Args {C : Carrier} (Γ : Shape C) (α : C.Arity) :=
  (i : C.Position α) → Expr (Γ ∷ i.arity)

/-- `Expr.Subterm e' e` holds when `e = ap p args` and `e'` is one of its arguments
`args j`. -/
inductive Expr.Subterm {C : Carrier} : (Σ Γ : Shape C, Expr Γ) → (Σ Γ : Shape C, Expr Γ) → Prop where
  | of_arg {Γ : Shape C} {α : C.Arity} (x : Γ ∋ α) (args : Args Γ α) (j : C.Position α) :
      Subterm ⟨Γ ∷ j.arity, args j⟩ ⟨Γ, ap x args⟩

theorem Expr.Subterm.wf {C : Carrier} : WellFounded (@Expr.Subterm C) := by
  constructor
  intro ⟨Γ, e⟩
  induction e with
  | ap p args ih =>
    apply Acc.intro
    rintro ⟨_, _⟩ h
    cases h
    exact ih _

instance Expr.Subterm.wellFoundedRelation {C : Carrier} : WellFoundedRelation (Σ Γ : Shape C, Expr Γ) where
  rel := @Expr.Subterm C
  wf := Expr.Subterm.wf

/-- η-expansion: a variable `p : Γ ∋ α` becomes the fully-applied tree
`ap (.there p) (fun i => η (.here i))`. -/
def Expr.η {C : Carrier} {Γ : Shape C} {α : C.Arity} : Γ ∋ α → Expr (Γ ∷ α)
  | x => .ap (.there x) (fun i => η (.here i))
termination_by _ => α
decreasing_by exact ⟨_, rfl⟩

/-- Action of a renaming on an expression. -/
def Renaming.act {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ) : Expr Γ → Expr Δ
  | .ap x args => .ap (ρ x) (fun i => act (ρ ⇑ʳ i.arity) (args i))

@[inherit_doc Renaming.act]
notation:60 "⟦" ρ "⟧ʳ " e:61 => Renaming.act ρ e

theorem Renaming.act_ap {C : Carrier} {Γ Δ : Shape C} (ρ : Γ →ʳ Δ)
    {α : C.Arity} (x : Γ ∋ α)
    (args : Expr.Args Γ α) :
  ⟦ ρ ⟧ʳ (.ap x args) = .ap (ρ x) (fun i => ⟦ ρ ⇑ʳ i.arity ⟧ʳ (args i))
  := rfl

theorem Renaming.act_id {C : Carrier} {Γ : Shape C} :
  ∀ (e : Expr Γ), ⟦ 𝟙ʳ Γ ⟧ʳ e = e
  | .ap x args => by
    simp [act_ap]
    funext i
    exact Renaming.act_id (args i)

theorem Renaming.act_comp
    {C : Carrier} {Γ Δ Ξ : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) :
  ∀ (e : Expr Γ), ⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
  | .ap x args => by
    show Expr.ap (σ (ρ x)) (fun i => ⟦ (σ ∘ʳ ρ) ⇑ʳ i.arity ⟧ʳ args i)
      = Expr.ap (σ (ρ x)) (fun i => ⟦ σ ⇑ʳ i.arity ⟧ʳ (⟦ ρ ⇑ʳ i.arity ⟧ʳ args i))
    congr 1
    funext i
    rw [Renaming.extend_comp]
    exact Renaming.act_comp _ _ (args i)
