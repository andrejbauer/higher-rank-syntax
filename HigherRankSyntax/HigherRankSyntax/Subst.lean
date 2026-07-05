import HigherRankSyntax.Expr

/-!
# Substitution

`Subst Δ Γ` maps each `Δ`-slot of arity `α` and result type `τ` to an
expression over `Γ ⋈ α` with result type `τ`.

`Subst.act σ Φ` applies `σ : Subst Δ (Γ ⋈ Ξ)` to an expression in
`Expr (Γ ⋈ Δ ⋈ Φ) τ`, producing an expression in `Expr (Γ ⋈ Ξ ⋈ Φ) τ`.

`Subst.threeway` classifies a head slot of `Γ ⋈ Δ ⋈ Ξ` as coming from
`Γ`, `Δ`, or `Ξ`.
-/

variable {A : Type} {C : Carrier A}

/-- A substitution from a domain arity into a target arity. -/
abbrev Subst (Δ Γ : C.Arity) :=
  ∀ ⦃α : C.Arity⦄ ⦃τ : C.Ty⦄, Δ ∋[τ] α → Expr (Γ ⋈ α) τ

/-- The identity substitution at arity `Γ`. -/
def Subst.id (Γ : C.Arity) : Subst Γ Γ :=
  (fun ⦃_⦄ ⦃_⦄ p => Expr.η p)

/-- Three-way dispatch of a slot of `Γ ⋈ Δ ⋈ Ξ`, used by `Subst.act`: the
prefix `Γ`, the substitution domain `Δ`, or the current depth `Ξ`. -/
inductive LeftMiddleRight (Γ Δ Ξ α : C.Arity) (τ : C.Ty) : Type where
  /-- The slot belongs to the prefix `Γ`. -/
  | left (q : Γ ∋[τ] α)
  /-- The slot belongs to the substitution domain `Δ`. -/
  | middle (q : Δ ∋[τ] α)
  /-- The slot belongs to the current depth `Ξ`. -/
  | right (q : Ξ ∋[τ] α)

/-- Dispatching a `Γ ⋈ Δ ⋈ Ξ`-slot into its source: prefix `Γ`, substitution
domain `Δ`, or current depth `Ξ`. -/
def Subst.threeway {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {τ : C.Ty} (p : Γ ⋈ Δ ⋈ Ξ ∋[τ] α) :
    LeftMiddleRight Γ Δ Ξ α τ :=
  C.copair Ξ (Γ ⋈ Δ) _
    (fun q => .right q)
    (fun q => C.copair Δ Γ _ (fun y => .middle y) (fun x => .left x) q) p

/-- Embed a classified site back into `Γ ⋈ Δ ⋈ Ξ`. -/
def Subst.reinject {Γ Δ Ξ : C.Arity} {α : C.Arity} {τ : C.Ty} :
  LeftMiddleRight Γ Δ Ξ α τ → Γ ⋈ Δ ⋈ Ξ ∋[τ] α
  | .left x => C.inr (C.inr x)
  | .middle x => C.inr (C.inl x)
  | .right x => C.inl x

/-- Every `Γ ⋈ Δ ⋈ Ξ` slot is the reinjection of its three-way classification. -/
theorem Subst.isReinject {Γ Δ Ξ : C.Arity} {α : C.Arity} {τ : C.Ty}
    (x : Γ ⋈ Δ ⋈ Ξ ∋[τ] α) :
  ∃ y : LeftMiddleRight Γ Δ Ξ α τ, x = reinject y
  := by
  rcases C.cover Ξ (Γ ⋈ Δ) x with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨.right x, rfl⟩
  · rcases C.cover Δ Γ y with ⟨z, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨.middle z, rfl⟩
    · exact ⟨.left w, rfl⟩

/-- Classifying a concrete right-injected `Ξ` head returns the right site. -/
@[simp] theorem Subst.threeway_inr {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {τ : C.Ty} (x : Ξ ∋[τ] α) :
  threeway (Γ := Γ) (Δ := Δ) (C.inl x) = .right x
  := by
  simp [threeway, Carrier.copair, Carrier.inl]

/-- Classifying a concrete middle-domain head returns the middle site. -/
@[simp] theorem Subst.threeway_inl_dom {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {τ : C.Ty} (x : Δ ∋[τ] α) :
  threeway (Γ := Γ) (Ξ := Ξ) (C.inr (C.inl x)) = .middle x
  := by
  simp [threeway, Carrier.copair, Carrier.inl, Carrier.inr]

/-- Classifying a concrete left-prefix head returns the left site. -/
@[simp] theorem Subst.threeway_inl_pre {Γ Δ Ξ : C.Arity}
    {α : C.Arity} {τ : C.Ty} (x : Γ ∋[τ] α) :
  threeway (Δ := Δ) (Ξ := Ξ) (C.inr (C.inr x)) = .left x
  := by
  simp [threeway, Carrier.copair, Carrier.inr]

/-- The identity instantiation at arity `α`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId (Δ α : C.Arity) : Subst α (Δ ⋈ α) :=
  fun ⦃_⦄ ⦃_⦄ i => Expr.η (C.inl i)


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `Φ`. -/
def Subst.act {Γ Δ Ξ : C.Arity}
      (σ : Subst Δ (Γ ⋈ Ξ))(Φ : C.Arity) {τ : C.Ty} :
    Expr (Γ ⋈ Δ ⋈ Φ) τ → Expr (Γ ⋈ Ξ ⋈ Φ) τ
  | .ap (α := α) x args =>
      match threeway x with
      | .right x =>
          .ap (C.inl x) (fun {_} {_} i => σ.act (Φ ⋈ _) (args i))
      | .middle z =>
          act (fun {_} {_} i => σ.act (Φ ⋈ _) (args i)) 1 (σ z)
      | .left z =>
          .ap (C.inr (C.inr z)) (fun {_} {_} i => σ.act (Φ ⋈ _) (args i))
termination_by e => (Δ, (⟨_, _, e⟩ : Σ Γ : C.Arity, Σ τ : C.Ty, Expr Γ τ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)
    | exact Prod.Lex.left _ _ ⟨_, ⟨z⟩⟩

/-- The ground substitution action `σ.act 1 e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ 1 e

/-- Substitution-level composition.  First substitute with `σ`, producing
expressions over `Γ ⋈ Θ`; then act on each filler with `θ`, producing
expressions over `Γ ⋈ Ξ`. -/
def Subst.comp {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ))
    (θ : Subst Θ (Γ ⋈ Ξ)) :
  Subst Δ (Γ ⋈ Ξ) :=
  (fun ⦃β⦄ ⦃_⦄ x => θ.act β (σ x))
