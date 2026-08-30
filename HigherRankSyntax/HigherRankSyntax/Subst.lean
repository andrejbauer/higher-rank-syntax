import HigherRankSyntax.Expr

/-!
# Substitution

`Subst Δ Γ` maps each `Δ`-slot of arity `α` to an expression over `Γ ⋈ α`.

`Subst.act σ Φ` applies `σ : Subst Δ (Γ ⋈ Ξ)` to an expression in
`Expr (Γ ⋈ Δ ⋈ Φ)`, producing an expression in `Expr (Γ ⋈ Ξ ⋈ Φ)`.

`Subst.threeway` classifies a head slot of `Γ ⋈ Δ ⋈ Ξ` as coming from
`Γ`, `Δ`, or `Ξ`.
-/

/-- A substitution from a domain arity into a target arity. -/
abbrev Subst (Δ Γ : C.Arity) :=
  ∀ ⦃α : C.Arity⦄, Δ ∋ α → Expr (Γ ⋈ α)

/-- The identity substitution at arity `Γ`. -/
def Subst.id (Γ : C.Arity) : Subst Γ Γ :=
  (fun ⦃_⦄ p => Expr.η p)

/-- The substitution obtained by eta-expanding the image of each renamed slot. -/
def Subst.ofRenaming {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) : Subst Γ Δ :=
  fun ⦃_⦄ x => Expr.η (ρ x)

/-- Three-way dispatch of a slot of `Γ ⋈ Δ ⋈ Ξ`, used by `Subst.act`: the
prefix `Γ`, the substitution domain `Δ`, or the current depth `Ξ`. -/
inductive LeftMiddleRight (Γ Δ Ξ α : C.Arity) : Type where
  /-- The slot belongs to the prefix `Γ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `Δ`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the current depth `Ξ`. -/
  | right (q : Ξ ∋ α)

/-- Dispatching a `Γ ⋈ Δ ⋈ Ξ`-slot into its source: prefix `Γ`, substitution
domain `Δ`, or current depth `Ξ`. -/
def Subst.threeway {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (p : Γ ⋈ Δ ⋈ Ξ ∋ α) :
    LeftMiddleRight Γ Δ Ξ α :=
  C.copair (Γ ⋈ Δ) Ξ _
    (fun q => C.copair Γ Δ _ (fun x => .left x) (fun y => .middle y) q)
    (fun q => .right q) p

/-- Embed a classified site back into `Γ ⋈ Δ ⋈ Ξ`. -/
def Subst.reinject {Γ Δ Ξ : C.Arity} {α : C.Arity} :
  LeftMiddleRight Γ Δ Ξ α → Γ ⋈ Δ ⋈ Ξ ∋ α
  | .left x => C.inl (C.inl x)
  | .middle x => C.inl (C.inr x)
  | .right x => C.inr x

/-- Every `Γ ⋈ Δ ⋈ Ξ` slot is the reinjection of its three-way classification. -/
theorem Subst.isReinject {Γ Δ Ξ : C.Arity} {α : C.Arity}
    (x : Γ ⋈ Δ ⋈ Ξ ∋ α) :
  ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨y, rfl⟩ | ⟨x, rfl⟩
  · rcases C.cover Γ Δ y with ⟨w, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨.left w, rfl⟩
    · exact ⟨.middle z, rfl⟩
  · exact ⟨.right x, rfl⟩

/-- Classifying a concrete current-depth `Ξ` head returns the right site. -/
@[simp] theorem Subst.threeway_right {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (C.inr x) = .right x
  := by
  simp [threeway, Carrier.copair, Carrier.inr]

/-- Classifying a concrete domain `Δ` head returns the middle site. -/
@[simp] theorem Subst.threeway_middle {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (C.inl (C.inr x)) = .middle x
  := by
  simp [threeway, Carrier.copair, Carrier.inl, Carrier.inr]

/-- Classifying a concrete prefix `Γ` head returns the left site. -/
@[simp] theorem Subst.threeway_left {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (C.inl (C.inl x)) = .left x
  := by
  simp [threeway, Carrier.copair, Carrier.inl]

/-- The identity instantiation at arity `α`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId (Δ α : C.Arity) : Subst α (Δ ⋈ α) :=
  fun ⦃_⦄ i => Expr.η (C.inr i)

/-- The substitution on `Γ ⋈ Δ` given by `σ` on `Γ`-slots and `θ` on `Δ`-slots. -/
def Subst.copair {Γ Δ Ω : C.Arity} (σ : Subst Γ Ω) (θ : Subst Δ Ω) :
    Subst (Γ ⋈ Δ) Ω :=
  fun ⦃Λ⦄ x =>
    C.copair Γ Δ (Expr (Ω ⋈ Λ)) (fun y => σ y) (fun z => θ z) x

@[simp] theorem Subst.copair_inl {Γ Δ Ω : C.Arity}
    (σ : Subst Γ Ω) (θ : Subst Δ Ω) {Λ : C.Arity} (x : Γ ∋ Λ) :
  Subst.copair σ θ (C.inl x) = σ x
  := by simp [Subst.copair, Carrier.copair, Carrier.inl]

@[simp] theorem Subst.copair_inr {Γ Δ Ω : C.Arity}
    (σ : Subst Γ Ω) (θ : Subst Δ Ω) {Λ : C.Arity} (x : Δ ∋ Λ) :
  Subst.copair σ θ (C.inr x) = θ x
  := by simp [Subst.copair, Carrier.copair, Carrier.inr]


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `Φ`. -/
def Subst.act {Γ Δ Ξ : C.Arity}
      (σ : Subst Δ (Γ ⋈ Ξ)) (Φ : C.Arity) :
    Expr (Γ ⋈ Δ ⋈ Φ) → Expr (Γ ⋈ Ξ ⋈ Φ)
  | .ap (α := α) x args =>
      match threeway x with
      | .right x =>
          .ap (C.inr x) (fun {_} i => σ.act (Φ ⋈ _) (args i))
      | .middle z =>
          act (Γ := Γ ⋈ Ξ)
            (fun {_} i => σ.act (Φ ⋈ _) (args i)) 1 (σ z)
      | .left z =>
          .ap (C.inl (C.inl z)) (fun {_} i => σ.act (Φ ⋈ _) (args i))
termination_by e => (Δ, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)
    | exact Prod.Lex.left _ _ ⟨z⟩

/-- Substitution-level composition.  First substitute with `σ`, producing
expressions over `Γ ⋈ Θ`; then act on each filler with `θ`, producing
expressions over `Γ ⋈ Ξ`. -/
def Subst.comp {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ))
    (θ : Subst Θ (Γ ⋈ Ξ)) :
  Subst Δ (Γ ⋈ Ξ) :=
  (fun ⦃β⦄ x => θ.act β (σ x))
