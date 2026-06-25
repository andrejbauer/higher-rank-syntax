import HigherRankSyntax.Expr

/-!
# Substitution

`Subst Δ Γ` maps each `Δ`-slot `i` to an expression over `Γ ∷ i.arity`.

`Subst.act σ Φ` applies the substitution `σ` to an expression at depth
`Φ : Shape C` (with `[Proper Φ]`).  The action is still prefix-aware: if
`σ : Subst Δ (Γ ⋈ Ξ)`, then it transforms
`Expr (Γ ⋈ Δ ⋈ Φ)` into `Expr (Γ ⋈ Ξ ⋈ Φ)`.  The data no longer stores the
prefix separately; the operation chooses that decomposition when acting.

`Subst.threeway` is the proof-facing head classifier for this action:
right/current-depth heads are preserved, middle/domain heads fire `σ`, and
left/prefix heads are preserved by direct reinjection.
-/


/-- A substitution record from a domain shape into a full target shape.
The `sub` field is the only data; prefix preservation is not part of the
record and is instead selected by `Subst.act` when the target is decomposed
as `Γ ⋈ Ξ`. -/
abbrev Subst {A : Type} {C : Carrier A} (Δ Γ : C.Arity) :=
  ∀ ⦃ α : C.Arity ⦄, Δ ∋ α → Expr (Γ ⋈ α)

/-- The identity substitution at shape `Γ`. -/
def Subst.id {A : Type} {C : Carrier A} (Γ : C.Arity) : Subst Γ Γ :=
  (fun ⦃β⦄ (p : Γ ∋ β) => Expr.η p)

/-- Three-way dispatch of a slot of `Γ ⋈ Δ ⋈ Ξ`, used by `Subst.act`: the
prefix `Γ`, the substitution domain `Δ`, or the current depth `Ξ`. -/
inductive LeftMiddleRight {A : Type} {C : Carrier A} (Γ Δ Ξ α : C.Arity) : Type where
  /-- The slot belongs to the prefix `Γ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `Δ`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the current depth `Ξ`. -/
  | right (q : Ξ ∋ α)

/-- Dispatching a `Γ ⋈ Δ ⋈ Ξ`-slot into its source: prefix `Γ`, substitution
domain `Δ`, or current depth `Ξ`. -/
def Subst.threeway {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α} (p : (Γ ⋈ Δ ⋈ Ξ) ∋ α) : LeftMiddleRight Γ Δ Ξ α :=
  C.copair Ξ (Γ ⋈ Δ) _
    (fun q => .right q)
    (fun q => C.copair Δ Γ _ (fun y => .middle y) (fun x => .left x) q) p

/-- Embed a classified site back into `Γ ⋈ Δ ⋈ Ξ`. -/
def Subst.reinject {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity} {α} :
  LeftMiddleRight Γ Δ Ξ α → (Γ ⋈ Δ ⋈ Ξ) ∋ α
  | .left x => C.inr (C.inr x)
  | .middle x => C.inr (C.inl x)
  | .right x => C.inl x

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.threeway`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.isReinject {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity} {α}
    (x : (Γ ⋈ Δ ⋈ Ξ) ∋ α) :
  ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases C.cover Ξ (Γ ⋈ Δ) x with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨.right x, rfl⟩
  · rcases C.cover Δ Γ y with ⟨z, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨.middle z, rfl⟩
    · exact ⟨.left w, rfl⟩

/-- Classifying a concrete right-injected `Ξ` head returns the right site. -/
@[simp] theorem Subst.threeway_inr {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (C.inl x) = .right x
  := by
  simp [threeway, Carrier.copair, Carrier.inl]

/-- Classifying a concrete middle-domain head returns the middle site. -/
@[simp] theorem Subst.threeway_inl_dom {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (C.inr (C.inl x)) = .middle x
  := by
  simp [threeway, Carrier.copair, Carrier.inl, Carrier.inr]

/-- Classifying a concrete left-prefix head returns the left site. -/
@[simp] theorem Subst.threeway_inl_pre {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (C.inr (C.inr x)) = .left x
  := by
  simp [threeway, Carrier.copair, Carrier.inr]

/-- The identity instantiation for the one-position telescope `⌊α⌋`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {A : Type} {C : Carrier A} (Δ α : C.Arity) : Subst α (Δ ⋈ α) :=
  fun ⦃β⦄ (i : α ∋ β) => Expr.η (C.inl i)


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `Φ`. -/
def Subst.act {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
      (σ : Subst Δ (Γ ⋈ Ξ))(Φ : C.Arity) :
    Expr (Γ ⋈ Δ ⋈ Φ) → Expr (Γ ⋈ Ξ ⋈ Φ)
  | .ap (α := α) x args =>
      match threeway x with
      | .right x =>
          .ap (C.inl x) (fun {_} i => σ.act (Φ ⋈ _) (args i))
      | .middle z =>
          act (fun {_} i => σ.act (Φ ⋈ _) (args i)) 1 (σ z)
      | .left z =>
          .ap (C.inr (C.inr z)) (fun {_} i => σ.act (Φ ⋈ _) (args i))
termination_by e => (Δ, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
decreasing_by
  all_goals
    first
    | exact Prod.Lex.right _ (Expr.Subterm.of_arg x args i)
    | exact Prod.Lex.left _ _ ⟨z⟩

/-- The ground substitution action `σ.act 1 e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ 1 e

/-- Substitution-level composition.  First substitute with `σ`, producing
expressions over `Γ ⋈ Θ`; then act on each filler with `θ`, producing
expressions over `Γ ⋈ Ξ`. -/
def Subst.comp {A : Type} {C : Carrier A} {Γ Δ Θ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Θ))
    (θ : Subst Θ (Γ ⋈ Ξ)) :
  Subst Δ (Γ ⋈ Ξ) :=
  (fun ⦃β⦄ x => θ.act β (σ x))
