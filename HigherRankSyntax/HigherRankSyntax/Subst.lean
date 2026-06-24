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

/-- Package an application argument family as a substitution from its head arity. -/
def Subst.fromArgs {A : Type} {C : Carrier A} (Γ Δ : C.Arity)
    (args : Expr.Args Γ Δ) :
    Subst Δ Γ := args

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
  C.copair (Γ ⋈ Δ) Ξ _ p
    (fun q => C.copair Γ Δ _ q .left .middle)
    .right

/-- Embed a classified site back into `Γ ⋈ Δ ⋈ Ξ`. -/
def Subst.reinject {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity} {α} :
  LeftMiddleRight Γ Δ Ξ α → (Γ ⋈ Δ ⋈ Ξ) ∋ α
  | .left x => C.inl (C.inl x)
  | .middle x => C.inl (C.inr x)
  | .right x => C.inr x

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.threeway`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.isReinject {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
      {α}
      (x : (Γ ⋈ Δ ⋈ Ξ) ∋ α) :
    ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨x, h_x⟩ | ⟨y, h_y⟩
  · exact ⟨.right x, h_x⟩
  · rcases C.cover Γ Δ y with ⟨z, h_z⟩ | ⟨w, h_w⟩
    · subst h_y
      exact ⟨.middle z, by rw [h_z]; rfl⟩
    · subst h_y
      exact ⟨.left w, by rw [h_w]; rfl⟩

/-- Classifying a concrete right-injected `Ξ` head returns the right site. -/
@[simp] theorem Subst.threeway_inr {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (C.inr x) = .right x
  := by
  unfold threeway
  rw [C.copair_inl]

/-- Classifying a concrete middle-domain head returns the middle site. -/
@[simp] theorem Subst.threeway_inl_dom {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (C.inl (C.inr x)) = .middle x
  := by
  unfold threeway
  rw [C.copair_inr]
  rw [C.copair_inl]

/-- Classifying a concrete left-prefix head returns the left site. -/
@[simp] theorem Subst.threeway_inl_pre {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (C.inl (C.inl x)) = .left x
  := by
  unfold threeway
  rw [C.copair_inr]
  rw [C.copair_inr]

/-- The identity instantiation for the one-position telescope `⌊α⌋`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {A : Type} {C : Carrier A} (Δ α : C.Arity) : Subst α (Δ ⋈ α) :=
  fun ⦃β⦄ (i : α ∋ β) => Expr.η (C.inr i)


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `Φ`. -/
def Subst.act {A : Type} {C : Carrier A} {Γ Δ Ξ : C.Arity}
    (σ : Subst Δ (Γ ⋈ Ξ))
    (Φ : C.Arity) :
    Expr (Γ ⋈ Δ ⋈ Φ) → Expr (Γ ⋈ Ξ ⋈ Φ)
  | .ap (α := α) x args =>
      match threeway x with
      | .right x =>
          .ap (C.inr x)
            (fun {_} i => σ.act (Φ ⋈ _) (args i))
      | .middle z =>
          act (Subst.fromArgs (Γ ⋈ Ξ ⋈ Φ) α
                (fun {_} i => σ.act (Φ ⋈ _) (args i))) 1 (σ z)
      | .left z =>
          .ap (C.inl (C.inl z))
            (fun {_} i => σ.act (Φ ⋈ _) (args i))
termination_by e =>
  (Δ, (⟨_, e⟩ : Σ Γ : C.Arity, Expr Γ))
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
