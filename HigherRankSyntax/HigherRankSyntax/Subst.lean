import HigherRankSyntax.Expr
import HigherRankSyntax.ProperTele
import HigherRankSyntax.ListArity

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
abbrev Subst {C : Carrier} (Δ Γ : Shape C) :=
  ∀ ⦃ α : C.Arity ⦄, Δ ∋ α → Expr (Γ ∷ α)

/-- Package an application argument family as a singleton-domain substitution. -/
def Subst.fromArgs {C : Carrier} (α : C.Arity) (Γ : Shape C)
    (args : Expr.Args Γ α) :
    Subst ⌊α⌋ Γ :=
  fun | _, .here i => args i

/-- The identity substitution at shape `Γ`. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst Γ Γ :=
  (fun ⦃β⦄ (p : Γ ∋ β) => Expr.η p)

/-- Three-way dispatch of a slot of `Γ ⋈ Δ ⋈ Ξ`, used by `Subst.act`: the
prefix `Γ`, the substitution domain `Δ`, or the current depth `Ξ`. -/
inductive LeftMiddleRight {C : Carrier} (Γ Δ Ξ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the prefix `Γ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `Δ`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the current depth `Ξ`. -/
  | right (q : Ξ ∋ α)

/-- Dispatching a `Γ ⋈ Δ ⋈ Ξ`-slot into its source: prefix `Γ`, substitution
domain `Δ`, or current depth `Ξ`. -/
def Subst.threeway {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    {α} (p : (Γ ⋈ Δ ⋈ Ξ) ∋ α) : LeftMiddleRight Γ Δ Ξ α :=
  Proper.classify (Γ ⋈ Δ) _ p
    (fun q => Proper.classify Γ _ q .left .middle)
    .right

/-- Embed a classified site back into `Γ ⋈ Δ ⋈ Ξ`. -/
def Subst.reinject {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α} :
  LeftMiddleRight Γ Δ Ξ α → (Γ ⋈ Δ ⋈ Ξ) ∋ α
  | .left x => Proper.inl _ (Proper.inl _ x)
  | .middle x => Proper.inl (Γ ⋈ Δ) (Proper.inr Γ x)
  | .right x => Proper.inr _ x

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.threeway`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.isReinject {C : Carrier} {Γ Δ Ξ : Shape C}
      [Proper Δ] [Proper Ξ] {α}
      (x : (Γ ⋈ Δ ⋈ Ξ) ∋ α) :
    ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases Proper.cover (Γ ⋈ Δ) x with ⟨x, h_x⟩ | ⟨y, h_y⟩
  · exact ⟨.right x, h_x⟩
  · rcases Proper.cover Γ y with ⟨z, h_z⟩ | ⟨w, h_w⟩
    · subst h_y
      exact ⟨.middle z, by rw [h_z]; rfl⟩
    · subst h_y
      exact ⟨.left w, by rw [h_w]; rfl⟩

/-- Classifying a concrete right-injected `Ξ` head returns the right site. -/
@[simp] theorem Subst.threeway_inr {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (Proper.inr (Γ ⋈ Δ) x) = .right x
  := by
  unfold threeway
  rw [Proper.classify_inr]

/-- Classifying a concrete middle-domain head returns the middle site. -/
@[simp] theorem Subst.threeway_inl_dom {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (Proper.inl (Γ ⋈ Δ) ((Proper.inr Γ) x)) = .middle x
  := by
  unfold threeway
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying a concrete left-prefix head returns the left site. -/
@[simp] theorem Subst.threeway_inl_pre {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (Proper.inl (Γ ⋈ Δ) (Proper.inl Γ x)) = .left x
  := by
  unfold threeway
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- The identity instantiation for the one-position telescope `⌊α⌋`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {C : Carrier} (Δ : Shape C) (α : C.Arity) : Subst ⌊α⌋ (Δ ⋈ ⌊α⌋) :=
  Subst.fromArgs α (Δ ⋈ ⌊α⌋) (fun i => Expr.η (.here i))


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `Φ`.  Uses
`Proper.classify` for the `Φ`/below-`Φ` dispatch and `Subst.threeway` for
the `Γ`/`Δ` dispatch.  All renamings used to rebuild new heads in the
target come from `[Proper Φ]` / `[Proper Ξ]`. -/
def Subst.act {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Ξ))
    (Φ : Shape C) [Proper Φ] :
    Expr (Γ ⋈ Δ ⋈ Φ) → Expr (Γ ⋈ Ξ ⋈ Φ)
  | .ap (α := α) x args =>
      match threeway x with
      |.right x =>
          .ap (Proper.inr _ x)
            (fun i => σ.act (Φ ∷ i.arity) (args i))
      | .middle z =>
          act (Subst.fromArgs α (Γ ⋈ Ξ ⋈ Φ)
                (fun i => σ.act (Φ ∷ i.arity) (args i))) Shape.nil (σ z)
      | .left z =>
          .ap
            (Proper.inl _ (Proper.inl _ z))
            (fun i => σ.act (Φ ∷ i.arity) (args i))
termination_by e =>
  ((⟨Δ.toList⟩ : ListArity C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg x args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subArity z
         exact ListArity.Lt.step β h_mem _ h_sub))

/-- The ground substitution action `σ.act Shape.nil e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ Shape.nil e

/-- Substitution-level composition.  First substitute with `σ`, producing
expressions over `Γ ⋈ Θ`; then act on each filler with `θ`, producing
expressions over `Γ ⋈ Ξ`. -/
def Subst.comp {C : Carrier} {Γ Δ Θ Ξ : Shape C}
    [Proper Θ] [Proper Ξ]
    (σ : Subst Δ (Γ ⋈ Θ))
    (θ : Subst Θ (Γ ⋈ Ξ)) :
    Subst Δ (Γ ⋈ Ξ) :=
  (fun ⦃β⦄ x => θ.act ⌊β⌋ (σ x))
