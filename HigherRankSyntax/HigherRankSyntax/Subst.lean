import HigherRankSyntax.Expr
import HigherRankSyntax.ProperTele

/-!
# Substitution

`Subst C dom cod` maps each `dom`-slot `i` to an expression over `cod ⋈ i.arity`.

`Subst.act σ τ` applies the substitution `σ` to an expression at depth
`τ : Shape C` (with `[Proper τ]`).  The action is still prefix-aware: if
`σ : Subst C Δ (Γ ⋈ Ξ)`, then it transforms
`Expr ((Γ ⋈ Δ) ⋈ τ)` into `Expr ((Γ ⋈ Ξ) ⋈ τ)`.  The data no longer stores the
prefix separately; the operation chooses that decomposition when acting.

`Subst.threeway` is the proof-facing head classifier for this action:
right/current-depth heads are preserved, middle/domain heads fire `σ`, and
left/prefix heads are preserved by direct reinjection.
-/


/-- A slot of `dom` witnesses that some `β ∈ dom.toList` has the slot's arity as
a sub-arity. -/
theorem SlotAt.subWitness {C : Carrier} :
  ∀ {Γ : List C.Arity} {α : C.Arity}, ListSlotAt Γ α → ∃ β, β ∈ Γ ∧ Carrier.Sub α β
  | _ :: _, _, .here i  => ⟨_, List.Mem.head _, ⟨i, rfl⟩⟩
  | _ :: _, _, .there p => by
      obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness p
      exact ⟨β, List.Mem.tail _ h_mem, h_sub⟩

/-- One-step WF relation on `List C.Arity`: `[β] ≺ dom` iff `β` is a sub-arity of
some `αⱼ ∈ dom`.  Used as the first component of `Subst.act`'s lex termination. -/
inductive DomLt {C : Carrier} : List C.Arity → List C.Arity → Prop
  | step {dom : List C.Arity} (αⱼ : C.Arity) (h_in : αⱼ ∈ dom)
         (β : C.Arity) (h_sub : Carrier.Sub β αⱼ) :
         DomLt [β] dom

private theorem DomLt.acc_singleton {C : Carrier} (α : C.Arity)
    (hα : Acc (Carrier.Sub (C := C)) α) :
    Acc (DomLt (C := C)) [α] := by
  induction hα with
  | intro α _ ih =>
      refine ⟨_, ?_⟩
      intro dom' hdom'
      cases hdom' with
      | step αⱼ h_in β h_sub =>
          cases h_in with
          | head         => exact ih β h_sub
          | tail _ h_nil => cases h_nil

private theorem DomLt.wf {C : Carrier} : WellFounded (DomLt (C := C)) := by
  refine ⟨fun dom => ?_⟩
  refine ⟨_, ?_⟩
  intro dom' hdom'
  cases hdom' with
  | step _ _ β _ => exact DomLt.acc_singleton β (C.subWf.apply β)

/-- Wrapper carrying the `DomLt` well-founded relation on `List C.Arity`. -/
structure DomMeasure (C : Carrier) : Type where
  unwrap : List C.Arity

instance (C : Carrier) : WellFoundedRelation (DomMeasure C) where
  rel := fun a b => DomLt a.unwrap b.unwrap
  wf := InvImage.wf DomMeasure.unwrap DomLt.wf

/-- A substitution record from a domain shape into a full target shape.
The `sub` field is the only data; prefix preservation is not part of the
record and is instead selected by `Subst.act` when the target is decomposed
as `Γ ⋈ Ξ`. -/
abbrev Subst (C : Carrier) (dom cod : Shape C) :=
  ∀ {α : C.Arity}, dom ∋ α → Expr (cod ∷ α)

/-- Package the argument family of an `α`-ary application as a substitution
whose domain is the singleton telescope `⌊α⌋`. -/
def Subst.fromArgs {C : Carrier}
    (α : C.Arity) (Γ : Shape C)
    (args : Expr.Args Γ α) :
    Subst C ⌊α⌋ Γ :=
  fun | .here i => args i

/-- Read a singleton-domain substitution as the argument family it contains. -/
def Subst.toArgs {C : Carrier} {α : C.Arity} {Γ : Shape C}
    (σ : Subst C ⌊α⌋ Γ) :
    Expr.Args Γ α :=
  fun i => σ (.here i)

@[simp]
theorem Subst.fromArgs_apply {C : Carrier}
    {α : C.Arity} {Γ : Shape C}
    (args : Expr.Args Γ α) (i : C.Binder α) :
    Subst.fromArgs α Γ args (.here i) = args i :=
  rfl

@[simp]
theorem Subst.toArgs_apply {C : Carrier}
    {α : C.Arity} {Γ : Shape C}
    (σ : Subst C ⌊α⌋ Γ) (i : C.Binder α) :
    Subst.toArgs σ i = σ (.here i) :=
  rfl

@[simp]
theorem Subst.toArgs_fromArgs {C : Carrier}
    {α : C.Arity} {Γ : Shape C}
    (args : Expr.Args Γ α) :
    Subst.toArgs (Subst.fromArgs α Γ args) = args := by
  funext i
  rfl

/-- Singleton-domain substitutions are extensional in their underlying
argument families. -/
theorem Subst.fromArgs_toArgs {C : Carrier}
    {α : C.Arity} {Γ : Shape C}
    (σ : Subst C ⌊α⌋ Γ) :
    (fun {β : C.Arity} (q : ⌊α⌋ ∋ β) =>
      Subst.fromArgs α Γ (Subst.toArgs σ) q)
    =
    (fun {β : C.Arity} (q : ⌊α⌋ ∋ β) => σ q) := by
  funext β q
  cases q with
  | here i => rfl
  | there q => nomatch q

/-- The identity substitution at shape `Γ`. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst C Γ Γ :=
  (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)

/-- Dispatching a slot of `pre ⋈ dom` into pre vs dom.  Returned by
`Subst.classifyDom`. -/
inductive LeftRight {C : Carrier} (Γ Δ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the left summand. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the right summand. -/
  | right (q : Δ ∋ α)

/-- Three-way dispatch of a slot of `(pre ⋈ dom) ⋈ τ`, used by `Subst.act`.
The cases record whether the head is already under the current depth `τ`,
is a substitutable `dom`-slot, or is an untouched `pre`-slot. -/
inductive LeftMiddleRight {C : Carrier} (Γ Δ Ξ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the current depth `τ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `dom`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the untouched prefix `pre`. -/
  | right (q : Ξ ∋ α)

/-- Dispatching a `pre ⋈ dom`-slot into pre vs dom, via `[Proper dom]`. -/
def classifyLeftRight {C : Carrier} {Γ Δ : Shape C} [Proper Δ]
    {α : C.Arity} (p : (Γ ⋈ Δ) ∋ α) : LeftRight Γ Δ α :=
  Proper.classify Γ (LeftRight Γ Δ α) p .right .left

/-- Dispatching a `(pre ⋈ dom) ⋈ τ`-slot into its mathematical source:
current depth, substitution domain, or untouched prefix. -/
def Subst.threeway {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    {α : C.Arity} (p : ((Γ ⋈ Δ) ⋈ Ξ) ∋ α) : LeftMiddleRight Γ Δ Ξ α :=
  Proper.classify (Γ ⋈ Δ) _ p
    .right
    (fun q => Proper.classify Γ _ q .middle .left)

/-- Embed a classified source site back into `(pre ⋈ dom) ⋈ τ`. -/
def Subst.reinject {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} :
  LeftMiddleRight Γ Δ Ξ α → ((Γ ⋈ Δ) ⋈ Ξ) ∋ α
  | .left x => Proper.inl _ (Proper.inl _ x)
  | .middle x => Proper.inl (Γ ⋈ Δ) (Proper.inr Γ x)
  | .right x => Proper.inr _ x

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.threeway`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.isReinject {C : Carrier} {Γ Δ Ξ : Shape C}
      [Proper Δ] [Proper Ξ] {α : C.Arity}
      (x : ((Γ ⋈ Δ) ⋈ Ξ) ∋ α) :
    ∃ y : LeftMiddleRight Γ Δ Ξ α, x = reinject y
  := by
  rcases Proper.cover (Γ ⋈ Δ) x with ⟨x, h_x⟩ | ⟨y, h_y⟩
  · exact ⟨.right x, h_x⟩
  · rcases Proper.cover Γ y with ⟨z, h_z⟩ | ⟨w, h_w⟩
    · subst h_y
      exact ⟨.middle z, by rw [h_z]; rfl⟩
    · subst h_y
      exact ⟨.left w, by rw [h_w]; rfl⟩

/-- Classifying an embedded `τ`-site returns the same `τ`-site. -/
theorem Subst.threeway_right {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (reinject (.right x)) = .right x
  := by
  unfold Subst.threeway Subst.reinject
  rw [Proper.classify_inr]

/-- Classifying an embedded `dom`-site returns the same `dom`-site. -/
theorem Subst.threeway_middle {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (reinject (.middle x)) = .middle x
  := by
  unfold threeway reinject
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying an embedded `pre`-site returns the same `pre`-site. -/
theorem  Subst.threeway_left {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (reinject (.left x)) = .left x
  := by
  unfold threeway reinject
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- Classifying a concrete right-injected `τ` head returns the right site. -/
theorem Subst.threeway_inr {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Ξ ∋ α) :
  threeway (Γ := Γ) (Δ := Δ) (Proper.inr (Γ ⋈ Δ) x) = .right x
  := by
  unfold threeway
  rw [Proper.classify_inr]

/-- Classifying a concrete middle-domain head returns the middle site. -/
theorem Subst.threeway_inl_dom {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Δ ∋ α) :
  threeway (Γ := Γ) (Ξ := Ξ) (Proper.inl (Γ ⋈ Δ) ((Proper.inr Γ) x)) = .middle x
  := by
  unfold threeway
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying a concrete left-prefix head returns the left site. -/
theorem Subst.threeway_inl_pre {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Γ ∋ α) :
  threeway (Δ := Δ) (Ξ := Ξ) (Proper.inl (Γ ⋈ Δ) (Proper.inl Γ x)) = .left x
  := by
  unfold threeway
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- The identity instantiation for the one-binder telescope `⌊α⌋`, with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {C : Carrier} (Δ : Shape C) (α : C.Arity) : Subst C ⌊α⌋ (Δ ⋈ ⌊α⌋) :=
  fun | .here i => Expr.η (.here i)


/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `τ`.  Uses
`Proper.classify` for the τ/below-τ dispatch and `σ.classifyDom` for
the pre/dom dispatch.  All renamings used to rebuild new heads in the
target come from `[Proper τ]` / `[Proper cod]`. -/
def Subst.act {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ]
    (σ : Subst C Δ (Γ ⋈ Ξ))
    (τ : Shape C) [Proper τ] :
    Expr ((Γ ⋈ Δ) ⋈ τ) → Expr ((Γ ⋈ Ξ) ⋈ τ)
  | .ap (α := α) x args =>
      match threeway x with
      |.right x =>
          .ap (Proper.inr _ x)
            (fun i => σ.act (τ ∷ i.arity) (args i))
      | .middle z =>
          act (Subst.fromArgs α ((Γ ⋈ Ξ) ⋈ τ)
              (fun i => σ.act (τ ∷ i.arity) (args i)))
            Shape.nil (σ z)
      | .left z =>
          .ap
            (Proper.inl _ (Proper.inl _ z))
            (fun i => σ.act (τ ∷ i.arity) (args i))
termination_by e =>
  ((⟨Δ.toList⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg x args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness z
         exact DomLt.step β h_mem _ h_sub))

/-- The ground substitution action `σ.act Shape.nil e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ Shape.nil e

/-- Postcompose a substitution `κ` with the action induced by `σ`, at passive
depth `Ω`.  Pointwise, every filler of `κ` is transformed by acting with `σ`.

The old ordinary substitution composition is the `Ω = Shape.nil`
specialization `Subst.comp θ Shape.nil σ`: first use `σ`, then postcompose its
fillers by `θ`. -/
def Subst.comp {C : Carrier} {Γ Δ Ξ Θ : Shape C}
    [Proper Δ] [Proper Ξ] [Proper Θ]
    (σ : Subst C Δ (Γ ⋈ Ξ))
    (Ω : Shape C) [Proper Ω]
    (κ : Subst C Θ (Γ ⋈ Δ ⋈ Ω)) :
    Subst C Θ (Γ ⋈ Ξ ⋈ Ω) :=
  fun {β} x => σ.act (Ω ∷ β) (κ x)

/-- Kleisli composition of substitutions: first substitute with `σ`, producing
expressions over `Γ ⋈ Θ`; then substitute the remaining `Θ`-variables with
`θ`, producing expressions over `Γ ⋈ Ξ`.

This is the empty-depth specialization of `Subst.comp`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Θ Ξ : Shape C}
    [Proper Δ] [Proper Θ] [Proper Ξ]
    (σ : Subst C Δ (Γ ⋈ Θ))
    (θ : Subst C Θ (Γ ⋈ Ξ)) :
    Subst C Δ (Γ ⋈ Ξ) :=
  Subst.comp θ Shape.nil σ
