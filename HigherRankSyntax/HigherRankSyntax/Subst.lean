import HigherRankSyntax.Expr
import HigherRankSyntax.ProperTele

/-!
# Substitution

`Subst C pre dom cod` (with `[Proper dom]` `[Proper cod]` in
scope) carries one field, `sub`, mapping each `dom`-slot to an
expression in `pre ⧺ cod`.

`Subst.act σ τ` applies the substitution `σ` to an expression at depth
`τ : Shape C` (with `[Proper τ]`).  It dispatches each head slot with
`Proper.classify` (τ-side vs. below τ) and then `Subst.classifyDom`
(pre vs. dom); pre-slots reinject into the target via `Proper.inl`.

`Subst.classifyDom` and `Subst.weakenCod` are *projections* through
the `[Proper dom]` and `[Proper cod]` instances, not struct
fields — they are determined by the structural data on dom and cod.
-/


/-- A slot of `dom` witnesses that some `β ∈ dom.toList` has the slot's arity as
a sub-arity. -/
theorem SlotAt.subWitness {C : Carrier} :
    ∀ {dom : List C.Arity} {α : C.Arity}, ListSlotAt dom α →
      ∃ β, β ∈ dom ∧ Carrier.Sub α β
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

/-- A substitution record.  Source shape is `pre ⧺ dom`, target is
`pre ⧺ cod`.  The `sub` field is the only data; slot dispatch and
pre-weakening are derived from `[Proper dom]` and `[Proper cod]`
at the operations that need them (see `Subst.classifyDom`,
`Subst.weakenCod`, `Subst.act`). -/
structure Subst (C : Carrier) (dom cod : Shape C) : Type where
  sub : ∀ {α : C.Arity}, dom ∋ α → Expr (cod ∷ α)

instance {C : Carrier} {dom cod : Shape C} :
    CoeFun (Subst C dom cod)
      (fun _ => ∀ {α : C.Arity}, dom ∋ α → Expr (cod ∷ α)) where
  coe := Subst.sub

/-- Dispatching a slot of `pre ⧺ dom` into pre vs dom.  Returned by
`Subst.classifyDom`. -/
inductive LeftRight {C : Carrier} (Γ Δ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the left summand. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the right summand. -/
  | right (q : Δ ∋ α)

/-- Three-way dispatch of a slot of `pre ⧺ dom ⧺ τ`, used by `Subst.act`.
The cases record whether the head is already under the current depth `τ`,
is a substitutable `dom`-slot, or is an untouched `pre`-slot. -/
inductive LeftMiddleRight {C : Carrier} (Γ Δ Ξ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the current depth `τ`. -/
  | left (q : Γ ∋ α)
  /-- The slot belongs to the substitution domain `dom`. -/
  | middle (q : Δ ∋ α)
  /-- The slot belongs to the untouched prefix `pre`. -/
  | right (q : Ξ ∋ α)

/-- Dispatching a `pre ⧺ dom`-slot into pre vs dom, via `[Proper dom]`. -/
def classifyLeftRight {C : Carrier} {Γ Δ : Shape C} [Proper Δ]
    {α : C.Arity} (p : Γ ⧺ Δ ∋ α) : LeftRight Γ Δ α :=
  Proper.classify Γ (LeftRight Γ Δ α) p .right .left

/-- Dispatching a `pre ⧺ dom ⧺ τ`-slot into its mathematical source:
current depth, substitution domain, or untouched prefix. -/
def Subst.classifySite {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    {α : C.Arity} (p : Γ ⧺ Δ ⧺ Ξ ∋ α) : LeftMiddleRight Γ Δ Ξ α :=
  Proper.classify (Γ ⧺ Δ) _ p
    .right
    (fun q => Proper.classify Γ _ q .middle .left)

/-- Embed a classified source site back into `pre ⧺ dom ⧺ τ`. -/
def Subst.reinject {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} :
    LeftMiddleRight Γ Δ Ξ α → Γ ⧺ Δ ⧺ Ξ ∋ α
  | .left x => Proper.inl _ (Proper.inl _ x)
  | .middle x => Proper.inl (Γ ⧺ Δ) (Proper.inr Γ x)
  | .right x => Proper.inr _ x

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.classifySite`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.coverSite {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity}
    (p : Γ ⧺ Δ ⧺ Ξ ∋ α) :
    ∃ site : LeftMiddleRight Γ Δ Ξ α, p = Subst.reinject site
  := by
  rcases Proper.cover (Γ ⧺ Δ) p with ⟨x, h_x⟩ | ⟨y, h_y⟩
  · exact ⟨.right x, h_x⟩
  · rcases Proper.cover Γ y with ⟨z, h_z⟩ | ⟨w, h_w⟩
    · subst h_y
      exact ⟨.middle z, by rw [h_z]; rfl⟩
    · subst h_y
      exact ⟨.left w, by rw [h_w]; rfl⟩

/-- Classifying an embedded `τ`-site returns the same `τ`-site. -/
theorem Subst.classifySite_right {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Ξ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      (Subst.reinject (.right x)) = .right x
  := by
  unfold Subst.classifySite Subst.reinject
  rw [Proper.classify_inr]

/-- Classifying an embedded `dom`-site returns the same `dom`-site. -/
theorem Subst.classifySite_middle {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Δ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      (Subst.reinject (.middle x)) = .middle x
  := by
  unfold Subst.classifySite Subst.reinject
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying an embedded `pre`-site returns the same `pre`-site. -/
theorem  Subst.classifySite_left {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Γ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      (Subst.reinject (.left x)) = .left x
  := by
  unfold Subst.classifySite Subst.reinject
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- Classifying a concrete right-injected `τ` head returns `SubstSite.tau`. -/
theorem Subst.classifySite_inr {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Ξ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      ((Proper.inr (Γ ⧺ Δ)) x) = .right x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inr]

/-- Classifying a concrete dom head returns `SubstSite.dom`. -/
theorem Subst.classifySite_inl_dom {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Δ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      ((Proper.inl (Γ ⧺ Δ)) ((Proper.inr Γ) x)) = .middle x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying a concrete pre head returns `SubstSite.pre`. -/
theorem Subst.classifySite_inl_pre {C : Carrier} {Γ Δ Ξ : Shape C}
    [Proper Δ] [Proper Ξ] {α : C.Arity} (x : Γ ∋ α) :
    Subst.classifySite (Γ := Γ) (Δ := Δ) (Ξ := Ξ)
      ((Proper.inl (Γ ⧺ Δ)) ((Proper.inl Γ) x)) = .left x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- Embedding `pre` into `pre ⧺ cod`, via `[Proper cod]`. -/
-- TODO: unecessary crap
def Subst.weakenCod {C : Carrier} {Γ Δ : Shape C} [Proper Δ] : Γ →ʳ Γ ⧺ Δ :=
  Proper.inl Γ

/-! ### Instantiation Subst

The `Subst.inst` constructor turns a "kit" (one expression per binder of an
arity α, in some target context) into a Subst with domain `⌊α⌋`.
Used inside `Subst.act`'s dom branch to act on a substituted expression
with the recursive arg results as fillers. -/

/-- Subst constructor from a slot-keyed function. -/
-- TODO: unecessary crap
abbrev Subst.inst {C : Carrier} (Δ : Shape C) {Ξ : Shape C} (f : ∀ {α : C.Arity}, Δ ∋ α → Expr (Ξ ∷ α)) : Subst C Δ Ξ where
  sub := f

/-- The identity instantiation for the one-binder telescope `⌊α⌋`,
with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {C : Carrier} (Δ : Shape C) (α : C.Arity) :
    Subst C ⌊α⌋ (Δ ⧺ ⌊α⌋) :=
  Subst.inst _ (fun q => match q with | .here i => Expr.η (.here i))

/-! ### Kleisli ↔ Subst correspondence

A Kleisli map of the syntax relative monad is `∀ {α}, (Γ ∋ α) → Expr (Δ ∷ α)`.
With cons-style telescopes and `pre := Shape.nil`, the correspondence to
`Subst` is *definitional*: `Shape.nil ⧺ X = X` by Tele's strict left unit. -/

/-- Wrap a Kleisli map as a `Subst` with empty `pre`. -/
-- TODO unecessary crap
def toSubst {C : Carrier} {Γ Δ : Shape C} (f : ∀ {α : C.Arity}, Γ ∋ α → Expr (Δ ∷ α)) : Subst C Γ Δ where
  sub := f

@[simp] theorem toSubst_sub {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, Γ ∋ α → Expr (Δ ∷ α))
    {α : C.Arity} (p : Γ ∋ α) :
    (toSubst f).sub p = f p := rfl

/-- The identity substitution at shape `Γ` — `toSubst` of the unit `Expr.η`. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst C Γ Γ :=
  toSubst (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)

/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `τ`.  Uses
`Proper.classify` for the τ/below-τ dispatch and `σ.classifyDom` for
the pre/dom dispatch.  All renamings used to rebuild new heads in the
target come from `[Proper τ]` / `[Proper cod]`. -/
def Subst.act {C : Carrier} : {Γ Δ Ξ : Shape C} →
    [Proper Δ] → [Proper Ξ] →
    (σ : Subst C Δ (Γ ⧺ Ξ)) →
    (τ : Shape C) → [Proper τ] →
    Expr (Γ ⧺ Δ ⧺ τ) → Expr (Γ ⧺ Ξ ⧺ τ)
  | Γ, Δ, Ξ, _, _, σ, τ, _, .ap (α := α) p args =>
      match Subst.classifySite p with
      |.right x =>
          .ap (Proper.inr (Γ ⧺ Ξ) x)
            (fun i => σ.act (τ ∷ i.arity) (args i))
      | .middle z =>
          (Subst.inst ⌊α⌋ (fun q => match q with
            -- TODO: this is a real problem here
            | .here i => σ.act (τ ∷ i.arity) (args i))).act Shape.nil (σ z)
      | .left z =>
          .ap
            (Proper.inl (Γ ⧺ Ξ)
              ((Subst.weakenCod σ) z))
            (fun i => σ.act (τ ∷ i.arity) (args i))
termination_by Γ Δ _ _ _ _ _ _ e =>
  ((⟨dom.toList⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg p args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness z
         exact DomLt.step β h_mem _ h_sub))

/-- The ground substitution action `σ.act Shape.nil e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ Shape.nil e

/-- Substitution-level composition.  First substitute with `σ`, producing
expressions over `pre ⧺ mid`; then act on each filler with `θ`, producing
expressions over `pre ⧺ cod`. -/
def Subst.comp {C : Carrier} {pre dom mid cod : Shape C}
    [Proper mid] [Proper cod]
    (σ : Subst C dom (pre ⧺ mid))
    (θ : Subst C mid (pre ⧺ cod)) :
    Subst C dom (pre ⧺ cod) :=
  Subst.inst dom (fun {β} x => θ.act ⌊β⌋ (σ.sub x))

/-- Kleisli composition of two Kleisli maps via `Subst.act`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ξ ∷ β)) :
    ∀ {β : C.Arity}, Γ ∋ β → Expr (Ξ ∷ β) :=
  fun {β} p => (toSubst g).act ⌊β⌋ (f p)
