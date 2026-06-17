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

/-- Dispatching a slot of `pre ⧺ dom` into pre vs dom.  Returned by
`Subst.classifyDom`. -/
inductive PreOrDom {C : Carrier} (pre dom : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to `pre`. -/
  | pre (q : pre ∋ α)
  /-- The slot belongs to `dom`. -/
  | dom (q : dom ∋ α)

/-- Three-way dispatch of a slot of `pre ⧺ dom ⧺ τ`, used by `Subst.act`.
The cases record whether the head is already under the current depth `τ`,
is a substitutable `dom`-slot, or is an untouched `pre`-slot. -/
inductive SubstSite {C : Carrier} (pre dom τ : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to the current depth `τ`. -/
  | tau (q : τ ∋ α)
  /-- The slot belongs to the substitution domain `dom`. -/
  | dom (q : dom ∋ α)
  /-- The slot belongs to the untouched prefix `pre`. -/
  | pre (q : pre ∋ α)

/-- A substitution record.  Source shape is `pre ⧺ dom`, target is
`pre ⧺ cod`.  The `sub` field is the only data; slot dispatch and
pre-weakening are derived from `[Proper dom]` and `[Proper cod]`
at the operations that need them (see `Subst.classifyDom`,
`Subst.weakenCod`, `Subst.act`). -/
structure Subst (C : Carrier) (pre dom cod : Shape C) : Type where
  sub : ∀ {α : C.Arity}, dom ∋ α → Expr (pre ⧺ cod ∷ α)

instance {C : Carrier} {pre dom cod : Shape C} :
    CoeFun (Subst C pre dom cod)
      (fun _ => ∀ {α : C.Arity}, dom ∋ α → Expr (pre ⧺ cod ∷ α)) :=
  ⟨Subst.sub⟩

/-- Dispatching a `pre ⧺ dom`-slot into pre vs dom, via `[Proper dom]`. -/
def Subst.classifyDom {C : Carrier} {pre dom cod : Shape C}
    [Proper dom] (_σ : Subst C pre dom cod)
    {α : C.Arity} (p : pre ⧺ dom ∋ α) : PreOrDom pre dom α :=
  Proper.classify pre _ p PreOrDom.dom PreOrDom.pre

/-- Dispatching a `pre ⧺ dom ⧺ τ`-slot into its mathematical source:
current depth, substitution domain, or untouched prefix. -/
def Subst.classifySite {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ]
    {α : C.Arity} (p : pre ⧺ dom ⧺ τ ∋ α) : SubstSite pre dom τ α :=
  Proper.classify (pre ⧺ dom) _ p
    SubstSite.tau
    (fun q =>
      Proper.classify pre _ q
        SubstSite.dom
        SubstSite.pre)

/-- Embed a classified source site back into `pre ⧺ dom ⧺ τ`. -/
def Subst.embedSource {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} :
    SubstSite pre dom τ α → pre ⧺ dom ⧺ τ ∋ α
  | .tau x => (Proper.inr (pre ⧺ dom)) x
  | .dom x => (Proper.inl (pre ⧺ dom)) ((Proper.inr pre) x)
  | .pre x => (Proper.inl (pre ⧺ dom)) ((Proper.inl pre) x)

/-- Every source slot is the embedding of a unique-looking `SubstSite`.
This is the proof-facing inverse of `Subst.classifySite`; use it to replace
nested `Proper.cover` splits. -/
theorem Subst.coverSite {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity}
    (p : pre ⧺ dom ⧺ τ ∋ α) :
    ∃ site : SubstSite pre dom τ α, p = Subst.embedSource site
  := by
  rcases Proper.cover (pre ⧺ dom) p with ⟨x, h_x⟩ | ⟨y, h_y⟩
  · exact ⟨.tau x, h_x⟩
  · rcases Proper.cover pre y with ⟨z, h_z⟩ | ⟨w, h_w⟩
    · subst h_y
      exact ⟨.dom z, by rw [h_z]; rfl⟩
    · subst h_y
      exact ⟨.pre w, by rw [h_w]; rfl⟩

/-- Classifying an embedded `τ`-site returns the same `τ`-site. -/
theorem Subst.classifySite_tau {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : τ ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      (Subst.embedSource (.tau x)) = SubstSite.tau x
  := by
  unfold Subst.classifySite Subst.embedSource
  rw [Proper.classify_inr]

/-- Classifying an embedded `dom`-site returns the same `dom`-site. -/
theorem Subst.classifySite_dom {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : dom ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      (Subst.embedSource (.dom x)) = SubstSite.dom x
  := by
  unfold Subst.classifySite Subst.embedSource
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying an embedded `pre`-site returns the same `pre`-site. -/
theorem Subst.classifySite_pre {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : pre ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      (Subst.embedSource (.pre x)) = SubstSite.pre x
  := by
  unfold Subst.classifySite Subst.embedSource
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- Classifying a concrete right-injected `τ` head returns `SubstSite.tau`. -/
theorem Subst.classifySite_inr {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : τ ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      ((Proper.inr (pre ⧺ dom)) x) = SubstSite.tau x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inr]

/-- Classifying a concrete dom head returns `SubstSite.dom`. -/
theorem Subst.classifySite_inl_dom {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : dom ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      ((Proper.inl (pre ⧺ dom)) ((Proper.inr pre) x)) = SubstSite.dom x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inl]
  rw [Proper.classify_inr]

/-- Classifying a concrete pre head returns `SubstSite.pre`. -/
theorem Subst.classifySite_inl_pre {C : Carrier} {pre dom τ : Shape C}
    [Proper dom] [Proper τ] {α : C.Arity} (x : pre ∋ α) :
    Subst.classifySite (pre := pre) (dom := dom) (τ := τ)
      ((Proper.inl (pre ⧺ dom)) ((Proper.inl pre) x)) = SubstSite.pre x
  := by
  unfold Subst.classifySite
  rw [Proper.classify_inl]
  rw [Proper.classify_inl]

/-- Embedding `pre` into `pre ⧺ cod`, via `[Proper cod]`. -/
def Subst.weakenCod {C : Carrier} {pre dom cod : Shape C}
    [Proper cod] (_σ : Subst C pre dom cod) :
    pre →ʳ pre ⧺ cod :=
  Proper.inl pre

/-! ### Instantiation Subst

The `Subst.inst` constructor turns a "kit" (one expression per binder of an
arity α, in some target context) into a Subst with domain `⌊α⌋`.
Used inside `Subst.act`'s dom branch to act on a substituted expression
with the recursive arg results as fillers. -/

/-- Subst constructor from a slot-keyed function. -/
abbrev Subst.inst {C : Carrier} {pre : Shape C} (dom : Shape C) {cod : Shape C}
    (f : ∀ {α : C.Arity}, dom ∋ α → Expr (pre ⧺ cod ∷ α)) :
    Subst C pre dom cod where
  sub := f

/-- The identity instantiation for the one-binder telescope `⌊α⌋`,
with an arbitrary fixed prefix `Δ`. -/
def Subst.instId {C : Carrier} (Δ : Shape C) (α : C.Arity) :
    Subst C Δ ⌊α⌋ ⌊α⌋ :=
  Subst.inst ⌊α⌋ (fun q => match q with
    | .here i => Expr.η (.here i))

/-! ### Kleisli ↔ Subst correspondence

A Kleisli map of the syntax relative monad is `∀ {α}, (Γ ∋ α) → Expr (Δ ∷ α)`.
With cons-style telescopes and `pre := Shape.nil`, the correspondence to
`Subst` is *definitional*: `Shape.nil ⧺ X = X` by Tele's strict left unit. -/

/-- Wrap a Kleisli map as a `Subst` with empty `pre`. -/
def toSubst {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, Γ ∋ α → Expr (Δ ∷ α)) :
    Subst C Shape.nil Γ Δ where
  sub := f

@[simp] theorem toSubst_sub {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, Γ ∋ α → Expr (Δ ∷ α))
    {α : C.Arity} (p : Γ ∋ α) :
    (toSubst f).sub p = f p := rfl

/-- The identity substitution at shape `Γ` — `toSubst` of the unit `Expr.η`. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst C Shape.nil Γ Γ :=
  toSubst (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)

/-! ### The substitution action -/

/-- Apply the substitution `σ` to an expression at depth `τ`.  Uses
`Proper.classify` for the τ/below-τ dispatch and `σ.classifyDom` for
the pre/dom dispatch.  All renamings used to rebuild new heads in the
target come from `[Proper τ]` / `[Proper cod]`. -/
def Subst.act {C : Carrier} : {pre dom cod : Shape C} →
    [Proper dom] → [Proper cod] →
    (σ : Subst C pre dom cod) →
    (τ : Shape C) → [Proper τ] →
    Expr (pre ⧺ dom ⧺ τ) → Expr (pre ⧺ cod ⧺ τ)
  | pre, dom, cod, _, _, σ, τ, _, .ap (α := α) p args =>
      match Subst.classifySite p with
      | SubstSite.tau x =>
          .ap (Proper.inr (pre ⧺ cod) x)
            (fun i => σ.act (τ ∷ i.arity) (args i))
      | SubstSite.dom z =>
          (Subst.inst ⌊α⌋ (fun q => match q with
            | .here i => σ.act (τ ∷ i.arity) (args i))).act Shape.nil (σ z)
      | SubstSite.pre z =>
          .ap
            (Proper.inl (pre ⧺ cod)
              ((Subst.weakenCod σ) z))
            (fun i => σ.act (τ ∷ i.arity) (args i))
termination_by pre dom _ _ _ _ _ _ e =>
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
    (σ : Subst C pre dom mid)
    (θ : Subst C pre mid cod) :
    Subst C pre dom cod :=
  Subst.inst dom (fun {β} x => θ.act ⌊β⌋ (σ.sub x))

/-- Kleisli composition of two Kleisli maps via `Subst.act`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ξ ∷ β)) :
    ∀ {β : C.Arity}, Γ ∋ β → Expr (Ξ ∷ β) :=
  fun {β} p => (toSubst g).act ⌊β⌋ (f p)
