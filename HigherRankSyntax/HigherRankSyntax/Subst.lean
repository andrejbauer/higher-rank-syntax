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

/-- Four-way dispatch of a slot of `pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner`.
The first three carry slots of the corresponding `Shape`; the inner case
carries a `ListSlotAt inner α` — a pure list slot, not coupled to any
surrounding Shape context. -/
inductive SubstSite {C : Carrier} (pre dom outer : Shape C)
    (inner : List C.Arity) (α : C.Arity) : Type where
  /-- The slot belongs to `pre`. -/
  | pre   (q : pre ∋ α)
  /-- The slot belongs to `dom`. -/
  | dom   (q : dom ∋ α)
  /-- The slot belongs to `outer`. -/
  | outer (q : outer ∋ α)
  /-- The slot belongs to the list-shaped accumulator `inner`. -/
  | inner (q : ListSlotAt inner α)

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

/-- Dispatch a slot of `pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner` into one of four
structural sources by induction on `inner`.  The base case (`inner = []`)
uses `Proper.classify` twice; the cons case peels one slot of the underlying
list at a time. -/
def Subst.classifySlot
    {C : Carrier} {pre dom outer : Shape C} [Proper dom] [Proper outer] :
    (inner : List C.Arity) → {α : C.Arity} →
    pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner ∋ α →
    SubstSite pre dom outer inner α
  | [], _, p =>
      Proper.classify (pre ⧺ dom) _ p
        (fun x => SubstSite.outer x)
        (fun y =>
          Proper.classify pre _ y
            (fun z => SubstSite.dom z)
            (fun w => SubstSite.pre w))
  | β :: rest, _, .here i =>
      SubstSite.inner (@ListSlotAt.here C β rest i)
  | β :: rest, _, .there p =>
      match Subst.classifySlot rest p with
      | SubstSite.pre   q => SubstSite.pre q
      | SubstSite.dom   q => SubstSite.dom q
      | SubstSite.outer q => SubstSite.outer q
      | SubstSite.inner q => SubstSite.inner (@ListSlotAt.there C β _ rest q)

/-- Embed a pure `ListSlotAt inner α` slot into the inner region of any
`pre ⧺ cod ⧺ outer ⧺ Tele.ofList inner ∋ α`.  Structural recursion on the
slot — each `.here`/`.there` re-emerges at the wider underlying-list level. -/
def Subst.embedInner {C : Carrier} {pre cod outer : Shape C} :
    {inner : List C.Arity} → {α : C.Arity} →
    ListSlotAt inner α → pre ⧺ cod ⧺ outer ⧺ Tele.ofList inner ∋ α
  | _ :: _, _, .here i  => .here i
  | _ :: _, _, .there q => .there (Subst.embedInner q)

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

/-- Apply the substitution `σ` to an expression at depth split into `outer`
(any `Shape`, fixed across the recursion) and `inner` (a list-shaped
accumulator that grows by `cons` per descent level).  Uses
`Subst.classifySlot` for the four-way head dispatch. -/
def Subst.act {C : Carrier} : {pre dom cod : Shape C} →
    [Proper dom] → [Proper cod] →
    (σ : Subst C pre dom cod) →
    (outer : Shape C) → [Proper outer] →
    (inner : List C.Arity) →
    Expr (pre ⧺ dom ⧺ outer ⧺ Tele.ofList inner) →
    Expr (pre ⧺ cod ⧺ outer ⧺ Tele.ofList inner)
  | pre, dom, cod, _, _, σ, outer, _, inner, .ap (α := α) p args =>
      match Subst.classifySlot inner p with
      | SubstSite.inner y =>
          .ap (Subst.embedInner (pre := pre) (cod := cod) (outer := outer) y)
            (fun i => σ.act outer (i.arity :: inner) (args i))
      | SubstSite.outer x =>
          .ap ((Proper.inl (pre ⧺ cod ⧺ outer))
                ((Proper.inr (pre ⧺ cod)) x))
            (fun i => σ.act outer (i.arity :: inner) (args i))
      | SubstSite.dom z =>
          (Subst.inst (pre := pre ⧺ cod) (cod := outer ⧺ Tele.ofList inner)
              ⌊α⌋ (fun q => match q with
                | .here i => σ.act outer (i.arity :: inner) (args i))).act
            Shape.nil [] (σ z)
      | SubstSite.pre w =>
          .ap ((Proper.inl (pre ⧺ cod ⧺ outer))
                ((Proper.inl (pre ⧺ cod))
                  ((Proper.inl pre) w)))
            (fun i => σ.act outer (i.arity :: inner) (args i))
termination_by pre dom _ _ _ _ _ _ _ e =>
  ((⟨dom.toList⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg p args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness z
         exact DomLt.step β h_mem _ h_sub))

/-- The ground substitution action `σ.act Shape.nil [] e`, mirroring `⟦ρ⟧ʳ e`. -/
notation:60 "⟦" σ "⟧ˢ " e:61 => Subst.act σ Shape.nil [] e

/-- Kleisli composition of two Kleisli maps via `Subst.act`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Ξ : Shape C} [Proper Δ] [Proper Ξ]
    (f : ∀ {β : C.Arity}, Γ ∋ β → Expr (Δ ∷ β))
    (g : ∀ {β : C.Arity}, Δ ∋ β → Expr (Ξ ∷ β)) :
    ∀ {β : C.Arity}, Γ ∋ β → Expr (Ξ ∷ β) :=
  fun {β} p => (toSubst g).act Shape.nil [β] (f p)
