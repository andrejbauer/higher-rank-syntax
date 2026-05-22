import HigherRankSyntaxSig.Expr

/-!
# Substitution

`Subst C` encodes a Kleisli map of the syntax relative monad.  `pre` is preserved,
`dom` is replaced by `cod`.  With `dom : List C.Arity`, every Kleisli map
`Γ →ˢ Δ` corresponds to a `Subst` (take `pre := nil`, `dom` = source list,
`cod` = target list, `sub` = the map).
-/


/-- Membership in a list of arities, with binder data at the position.  Mirrors
`SlotAt`'s structure but indexed by `List C.Arity` instead of `Shape C`. -/
inductive ListSlot {C : Carrier} : List C.Arity → C.Arity → Type where
  | here  : {β : C.Arity} → {rest : List C.Arity} → (i : C.Binder β) →
            ListSlot (β :: rest) i.arity
  | there : {β : C.Arity} → {rest : List C.Arity} → {α : C.Arity} →
            (p : ListSlot rest α) → ListSlot (β :: rest) α

/-- Canonical embedding of a list-slot into the shape extended by that list. -/
def ListSlot.toSlotAt {C : Carrier} (pre : Shape C) :
    {dom : List C.Arity} → {α : C.Arity} → ListSlot dom α → (pre ⋈* dom) ∋ α
  | _, _, ListSlot.here i  => SlotAt.here i
  | _, _, ListSlot.there p => SlotAt.there (ListSlot.toSlotAt pre p)

/-- A list-slot witnesses that some `β ∈ dom` has the slot's arity as a sub-arity. -/
theorem ListSlot.subWitness {C : Carrier} :
    ∀ {dom : List C.Arity} {α : C.Arity}, ListSlot dom α →
      ∃ β, β ∈ dom ∧ Carrier.Sub α β
  | _ :: _, _, .here i  => ⟨_, List.Mem.head _, ⟨i, rfl⟩⟩
  | _ :: _, _, .there p => by
      obtain ⟨β, h_mem, h_sub⟩ := ListSlot.subWitness p
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

/-- A substitution record. -/
structure Subst (C : Carrier) where
  pre : Shape C
  dom : List C.Arity
  cod : List C.Arity
  sub : ∀ {α : C.Arity}, ListSlot dom α → Expr ((pre ⋈* cod) ⋈ α)

/-- The slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)`. -/
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → (Γ ⋈* (τ_above ++ β :: τ_below)) ∋ i.arity
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- Position of a slot in `(pre ⋈* dom) ⋈* τ`: a pre-slot, a dom-list-slot,
or a τ-binder. -/
inductive XPos {C : Carrier} (pre : Shape C) (dom : List C.Arity) :
    (τ : List C.Arity) → {α : C.Arity} →
    SlotAt ((pre ⋈* dom) ⋈* τ) α → Type where
  | pre : {τ : List C.Arity} → {α : C.Arity} → (p : pre ∋ α) →
          XPos pre dom τ (((pre ⋈* dom) ↪ʳ* τ) ((pre ↪ʳ* dom) p))
  | dom : {τ : List C.Arity} → {α : C.Arity} → (q : ListSlot dom α) →
          XPos pre dom τ (((pre ⋈* dom) ↪ʳ* τ) (ListSlot.toSlotAt pre q))
  | ext : {τ_above : List C.Arity} → {β : C.Arity} →
          {τ_below : List C.Arity} → (i : C.Binder β) →
          XPos pre dom (τ_above ++ β :: τ_below)
            (tauSlot (pre ⋈* dom) τ_above β τ_below i)

/-- Classification of a slot in `pre ⋈* dom` (i.e., below τ): either in pre or
in dom.  Two-constructor companion to `XPos`'s three; the `XPos.ext` case is
impossible below τ. -/
inductive PreOrDom {C : Carrier} (pre : Shape C) (dom : List C.Arity) :
    {α : C.Arity} → (p : (pre ⋈* dom) ∋ α) → Type where
  | pre : {α : C.Arity} → (q : pre ∋ α) → PreOrDom pre dom ((pre ↪ʳ* dom) q)
  | dom : {α : C.Arity} → (q : ListSlot dom α) →
          PreOrDom pre dom (ListSlot.toSlotAt pre q)

/-- Walk through dom: at `dom = []` the slot is in pre. -/
def classifyDom {C : Carrier} (pre : Shape C) :
    (dom : List C.Arity) → {α : C.Arity} → (p : (pre ⋈* dom) ∋ α) →
      PreOrDom pre dom p
  | [],         _, p          => PreOrDom.pre p
  | _ :: _,     _, .here i    => PreOrDom.dom (.here i)
  | _ :: dom',  _, .there p'  =>
    match classifyDom pre dom' p' with
    | PreOrDom.pre q   => PreOrDom.pre q
    | PreOrDom.dom q'  => PreOrDom.dom (ListSlot.there q')

/-- Walk through τ; at `τ = []` delegate to `classifyDom`. -/
def classify {C : Carrier} (pre : Shape C) (dom : List C.Arity) :
    (τ : List C.Arity) → {α : C.Arity} → (p : ((pre ⋈* dom) ⋈* τ) ∋ α) →
      XPos pre dom τ p
  | [],       _, p           =>
      match classifyDom pre dom p with
      | PreOrDom.pre q  => XPos.pre q
      | PreOrDom.dom q  => XPos.dom q
  | _ :: _,   _, .here i     => XPos.ext (τ_above := []) i
  | β :: τ',  _, .there p'   =>
    match classify pre dom τ' p' with
    | XPos.pre q   => XPos.pre q
    | XPos.dom q'  => XPos.dom q'
    | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) j =>
        XPos.ext (τ_above := β :: ta) (β := b) (τ_below := tb) j

/-- The walker: apply σ to an expression at depth τ. -/
def Subst.act {C : Carrier} : (σ : Subst C) → (τ : List C.Arity) →
    Expr ((σ.pre ⋈* σ.dom) ⋈* τ) → Expr ((σ.pre ⋈* σ.cod) ⋈* τ)
  | σ, τ, .apply p args =>
    match classify σ.pre σ.dom τ p with
    | XPos.pre q =>
        Expr.apply
          (((σ.pre ⋈* σ.cod) ↪ʳ* τ) ((σ.pre ↪ʳ* σ.cod) q))
          (fun i => σ.act (i.arity :: τ) (args i))
    | XPos.dom (α := a) q =>
        let aux : Subst C :=
          { pre := σ.pre ⋈* σ.cod
          , dom := [a]
          , cod := τ
          , sub := fun {_} q' =>
              match q' with
              | .here i => σ.act (i.arity :: τ) (args i) }
        aux.act [] (σ.sub q)
    | XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
        Expr.apply
          (tauSlot (σ.pre ⋈* σ.cod) ta b tb i)
          (fun j => σ.act (j.arity :: (ta ++ b :: tb)) (args j))
termination_by σ _ e => ((⟨σ.dom⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; exact Expr.Subterm.of_arg _ _ _)
    | (apply Prod.Lex.left
       obtain ⟨β, h_mem, h_sub⟩ := ListSlot.subWitness q
       exact DomLt.step β h_mem _ h_sub)
