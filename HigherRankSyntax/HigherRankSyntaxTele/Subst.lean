import HigherRankSyntaxTele.Expr
import HigherRankSyntaxTele.ProperTele

/-!
# Substitution

`Subst C pre dom cod` (with `[ProperTele dom]` `[ProperTele cod]` in
scope) carries one field, `sub`, mapping each `dom`-slot to an
expression in `pre ⋈* cod`.

The walker `Subst.act` takes `τ : Shape C` with `[ProperTele τ]` and
uses `ProperTele.classify (t := τ)` for the τ/below-τ dispatch and
`ProperTele.classify (t := dom)` for the pre/dom dispatch below τ.
Weakening pre-slots into the target uses `ProperTele.weaken (t := cod)`.

`Subst.classifyDom` and `Subst.weakenCod` are *projections* through
the `[ProperTele dom]` and `[ProperTele cod]` instances, not struct
fields — they're determined by the structural data on dom and cod.
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

/-- Dispatching a slot of `pre ⋈* dom` into pre vs dom.  Returned by
`Subst.classifyDom`. -/
inductive PreOrDom {C : Carrier} (pre dom : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to `pre`. -/
  | pre (q : pre ∋ α)
  /-- The slot belongs to `dom`. -/
  | dom (q : dom ∋ α)

/-- A substitution record.  Source shape is `pre ⋈* dom`, target is
`pre ⋈* cod`.  The `sub` field is the only data; slot dispatch and
pre-weakening are derived from `[ProperTele dom]` and `[ProperTele cod]`
at the operations that need them (see `Subst.classifyDom`,
`Subst.weakenCod`, `Subst.act`). -/
structure Subst (C : Carrier) (pre dom cod : Shape C) : Type where
  sub : ∀ {α : C.Arity}, (dom ∋ α) → Expr ((pre ⋈* cod) ⋈ α)

/-- Dispatching a `pre ⋈* dom`-slot into pre vs dom, via `[ProperTele dom]`. -/
def Subst.classifyDom {C : Carrier} {pre dom cod : Shape C}
    [ProperTele dom] (_σ : Subst C pre dom cod)
    {α : C.Arity} (p : (pre ⋈* dom) ∋ α) : PreOrDom pre dom α :=
  ProperTele.classify (t := dom) pre _ p PreOrDom.dom PreOrDom.pre

/-- Embedding `pre` into `pre ⋈* cod`, via `[ProperTele cod]`. -/
def Subst.weakenCod {C : Carrier} {pre dom cod : Shape C}
    [ProperTele cod] (_σ : Subst C pre dom cod) :
    pre →ʳ pre ⋈* cod :=
  ProperTele.weaken (t := cod) pre

/-! ### Kleisli ↔ Subst correspondence

A Kleisli map of the syntax relative monad is `∀ {α}, (Γ ∋ α) → Expr (Δ ⋈ α)`.
With cons-style telescopes and `pre := Shape.nil`, the correspondence to
`Subst` is *definitional*: `Shape.nil ⋈* X = X` by Tele's strict left unit. -/

/-- Wrap a Kleisli map as a `Subst` with empty `pre`. -/
def toSubst {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α)) :
    Subst C Shape.nil Γ Δ where
  sub := f

@[simp] theorem toSubst_sub {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α))
    {α : C.Arity} (p : Γ ∋ α) :
    (toSubst f).sub p = f p := rfl

/-- The identity substitution at shape `Γ` — `toSubst` of the unit `Expr.η`. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst C Shape.nil Γ Γ :=
  toSubst (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)

/-! ### The walker -/

/-- Apply a substitution to an expression at depth `τ`.  Uses
`ProperTele.classify (t := τ)` for the τ/below-τ dispatch and
`σ.classifyDom` for the pre/dom dispatch.  All renamings used to rebuild
new heads in the target come from `[ProperTele τ]` / `[ProperTele cod]`. -/
def Subst.act {C : Carrier} : {pre dom cod : Shape C} →
    [ProperTele dom] → [ProperTele cod] →
    (σ : Subst C pre dom cod) →
    (τ : Shape C) → [ProperTele τ] →
    Expr ((pre ⋈* dom) ⋈* τ) → Expr ((pre ⋈* cod) ⋈* τ)
  | pre, dom, cod, _, _, σ, τ, _, .apply (α := α) p args =>
      ProperTele.classify (t := τ) (pre ⋈* dom) (Expr ((pre ⋈* cod) ⋈* τ)) p
        (fun q_τ =>
          Expr.apply (ProperTele.embed (t := τ) (pre ⋈* cod) q_τ)
            (fun i => σ.act (τ ⋈ i.arity) (args i)))
        (fun p_below =>
          match σ.classifyDom p_below with
          | PreOrDom.dom q_dom =>
              let aux : Subst C (pre ⋈* cod) (Shape.nil ⋈ α) τ := {
                sub := fun {_} q' => match q' with
                  | .here i => σ.act (τ ⋈ i.arity) (args i)
              }
              aux.act Shape.nil (σ.sub q_dom)
          | PreOrDom.pre q_pre =>
              Expr.apply
                (ProperTele.weaken (t := τ) (pre ⋈* cod)
                  ((Subst.weakenCod σ).apply q_pre))
                (fun i => σ.act (τ ⋈ i.arity) (args i)))
termination_by pre dom _ _ _ _ _ _ e =>
  ((⟨dom.toList⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg p args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness q_dom
         exact DomLt.step β h_mem _ h_sub))

/-- Kleisli composition of two Kleisli maps via `Subst.act`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Ε : Shape C} [ProperTele Δ] [ProperTele Ε]
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, (Δ ∋ β) → Expr (Ε ⋈ β)) :
    ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Ε ⋈ β) :=
  fun {β} p => (toSubst g).act (Shape.nil ⋈ β) (f p)
