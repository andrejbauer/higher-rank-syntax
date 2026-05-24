import HigherRankSyntaxTele.Expr
import HigherRankSyntaxTele.ProperTele

/-!
# Substitution

`Subst C` carries the data for a single-pass substitution walker:

* `pre`, `dom`, `cod : Shape C` — the OCaml-style three-region partition.
* `sub` — substitutes `dom`-slots with expressions in `pre ⋈* cod`.
* `classifyDom` — dispatches a slot of `pre ⋈* dom` into either a `dom`-slot
  or a `pre`-slot.  Carried as a function so the walker doesn't induct on
  the underlying telescope.
* `weakenCod` — `pre →ʳ pre ⋈* cod`, the renaming needed for pre-slot
  rebuild.  Carried for the same reason.

The walker `Subst.act` takes `τ : CTele C` and uses CTele's classifier for
the τ/below-τ dispatch and `σ.classifyDom` for the pre/dom dispatch below τ.
No list pattern-matching anywhere in the construction.
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

/-- Dispatching a slot of `pre ⋈* dom` into pre vs dom.  Carried by `Subst` as a
function-typed field. -/
inductive PreOrDom {C : Carrier} (pre dom : Shape C) (α : C.Arity) : Type where
  /-- The slot belongs to `pre`. -/
  | pre (q : pre ∋ α)
  /-- The slot belongs to `dom`. -/
  | dom (q : dom ∋ α)

/-- A substitution record.  Source shape is `pre ⋈* dom`, target is `pre ⋈* cod`.

`pre`, `dom`, `cod` are type-level parameters (not fields), so type-equality of
two Substs forces equality of all three regions.  Beyond the sub map, `Subst`
carries two function-typed helpers consumed uniformly by the walker:

* `classifyDom` dispatches a `pre ⋈* dom` slot into pre vs dom.
* `weakenCod` embeds `pre` into `pre ⋈* cod` (for pre-slot rebuild). -/
structure Subst (C : Carrier) (pre dom cod : Shape C) where
  sub : ∀ {α : C.Arity}, (dom ∋ α) → Expr ((pre ⋈* cod) ⋈ α)
  classifyDom : ∀ {α : C.Arity}, ((pre ⋈* dom) ∋ α) → PreOrDom pre dom α
  weakenCod : pre →ʳ pre ⋈* cod

/-! ### Kleisli ↔ Subst correspondence

A Kleisli map of the syntax relative monad is `∀ {α}, (Γ ∋ α) → Expr (Δ ⋈ α)`.
With cons-style telescopes and `pre := Shape.nil`, the correspondence to
`Subst` is *definitional*: `Shape.nil ⋈* X = X` by Tele's strict left unit. -/

/-- Wrap a Kleisli map as a `Subst` with empty `pre`. -/
def toSubst {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α)) : Subst C Shape.nil Γ Δ where
  sub := f
  classifyDom := fun {_} p => PreOrDom.dom p
  weakenCod := ⟨fun {_} p => nomatch p⟩

@[simp] theorem toSubst_classifyDom {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α))
    {α : C.Arity} (p : Γ ∋ α) :
    (toSubst f).classifyDom p = PreOrDom.dom p := rfl

@[simp] theorem toSubst_sub {C : Carrier} {Γ Δ : Shape C}
    (f : ∀ {α : C.Arity}, (Γ ∋ α) → Expr (Δ ⋈ α))
    {α : C.Arity} (p : Γ ∋ α) :
    (toSubst f).sub p = f p := rfl

/-- The identity substitution at shape `Γ` — `toSubst` of the unit `Expr.η`.
This is the Kleisli identity of the syntax relative monad. -/
def Subst.id {C : Carrier} (Γ : Shape C) : Subst C Shape.nil Γ Γ :=
  toSubst (fun {β : C.Arity} (p : Γ ∋ β) => Expr.η p)

/-! ### The walker -/

/-- Apply a substitution to an expression at depth `τ` (itself a classifiable
telescope).  Uses `τ.classify` (CPS) for the τ/below-τ dispatch and
`σ.classifyDom` (inductive) for the pre/dom dispatch.  All renamings used to
rebuild new heads in the target come from carried function-typed fields
(`τ.weaken`/`τ.embed`/`σ.weakenCod`). -/
def Subst.act {C : Carrier} : {pre dom cod : Shape C} → (σ : Subst C pre dom cod) →
    (τ : CTele C) →
    Expr ((pre ⋈* dom) ⋈* τ.shape) → Expr ((pre ⋈* cod) ⋈* τ.shape)
  | pre, dom, cod, σ, τ, .apply (α := α) p args =>
      τ.classify (pre ⋈* dom) (Expr ((pre ⋈* cod) ⋈* τ.shape)) p
        (fun q_τ =>
          Expr.apply (τ.embed (pre ⋈* cod) q_τ)
            (fun i => σ.act (CTele.cons i.arity τ) (args i)))
        (fun p_below =>
          match σ.classifyDom p_below with
          | PreOrDom.dom q_dom =>
              let aux : Subst C (pre ⋈* cod) (Shape.nil ⋈ α) τ.shape := {
                sub := fun {_} q' => match q' with
                  | .here i => σ.act (CTele.cons i.arity τ) (args i)
                classifyDom := fun {_} p' =>
                  match p' with
                  | .here i  => PreOrDom.dom (.here i)
                  | .there q => PreOrDom.pre q
                weakenCod := τ.weaken (pre ⋈* cod)
              }
              aux.act CTele.id (σ.sub q_dom)
          | PreOrDom.pre q_pre =>
              Expr.apply (τ.weaken (pre ⋈* cod) (σ.weakenCod q_pre))
                (fun i => σ.act (CTele.cons i.arity τ) (args i)))
termination_by pre dom _ _ _ e =>
  ((⟨dom.toList⟩ : DomMeasure C), (⟨_, e⟩ : Σ Γ : Shape C, Expr Γ))
decreasing_by
  all_goals (
    first
      | (refine Prod.Lex.right _ ?_; exact Expr.Subterm.of_arg p args i)
      | (refine Prod.Lex.left _ _ ?_
         obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subWitness q_dom
         exact DomLt.step β h_mem _ h_sub))

/-- Kleisli composition of two Kleisli maps via `Subst.act`.  Reified to take
the form expected by the relative-monad `lift`. -/
def Subst.kcomp {C : Carrier} {Γ Δ Ε : Shape C}
    (f : ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Δ ⋈ β))
    (g : ∀ {β : C.Arity}, (Δ ∋ β) → Expr (Ε ⋈ β)) :
    ∀ {β : C.Arity}, (Γ ∋ β) → Expr (Ε ⋈ β) :=
  fun {β} p => (toSubst g).act (CTele.cons β CTele.id) (f p)
