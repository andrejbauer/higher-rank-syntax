import HigherRankSyntax.Expr
import HigherRankSyntax.ListSlot
import Mathlib.Order.GameAdd

/-!
# Well-founded measure on substitution domains

`ListArity.Lt` is the one-step well-founded relation on `List C.Arity` driving the
termination of `Subst.act` and `act_interchange`.  `ListArity` wraps it as a
`WellFoundedRelation`.
-/

/-- A slot of `αs` witnesses that some `β ∈ αs` has the slot's arity as a
sub-arity. -/
theorem SlotAt.subArity {C : Carrier} :
  ∀ {αs : List C.Arity} {α : C.Arity}, ListSlotAt αs α → ∃ β, β ∈ αs ∧ Carrier.Sub α β
  | _ :: _, _, .here i  => ⟨_, List.Mem.head _, ⟨i, rfl⟩⟩
  | _ :: _, _, .there p => by
      obtain ⟨β, h_mem, h_sub⟩ := SlotAt.subArity p
      exact ⟨β, List.Mem.tail _ h_mem, h_sub⟩

/-- One-step WF relation on `List C.Arity`: `[β] ≺ αs` iff `β` is a sub-arity of
some `αⱼ ∈ αs`.  Used as the first component of `Subst.act`'s lex termination. -/
inductive ListArity.Lt {C : Carrier} : List C.Arity → List C.Arity → Prop
  | step {αs : List C.Arity} (αⱼ : C.Arity) (h_in : αⱼ ∈ αs)
         (β : C.Arity) (h_sub : Carrier.Sub β αⱼ) :
         ListArity.Lt [β] αs

private theorem ListArity.Lt.acc_singleton {C : Carrier} (α : C.Arity)
    (hα : Acc (Carrier.Sub (C := C)) α) :
    Acc (ListArity.Lt (C := C)) [α] := by
  induction hα with
  | intro α _ ih =>
      constructor
      intro αs' hαs'
      cases hαs' with
      | step αⱼ h_in β h_sub =>
          cases h_in with
          | head         => exact ih β h_sub
          | tail _ h_nil => cases h_nil

private theorem ListArity.Lt.wf {C : Carrier} : WellFounded (ListArity.Lt (C := C)) := by
  constructor
  intro αs
  constructor
  intro αs' hαs'
  cases hαs' with
  | step _ _ β _ => apply ListArity.Lt.acc_singleton ; apply C.subWf.apply

/-- A slot of `αs` descends to the singleton list of its own arity. -/
theorem ListArity.Lt.of_slot {C : Carrier} {αs : List C.Arity} {α : C.Arity}
    (z : ListSlotAt αs α) : ListArity.Lt [α] αs :=
  let ⟨γ, h_mem, h_sub⟩ := SlotAt.subArity z
  ListArity.Lt.step γ h_mem α h_sub

/-- Wrapper carrying the `ListArity.Lt` well-founded relation on `List C.Arity`. -/
structure ListArity (C : Carrier) : Type where
  unwrap : List C.Arity

instance (C : Carrier) : WellFoundedRelation (ListArity C) where
  rel := fun a b => ListArity.Lt a.unwrap b.unwrap
  wf := InvImage.wf ListArity.unwrap ListArity.Lt.wf

/-- Unordered pair of substitution-domain measures.  Opaque wrapper over
`Sym2 (ListArity C)`; the well-founded relation shrinks either component by
`ListArity.Lt`.  Switching to a multiset order touches only this file. -/
structure ListArity.Pair (C : Carrier) : Type where
  ofSym2 ::
  unwrap : Sym2 (ListArity C)

/-- The unordered pair of two domain measures. -/
def ListArity.Pair.mk {C : Carrier} (a b : ListArity C) : ListArity.Pair C :=
  ⟨s(a, b)⟩

instance (C : Carrier) : WellFoundedRelation (ListArity.Pair C) where
  rel a b := Sym2.GameAdd (@WellFoundedRelation.rel (ListArity C) _) a.unwrap b.unwrap
  wf := InvImage.wf ListArity.Pair.unwrap
    (WellFounded.sym2_gameAdd (@WellFoundedRelation.wf (ListArity C) _))

/-- Descend by shrinking the first component. -/
theorem ListArity.Pair.lt_left {C : Carrier} {a a' b : ListArity C}
    (h : ListArity.Lt a'.unwrap a.unwrap) :
    WellFoundedRelation.rel (ListArity.Pair.mk a' b) (ListArity.Pair.mk a b) :=
  Sym2.GameAdd.fst h

/-- Descend by shrinking the second component. -/
theorem ListArity.Pair.lt_right {C : Carrier} {a b b' : ListArity C}
    (h : ListArity.Lt b'.unwrap b.unwrap) :
    WellFoundedRelation.rel (ListArity.Pair.mk a b') (ListArity.Pair.mk a b) :=
  Sym2.GameAdd.snd h

/-- Descend by shrinking one component, the survivor moving to the other slot. -/
theorem ListArity.Pair.lt_swap {C : Carrier} {a b b' : ListArity C}
    (h : ListArity.Lt b'.unwrap a.unwrap) :
    WellFoundedRelation.rel (ListArity.Pair.mk b b') (ListArity.Pair.mk a b) :=
  Sym2.GameAdd.snd_fst h
