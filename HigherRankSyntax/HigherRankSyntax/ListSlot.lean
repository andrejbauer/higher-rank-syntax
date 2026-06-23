import HigherRankSyntax.Carrier

/-!
# List-indexed slots

`ListSlotAt xs α` is a slot of arity `α` in the arity-list `xs`: a position in
`xs` together with the position it opens.  This is the pure list-level theory,
independent of telescopes; `Shape.SlotAt` is `ListSlotAt` on a shape's
underlying list.

A slot is determined by two transport-free observations: its positional depth
`idx` and the position `tag` it picks out.  `ext` is the resulting determinacy
principle.
-/

/-- A slot of a list of arities with its arity tracked as a type index. -/
inductive ListSlotAt {C : Carrier} : List C.Arity → C.Arity → Type where
  /-- A position introduced by the topmost extension at its position's arity. -/
  | here  : {β : C.Arity} → {rest : List C.Arity} → (i : C.Position β) →
            ListSlotAt (β :: rest) i.arity
  /-- A slot inherited from below the topmost extension, at the same arity. -/
  | there : {β α : C.Arity} → {rest : List C.Arity} →
            ListSlotAt rest α → ListSlotAt (β :: rest) α

namespace ListSlotAt

/-- Positional depth of a slot in its list. -/
def idx {C : Carrier} : {xs : List C.Arity} → {α : C.Arity} → ListSlotAt xs α → Nat
  | _, _, .here _  => 0
  | _, _, .there s => s.idx + 1

/-- The position a slot picks out, together with the list element it sits at. -/
def tag {C : Carrier} : {xs : List C.Arity} → {α : C.Arity} →
    ListSlotAt xs α → Σ β : C.Arity, C.Position β
  | _, _, .here (β := β) i => ⟨β, i⟩
  | _, _, .there s         => s.tag

/-- The arity of a slot is the arity of the position it picks out. -/
theorem tag_arity {C : Carrier} : {xs : List C.Arity} → {α : C.Arity} →
    (s : ListSlotAt xs α) → (s.tag).2.arity = α
  | _, _, .here _  => rfl
  | _, _, .there s => tag_arity s

/-- Determinacy, heterogeneous: slots of the *same list* with equal position and
position are equal, even when their arity indices are stated separately. -/
theorem ext_heq {C : Carrier} : {xs : List C.Arity} → {α α' : C.Arity} →
    (s : ListSlotAt xs α) → (s' : ListSlotAt xs α') →
    s.idx = s'.idx → s.tag = s'.tag → HEq s s'
  | _, _, _, .here i,  .here i',  _,  ht => by
      simp only [tag] at ht
      injection ht with _ hi'
      subst hi'
      rfl
  | _, _, _, .here _,  .there _,  hi, _  => by simp [idx] at hi
  | _, _, _, .there _, .here _,   hi, _  => by simp [idx] at hi
  | _, _, _, .there s, .there s', hi, ht => by
      have hα : (s.tag).2.arity = (s'.tag).2.arity := by
        simp only [tag] at ht; rw [ht]
      rw [tag_arity, tag_arity] at hα
      subst hα
      have h := ext_heq s s' (by simpa [idx] using hi) (by simpa [tag] using ht)
      rw [eq_of_heq h]

/-- A slot is determined by its position and the position it picks out. -/
theorem ext {C : Carrier} {xs : List C.Arity} {α : C.Arity}
    (s s' : ListSlotAt xs α) (hi : s.idx = s'.idx) (ht : s.tag = s'.tag) : s = s' :=
  eq_of_heq (ext_heq s s' hi ht)

end ListSlotAt
