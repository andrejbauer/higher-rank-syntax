/-!
# Telescopes — cons-style

A *telescope* over `α` is an endofunction `f : List α → List α` representing
"prepend some list to the input".  Formally, `f xs = f [] ++ xs`.

Telescopes form a strict monoid under function composition (with `id` as unit):
- function composition is definitionally associative;
- η-equivalence makes `id ∘ f` and `f ∘ id` definitionally `f`;
- propositional proof irrelevance collapses subtype equality to value equality.

The cons-style convention (vs. snoc-style `xs ↦ xs ++ lst`) is chosen so that
`(Tele.cons α ∘ᵗ Γ).toList = α :: Γ.toList` reduces *definitionally* — this is
what makes `SlotAt`-via-underlying-list work cleanly under pattern matching.

Many results in this file hold for arbitrary endofunctions `List α → List α`,
not just telescopes.  The `property` field is required only where the
extensional characterization is needed.
-/


/-- A telescope: an endofunction on `List α` that factors as left-prepending its
underlying list. -/
@[ext] structure Tele (α : Type) where
  /-- The underlying endofunction. -/
  val : List α → List α
  /-- Extensional characterization: the map is left-append by its action on `[]`. -/
  property : ∀ xs, val xs = val [] ++ xs

/-- Apply a telescope as a function. -/
instance {α : Type} : CoeFun (Tele α) (fun _ => List α → List α) := ⟨Tele.val⟩

namespace Tele

/-- Identity telescope. -/
def id {α : Type} : Tele α := ⟨_root_.id, fun _ => rfl⟩

/-- Composition of telescopes.  `t ∘ᵗ s` applies `s` first, then `t`. -/
def comp {α : Type} (t s : Tele α) : Tele α where
  val xs := t (s xs)
  property xs := by
    show t (s xs) = t (s []) ++ xs
    rw [s.property xs, t.property (s [] ++ xs), t.property (s [])]
    exact (List.append_assoc _ _ _).symm

@[inherit_doc Tele.comp]
infixl:90 " ∘ᵗ " => Tele.comp

/-- The "cons" telescope: `xs ↦ a :: xs`.  Underlying list: `[a]`. -/
def cons {α : Type} (a : α) : Tele α where
  val xs := a :: xs
  property _ := rfl

/-- The underlying list of a telescope: `t.toList = t []`. -/
def toList {α : Type} (t : Tele α) : List α := t []

/-- The "tele" map from `List α` to `Tele α`, defined recursively so that
`ofList (β :: rest) = Tele.cons β ∘ᵗ ofList rest` is `rfl`. -/
def ofList {α : Type} : List α → Tele α
  | []        => Tele.id
  | β :: rest => Tele.cons β ∘ᵗ ofList rest

/-! ### Definitional reductions -/

@[simp] theorem id_apply {α : Type} (xs : List α) : (Tele.id : Tele α) xs = xs := rfl

@[simp] theorem cons_apply {α : Type} (a : α) (xs : List α) :
    (Tele.cons a) xs = a :: xs := rfl

@[simp] theorem comp_apply {α : Type} (t s : Tele α) (xs : List α) :
    (t ∘ᵗ s) xs = t (s xs) := rfl

@[simp] theorem id_toList {α : Type} : (Tele.id : Tele α).toList = [] := rfl

@[simp] theorem cons_toList {α : Type} (a : α) : (Tele.cons a).toList = [a] := rfl

@[simp] theorem cons_comp_toList {α : Type} (a : α) (t : Tele α) :
    (Tele.cons a ∘ᵗ t).toList = a :: t.toList := rfl

@[simp] theorem ofList_nil {α : Type} : (ofList ([] : List α)) = Tele.id := rfl

@[simp] theorem ofList_cons {α : Type} (β : α) (rest : List α) :
    ofList (β :: rest) = Tele.cons β ∘ᵗ ofList rest := rfl

/-! ### Strict monoid laws (all `rfl`) -/

@[simp] theorem id_comp {α : Type} (t : Tele α) : Tele.id ∘ᵗ t = t := rfl

@[simp] theorem comp_id {α : Type} (t : Tele α) : t ∘ᵗ Tele.id = t := rfl

@[simp] theorem comp_assoc {α : Type} (t s r : Tele α) :
    (t ∘ᵗ s) ∘ᵗ r = t ∘ᵗ (s ∘ᵗ r) := rfl

/-! ### Round trip -/

@[simp] theorem ofList_toList {α : Type} : ∀ (lst : List α), (ofList lst).toList = lst
  | [] => rfl
  | β :: rest => by
      show (Tele.cons β ∘ᵗ ofList rest).toList = β :: rest
      show β :: (ofList rest).toList = β :: rest
      rw [ofList_toList rest]

/-- Telescopes act as left-prepending of their underlying list. -/
theorem apply_eq_toList_append {α : Type} (t : Tele α) (xs : List α) :
    t xs = t.toList ++ xs := t.property xs

theorem ofList_apply {α : Type} :
    ∀ (lst : List α) (xs : List α), (ofList lst) xs = lst ++ xs
  | [], _ => rfl
  | β :: rest, xs => by
      show (Tele.cons β ∘ᵗ ofList rest) xs = (β :: rest) ++ xs
      show β :: (ofList rest) xs = β :: (rest ++ xs)
      rw [ofList_apply rest xs]

theorem ofList_toList_eq {α : Type} (t : Tele α) : ofList t.toList = t := by
  apply Tele.ext
  funext xs
  rw [ofList_apply]
  exact (t.property xs).symm

end Tele
