/-!
# Telescopes

A *telescope* over `α` is an endofunction on `List α` that "preserves cons" —
equivalently, an endofunction of the form `xs ↦ xs ++ lst` for some `lst : List α`.

Telescopes form a strict monoid under function composition (with `id` as unit),
because:
- function composition is definitionally associative;
- η-equivalence makes `id ∘ f` and `f ∘ id` definitionally `f`;
- propositional proof irrelevance collapses subtype equality to value equality.

This sidesteps the propositional `xs ++ [] = xs` that breaks the list monoid's
unit law.
-/


/-- A telescope: an endofunction on `List α` whose action on a cons is to lift the
head out — equivalently, an "append on the right" function. -/
@[ext] structure Tele (α : Type) where
  /-- The underlying endofunction. -/
  val : List α → List α
  /-- Cons-preservation: characterises telescopes as right-appends. -/
  property : ∀ (x : α) (xs : List α), val (x :: xs) = x :: val xs

namespace Tele

/-- Identity telescope. -/
def id {α : Type} : Tele α := ⟨_root_.id, fun _ _ => rfl⟩

/-- Composition of telescopes.  `t ∘ᵗ s` applies `s` first, then `t`. -/
def comp {α : Type} (t s : Tele α) : Tele α where
  val := t.val ∘ s.val
  property := fun x xs => by
    show t.val (s.val (x :: xs)) = x :: t.val (s.val xs)
    rw [s.property, t.property]

@[inherit_doc Tele.comp]
infixl:90 " ∘ᵗ " => Tele.comp

/-- The "snoc" telescope: `xs ↦ xs ++ [a]`.  Underlying list: `[a]`. -/
def snoc {α : Type} (a : α) : Tele α where
  val xs := xs ++ [a]
  property := fun _ _ => rfl

/-- The "tele" map from `List α` to `Tele α`: `lst ↦ (xs ↦ xs ++ lst)`. -/
def ofList {α : Type} (lst : List α) : Tele α where
  val xs := xs ++ lst
  property := fun _ _ => rfl

/-- The underlying list of a telescope: `t.toList = t []`. -/
def toList {α : Type} (t : Tele α) : List α := t.val []

@[simp] theorem id_toList {α : Type} : (Tele.id : Tele α).toList = [] := rfl

@[simp] theorem snoc_toList {α : Type} (a : α) : (snoc a).toList = [a] := rfl

@[simp] theorem ofList_toList {α : Type} (lst : List α) : (ofList lst).toList = lst :=
  List.nil_append lst

/-! ### Strict monoid laws (all `rfl`) -/

@[simp] theorem id_comp {α : Type} (t : Tele α) : Tele.id ∘ᵗ t = t := rfl

@[simp] theorem comp_id {α : Type} (t : Tele α) : t ∘ᵗ Tele.id = t := rfl

@[simp] theorem comp_assoc {α : Type} (t s r : Tele α) :
    (t ∘ᵗ s) ∘ᵗ r = t ∘ᵗ (s ∘ᵗ r) := rfl

/-! ### Round-trips between `Tele` and `List` -/

theorem ofList_toList_eq {α : Type} (t : Tele α) : ofList t.toList = t := by
  apply Tele.ext
  funext xs
  show xs ++ t.val [] = t.val xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show x :: (xs ++ t.val []) = t.val (x :: xs)
    rw [t.property, ih]

@[simp] theorem toList_comp {α : Type} (t s : Tele α) :
    (t ∘ᵗ s).toList = s.toList ++ t.toList := by
  show t.val (s.val []) = s.val [] ++ t.val []
  have h : t.val (s.val []) = (ofList t.toList).val (s.val []) := by
    rw [ofList_toList_eq]
  rw [h]
  rfl

end Tele
