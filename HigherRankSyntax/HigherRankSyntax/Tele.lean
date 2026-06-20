/-!
# Telescopes — cons-style

A *telescope* over `α` is an endofunction `f : List α → List α`.  We use
them to represent "prepend some list to the input", but Tele itself
imposes no such restriction — it's just the carrier of the strict-monoid
structure.  Cons-preservation properties (where needed) are imposed
externally via the `Proper` type class.

Telescopes form a strict monoid under function composition (with `id` as unit):
- function composition is definitionally associative;
- η-equivalence makes `id ∘ f` and `f ∘ id` definitionally `f`.

The cons-style convention (vs. snoc-style `xs ↦ xs ⋈ lst`) is chosen so that
`(Tele.cons α ∘ᵗ Γ).toList = α :: Γ.toList` reduces *definitionally* — this is
what makes `SlotAt`-via-underlying-list work cleanly under pattern matching.
-/


/-- A telescope: an endofunction on `List α`. -/
@[ext] structure Tele (α : Type) where
  /-- The underlying endofunction. -/
  val : List α → List α

/-- Apply a telescope as a function. -/
instance {α : Type} : CoeFun (Tele α) (fun _ => List α → List α) := ⟨Tele.val⟩

namespace Tele

/-- Identity telescope. -/
def id (α : Type) : Tele α := ⟨_root_.id⟩

/-- Composition of telescopes.  `t ∘ᵗ s` applies `s` first, then `t`. -/
def comp {α : Type} (t s : Tele α) : Tele α := ⟨fun xs => t (s xs)⟩

@[inherit_doc Tele.comp]
infixl:90 " ∘ᵗ " => Tele.comp

/-- The "cons" telescope: `xs ↦ a :: xs`.  Underlying list: `[a]`. -/
def cons {α : Type} (a : α) : Tele α := ⟨fun xs => a :: xs⟩

/-- The underlying list of a telescope: `t.toList = t []`. -/
def toList {α : Type} (t : Tele α) : List α := t []

/-- The "tele" map from `List α` to `Tele α`, defined recursively so that
`ofList (β :: rest) = Tele.cons β ∘ᵗ ofList rest` is `rfl`. -/
def ofList {α : Type} : List α → Tele α
  | []        => Tele.id _
  | β :: rest => Tele.cons β ∘ᵗ ofList rest

/-! ### Reductions -/

@[simp] theorem id_apply {α : Type} (xs : List α) : (Tele.id α) xs = xs := rfl

@[simp] theorem cons_apply {α : Type} (a : α) (xs : List α) :
    (Tele.cons a) xs = a :: xs := rfl

@[simp] theorem comp_apply {α : Type} (t s : Tele α) (xs : List α) :
    (t ∘ᵗ s) xs = t (s xs) := rfl

@[simp] theorem id_toList {α : Type} : (Tele.id α).toList = [] := rfl

@[simp] theorem cons_toList {α : Type} (a : α) : (Tele.cons a).toList = [a] := rfl

@[simp] theorem cons_comp_toList {α : Type} (a : α) (t : Tele α) :
    (Tele.cons a ∘ᵗ t).toList = a :: t.toList := rfl

@[simp] theorem ofList_nil {α : Type} : (ofList ([] : List α)) = Tele.id _ := rfl

@[simp] theorem ofList_cons {α : Type} (β : α) (rest : List α) :
    ofList (β :: rest) = Tele.cons β ∘ᵗ ofList rest := rfl

/-! ### Monoid laws -/

@[simp] theorem id_comp {α : Type} (t : Tele α) : Tele.id _ ∘ᵗ t = t := rfl

@[simp] theorem comp_id {α : Type} (t : Tele α) : t ∘ᵗ Tele.id _ = t := rfl

@[simp] theorem comp_assoc {α : Type} (t s r : Tele α) :
    (t ∘ᵗ s) ∘ᵗ r = t ∘ᵗ (s ∘ᵗ r) := rfl

/-! ### Round trip -/

@[simp] theorem ofList_toList {α : Type} : ∀ (lst : List α), (ofList lst).toList = lst
  | [] => rfl
  | β :: rest => by
      show (Tele.cons β ∘ᵗ ofList rest).toList = β :: rest
      show β :: (ofList rest).toList = β :: rest
      rw [ofList_toList rest]

theorem ofList_apply {α : Type} :
    ∀ (lst : List α) (xs : List α), (ofList lst) xs = lst ++ xs
  | [], _ => rfl
  | β :: rest, xs => by
      show (Tele.cons β ∘ᵗ ofList rest) xs = (β :: rest) ++ xs
      show β :: (ofList rest) xs = β :: (rest ++ xs)
      rw [ofList_apply rest xs]

end Tele
