import HigherRankSyntax.Action.Carrier

/-!
# Renamings of shapes

A *renaming* `γ →ʳ δ` is an arity-respecting slot map: a function
`ShapeSlots γ → ShapeSlots δ` that sends each slot to a slot of the
same arity.  Renamings are the morphisms of the Shape category in
the relative-monad picture.

Arities form a **discrete** category — only identities — so no
separate notion of renaming on arities is needed.
-/

namespace Action

open scoped Carrier

/-- A renaming of shapes from `γ` to `δ`: an arity-respecting slot
map. -/
structure Renaming {C : Carrier} (γ δ : C.Shape) : Type where
  /-- The underlying slot map. -/
  toFun : C.ShapeSlots γ → C.ShapeSlots δ
  /-- Each slot's image has the same arity as the slot itself. -/
  arity_preserving : ∀ s, C.shapeArity δ (toFun s) = C.shapeArity γ s

/-- Notation `γ →ʳ δ` for renamings from `γ` to `δ`. -/
scoped infixr:25 " →ʳ " => Renaming

namespace Renaming

variable {C : Carrier}

instance {γ δ : C.Shape} :
    CoeFun (γ →ʳ δ) (fun _ => C.ShapeSlots γ → C.ShapeSlots δ) :=
  ⟨toFun⟩

/-- The identity renaming. -/
def id (γ : C.Shape) : γ →ʳ γ where
  toFun := _root_.id
  arity_preserving _ := rfl

/-- Composition of renamings: `comp f g` sends a slot through `f`,
then through `g`.  Order matches the categorical convention
`f ≫ g`. -/
def comp {γ δ ε : C.Shape} (f : γ →ʳ δ) (g : δ →ʳ ε) : γ →ʳ ε where
  toFun := g.toFun ∘ f.toFun
  arity_preserving s :=
    (g.arity_preserving (f.toFun s)).trans (f.arity_preserving s)

/-- Extend a renaming through a fresh binder of arity `β`.

`f.extend β : γ ⋈ β →ʳ δ ⋈ β` acts as `f` on the γ-side of the
slot equivalence and as the identity on the β-binder slots.
Categorically: `extend (- , β) : Shape ⥤ Shape` is a functor for
each fixed `β`. -/
def extend {γ δ : C.Shape} (f : γ →ʳ δ) (β : C.Arity) :
    γ ⋈ β →ʳ δ ⋈ β where
  toFun s :=
    match C.slotsExt γ β s with
    | .inl p => (C.slotsExt δ β).symm (.inl (f.toFun p))
    | .inr y => (C.slotsExt δ β).symm (.inr y)
  arity_preserving s := by
    rw [C.slotsExtCompat δ β, C.slotsExtCompat γ β]
    rcases h : C.slotsExt γ β s with p | y
    · simp only [h, Equiv.apply_symm_apply, Sum.elim_inl]
      exact f.arity_preserving p
    · simp only [h, Equiv.apply_symm_apply, Sum.elim_inr]

/-- Two renamings are equal when their underlying slot maps agree
pointwise.  Their arity-preservation proofs are propositions and
agree by `proof_irrel`. -/
@[ext]
theorem ext {γ δ : C.Shape} {f g : γ →ʳ δ}
    (h : ∀ s, f.toFun s = g.toFun s) : f = g := by
  cases f; cases g
  congr
  funext s
  exact h s

/-! ## Category laws

Shapes with renamings form a category.  Identity and composition
satisfy the unit and associativity laws by direct unfolding. -/

theorem id_comp {γ δ : C.Shape} (f : γ →ʳ δ) :
    comp (id γ) f = f := by
  ext; rfl

theorem comp_id {γ δ : C.Shape} (f : γ →ʳ δ) :
    comp f (id δ) = f := by
  ext; rfl

theorem comp_assoc {γ δ ε ζ : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) (h : ε →ʳ ζ) :
    comp (comp f g) h = comp f (comp g h) := by
  ext; rfl

/-! ## Functoriality of `extend`

For each fixed arity `β`, `(- ).extend β : Shape ⥤ Shape` is a
functor: it preserves identities and composition. -/

@[simp]
theorem extend_id (γ : C.Shape) (β : C.Arity) :
    (id γ).extend β = id (γ ⋈ β) := by
  ext s
  show (match C.slotsExt γ β s with
        | .inl p => (C.slotsExt γ β).symm (.inl p)
        | .inr y => (C.slotsExt γ β).symm (.inr y)) = s
  rw [show (match C.slotsExt γ β s with
            | .inl p => (C.slotsExt γ β).symm (.inl p)
            | .inr y => (C.slotsExt γ β).symm (.inr y))
          = (C.slotsExt γ β).symm ((C.slotsExt γ β) s)
       by cases C.slotsExt γ β s <;> rfl]
  exact (C.slotsExt γ β).symm_apply_apply s

@[simp]
theorem extend_comp {γ δ ε : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) (β : C.Arity) :
    (comp f g).extend β = comp (f.extend β) (g.extend β) := by
  ext s
  show (match C.slotsExt γ β s with
        | .inl p => (C.slotsExt ε β).symm (.inl (g.toFun (f.toFun p)))
        | .inr y => (C.slotsExt ε β).symm (.inr y))
       = (match C.slotsExt δ β
             (match C.slotsExt γ β s with
              | .inl p => (C.slotsExt δ β).symm (.inl (f.toFun p))
              | .inr y => (C.slotsExt δ β).symm (.inr y)) with
          | .inl q => (C.slotsExt ε β).symm (.inl (g.toFun q))
          | .inr z => (C.slotsExt ε β).symm (.inr z))
  cases C.slotsExt γ β s with
  | inl p => simp [Equiv.apply_symm_apply]
  | inr y => simp [Equiv.apply_symm_apply]

end Renaming

end Action
