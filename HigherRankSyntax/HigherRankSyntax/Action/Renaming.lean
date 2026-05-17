import HigherRankSyntax.Action.Carrier

/-!
# Renamings of shapes

A *renaming* `γ →ʳ δ` is an arity-respecting slot map: a function
`ShapeSlots γ → ShapeSlots δ` that sends each slot to a slot of the
same arity.  Renamings are the morphisms of the Shape category in
the relative-monad picture.

Arities form a **discrete** category — only identities — so no
separate notion of renaming on arities is needed.

## Notations

  - `γ →ʳ δ` is the type of renamings from γ to δ.
  - `𝟙ʳ` is the identity renaming.
  - `g ∘ʳ f` is the composition; the textual order reverses
    `Renaming.comp` so it reads "g after f", matching the
    mathematical `g ∘ f`.
  - `f ⇑ʳ β` extends a renaming `f` through a fresh binder of
    arity `β`.

The `ʳ` suffix is consistently on the right.
-/

namespace Action

/-- A renaming of shapes from `γ` to `δ`: an arity-respecting slot
map. -/
structure Renaming {C : Carrier} (γ δ : C.Shape) : Type where
  /-- The underlying slot map. -/
  toFun : C.ShapeSlots γ → C.ShapeSlots δ
  /-- Each slot's image has the same arity as the slot itself. -/
  arity_preserving : ∀ s, C.shapeArity δ (toFun s) = C.shapeArity γ s

/-- Notation `γ →ʳ δ` for renamings from `γ` to `δ`. -/
scoped infixr:25 " →ʳ " => Renaming

instance {C : Carrier} {γ δ : C.Shape} :
    CoeFun (γ →ʳ δ) (fun _ => C.ShapeSlots γ → C.ShapeSlots δ) :=
  ⟨Renaming.toFun⟩

/-- The identity renaming. -/
def Renaming.id {C : Carrier} (γ : C.Shape) : γ →ʳ γ where
  toFun := _root_.id
  arity_preserving _ := rfl

/-- The identity renaming on a context. -/
scoped notation "𝟙ʳ" => Renaming.id _

/-- Composition of renamings: `comp f g` sends a slot through `f`,
then through `g`. -/
def Renaming.comp {C : Carrier} {γ δ ε : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) : γ →ʳ ε where
  toFun x := g (f x)
  arity_preserving s :=
    (g.arity_preserving (f s)).trans (f.arity_preserving s)

/-- `g ∘ʳ f` is the composition "g after f" (= `Renaming.comp f g`).
The textual order matches the mathematical `g ∘ f`. -/
scoped notation:90 g:90 " ∘ʳ " f:91 => Renaming.comp f g

/-- Two renamings are equal when their underlying slot maps agree
pointwise.  Their arity-preservation proofs are propositions and
agree by `proof_irrel`. -/
@[ext]
theorem Renaming.ext {C : Carrier} {γ δ : C.Shape} {f g : γ →ʳ δ}
    (h : ∀ s, f s = g s) : f = g := by
  cases f; cases g
  congr
  funext s
  exact h s

/-! ## Category laws -/

theorem Renaming.id_comp {C : Carrier} {γ δ : C.Shape} (f : γ →ʳ δ) :
    f ∘ʳ 𝟙ʳ = f := by
  ext; rfl

theorem Renaming.comp_id {C : Carrier} {γ δ : C.Shape} (f : γ →ʳ δ) :
    𝟙ʳ ∘ʳ f = f := by
  ext; rfl

theorem Renaming.comp_assoc {C : Carrier} {γ δ ε ζ : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) (h : ε →ʳ ζ) :
    h ∘ʳ (g ∘ʳ f) = (h ∘ʳ g) ∘ʳ f := by
  ext; rfl

/-! ## Extending through a binder -/

/-- Extend a renaming through a fresh binder of arity `β`.

`f.extend β : γ ⋈ β →ʳ δ ⋈ β` acts as `f` on the γ-side of the
slot equivalence and as the identity on the β-binder slots. -/
def Renaming.extend {C : Carrier} {γ δ : C.Shape}
    (f : γ →ʳ δ) (β : C.Arity) : γ ⋈ β →ʳ δ ⋈ β where
  toFun s :=
    match C.slotsExt γ β s with
    | .inl p => Carrier.inlSlot δ β (f p)
    | .inr y => Carrier.inrSlot δ β y
  arity_preserving s := by
    rw [C.slotsExtCompat γ β]
    rcases h : C.slotsExt γ β s with p | y
    · simp only [h, Sum.elim_inl, Carrier.shapeArity_inlSlot]
      exact f.arity_preserving p
    · simp only [h, Sum.elim_inr, Carrier.shapeArity_inrSlot]

/-- `f ⇑ʳ β` is `f` extended through a fresh binder of arity `β`. -/
scoped infixl:95 " ⇑ʳ " => Renaming.extend

/-- The canonical inclusion of `γ` into `γ ⋈ β` as the γ-summand of
the slot equivalence: every slot of `γ` is sent to its image on the
γ-side of `slotsExt`. -/
def Renaming.weaken {C : Carrier} (γ : C.Shape) (β : C.Arity) :
    γ →ʳ γ ⋈ β where
  toFun := Carrier.inlSlot γ β
  arity_preserving := Carrier.shapeArity_inlSlot γ β

/-- Iterated weakening: the canonical inclusion `γ →ʳ γ ⋈* τ`, built
by recursion on `τ`.  Empty `τ` gives the identity; cons extends the
previous weakening through one more binder. -/
def Renaming.weakenList {C : Carrier} (γ : C.Shape) :
    (τ : List C.Arity) → γ →ʳ γ ⋈* τ
  | [] => Renaming.id γ
  | β :: rest => Renaming.weaken (γ ⋈* rest) β ∘ʳ Renaming.weakenList γ rest

/-! ## Functoriality of `extend`

For each fixed arity `β`, `(- ⇑ʳ β) : Shape ⥤ Shape` is a functor:
it preserves identities and composition. -/

@[simp]
theorem Renaming.extend_id {C : Carrier} (γ : C.Shape) (β : C.Arity) :
    (𝟙ʳ : γ →ʳ γ) ⇑ʳ β = 𝟙ʳ := by
  ext s
  show (match C.slotsExt γ β s with
        | .inl p => Carrier.inlSlot γ β p
        | .inr y => Carrier.inrSlot γ β y) = s
  rw [show (match C.slotsExt γ β s with
            | .inl p => Carrier.inlSlot γ β p
            | .inr y => Carrier.inrSlot γ β y)
          = (C.slotsExt γ β).symm ((C.slotsExt γ β) s)
       by cases C.slotsExt γ β s <;> rfl]
  exact (C.slotsExt γ β).symm_apply_apply s

@[simp]
theorem Renaming.extend_comp {C : Carrier} {γ δ ε : C.Shape}
    (f : γ →ʳ δ) (g : δ →ʳ ε) (β : C.Arity) :
    (g ∘ʳ f) ⇑ʳ β = (g ⇑ʳ β) ∘ʳ (f ⇑ʳ β) := by
  ext s
  show (match C.slotsExt γ β s with
        | .inl p => Carrier.inlSlot ε β (g (f p))
        | .inr y => Carrier.inrSlot ε β y)
       = (match C.slotsExt δ β
             (match C.slotsExt γ β s with
              | .inl p => Carrier.inlSlot δ β (f p)
              | .inr y => Carrier.inrSlot δ β y) with
          | .inl q => Carrier.inlSlot ε β (g q)
          | .inr z => Carrier.inrSlot ε β z)
  cases C.slotsExt γ β s with
  | inl p => simp [Carrier.inlSlot, Equiv.apply_symm_apply]
  | inr y => simp [Carrier.inrSlot, Equiv.apply_symm_apply]

end Action
