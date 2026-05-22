import HigherRankSyntax.Carrier

/-!
# Shapes and slots

The framework-level data on top of a `Carrier`.

* **Shape maps.**  A shape is represented by a base shape and a representable map on
  lists of arities.

* **Shapes.**  `Shape C` stores a base shape and a context map `ctx : List C.Arity → List C.Arity`
  satisfying the representability law `f (l₁ ++ l₂) = l₁ ++ f l₂`.  Iterated shape
  extension uses map composition.

* **Slots.**  `SlotAt Γ` is still the same inductive family of slots, with one constructor
  per layer: `.base x` for a variable of the base layer, `.here i` for the topmost
  binder extension, and `.there p` for a slot inherited from the shape below.

* **Slot arity.**  `SlotAt.arity` reads off the arity of a slot by recursion: a base slot
  uses the variable's `arity`, a `.here` binder uses that binder's `arity`, and `.there`
  inherits the arity from the underlying slot.
-/

/-- A list map representable by list concatenation on the right. -/
structure RepresentableListMap (α : Type) where
  /-- The represented endomorphism on lists. -/
  toFun : List α → List α
  /-- `f (l₁ ++ l₂) = l₁ ++ f l₂` for all lists. -/
  repr : ∀ l₁ l₂, toFun (l₁ ++ l₂) = l₁ ++ toFun l₂

namespace RepresentableListMap

variable {α : Type}

theorem ext {α : Type} {f g : RepresentableListMap α} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance (α : Type) : CoeFun (RepresentableListMap α) (fun _ => List α → List α) := ⟨toFun⟩

/-- The identity representable map `l ↦ l`. -/
def id (α : Type) : RepresentableListMap α :=
  { toFun := fun l => l
  , repr := by
      intro l₁ l₂
      rfl }

/-- The representable map `l ↦ l ++ τ`, i.e. append `τ` on the right. -/
def ofList {α : Type} (τ : List α) : RepresentableListMap α :=
  { toFun := fun l => l ++ τ
  , repr := by
      intro l₁ l₂
      simp [List.append_assoc] }

/-- Appending with the empty list is the identity map. -/
@[simp] theorem ofList_nil : ofList ([] : List α) = id α := by
  refine RepresentableListMap.ext ?_
  funext l
  simp [RepresentableListMap.ofList, RepresentableListMap.id, List.append_nil]

/-- Composition/extension of representable maps: apply the second, then the first. -/
def mul (f g : RepresentableListMap α) : RepresentableListMap α :=
  { toFun := fun l => f (g l)
  , repr := by
      intro l₁ l₂
      rw [g.repr, f.repr] }

instance : One (RepresentableListMap α) := ⟨id α⟩

instance : Mul (RepresentableListMap α) := ⟨mul⟩

@[simp] theorem one_mul (f : RepresentableListMap α) : id α * f = f := by
  rfl

@[simp] theorem mul_one (f : RepresentableListMap α) : f * id α = f := by
  rfl

@[simp] theorem mul_assoc (f g h : RepresentableListMap α) :
    (f * g) * h = f * (g * h) := by
    rfl

/-- Core characterization: `f l = l ++ f []`. -/
theorem toFun_append (f : RepresentableListMap α) (l : List α) :
    f.toFun l = l ++ f.toFun [] := by
  simpa using f.repr l []

/-- Representing lists compose by map multiplication with reversal of concatenation order.

`ofList (xs ++ ys)` is the same as `ofList ys * ofList xs` because context maps compose
right-to-left on lists. -/
@[simp] theorem ofList_append (xs ys : List α) :
    ofList (xs ++ ys) = ofList ys * ofList xs := by
  refine RepresentableListMap.ext ?_
  funext l
  change
    l ++ (xs ++ ys) =
      (RepresentableListMap.ofList ys * RepresentableListMap.ofList xs).toFun l
  calc
    l ++ (xs ++ ys) = (l ++ xs) ++ ys := by simp [List.append_assoc]
    _ = (RepresentableListMap.ofList ys * RepresentableListMap.ofList xs).toFun l := by
      change (l ++ xs) ++ ys = RepresentableListMap.ofList ys (RepresentableListMap.ofList xs l)
      simp [RepresentableListMap.ofList]

end RepresentableListMap

/-- A shape over a carrier `C`: a base shape and a representable context map on arity lists. -/
structure Shape (C : Carrier) where
  /-- The base shape associated with this shape layer. -/
  baseShape : C.BaseShape
  /-- The representable context extension map. -/
  ctx : RepresentableListMap C.Arity

/-- Extensionality for shapes. -/
theorem Shape.eq_of_fields {C : Carrier} {Γ Δ : Shape C}
    (hbase : Γ.baseShape = Δ.baseShape) (hctx : Γ.ctx = Δ.ctx) : Γ = Δ := by
  cases Γ
  cases Δ
  cases hbase
  cases hctx
  rfl

/-- The base shape constructor `Shape.base γ`. -/
def Shape.base {C : Carrier} (γ : C.BaseShape) : Shape C :=
  { baseShape := γ, ctx := RepresentableListMap.id C.Arity }

/-- Action of an arity on a shape, adding that binder layer at the top. -/
def Shape.ext {C : Carrier} (Γ : Shape C) (α : C.Arity) : Shape C :=
  { baseShape := Γ.baseShape
  , ctx := Γ.ctx * RepresentableListMap.ofList [α] }

infixl:65 " ⋈ " => Shape.ext

/-- A slot of a shape with its arity tracked as a type index: a variable of the base
layer (`.base x` at `x.arity`), a fresh binder of the topmost extension (`.here i` at
`i.arity`), or a slot inherited from the shape below (`.there p` at the same arity as
`p`). -/
inductive SlotAt {C : Carrier} : Shape C → C.Arity → Type where
  /-- A variable of the base shape at its variable's arity. -/
  | base : {γ : C.BaseShape} → (x : C.Var γ) → SlotAt (Shape.base γ) x.arity
  /-- A binder introduced by the topmost extension at its binder's arity. -/
  | here : {Γ : Shape C} → {α : C.Arity} → (i : C.Binder α) → SlotAt (Γ ⋈ α) i.arity
  /-- A slot inherited from the shape below the topmost extension, at the same arity. -/
  | there : {Γ : Shape C} → {β α : C.Arity} → SlotAt Γ α → SlotAt (Γ ⋈ β) α

/-- `Γ ∋ α` is the type of slots of `Γ` at arity `α`. -/
notation:35 Γ " ∋ " α => SlotAt Γ α

/-- Extract the arity index from a slot. -/
@[reducible]
def SlotAt.arity {C : Carrier} {Γ : Shape C} {α : C.Arity} (_ : Γ ∋ α) : C.Arity := α

/-- One-step-by-list context extension.

`Γ ⋈* τ` extends `Γ` by all binders in `τ`, with list head being the outermost extension
(cons-as-snoc convention). -/
def Shape.extList {C : Carrier} (Γ : Shape C) : List C.Arity → Shape C
  | []        => Γ
  | β :: rest => (Shape.extList Γ rest) ⋈ β

/-- Iterated extension of a shape by a list of arities. -/
infixl:67 " ⋈* " => Shape.extList

/-- Weakening a base-slot through an iterated extension by a list of arities. -/
def Shape.weakenList {C : Carrier} {α : C.Arity} (Γ : Shape C) :
    (τ : List C.Arity) → SlotAt Γ α → SlotAt (Γ ⋈* τ) α
  := fun τ p =>
    match τ with
    | [] => p
    | _ :: rest => SlotAt.there (Shape.weakenList (Γ := Γ) (α := α) rest p)

/-! ## Representable map extension helpers -/

/-- A slot at depth `|τ_above|` in `Γ ⋈* (τ_above ++ β :: τ_below)` corresponding to
binder `i` of `β`.  Iterates `.there` over `τ_above` from `.here i`. -/
def tauSlot {C : Carrier} (Γ : Shape C) :
    (τ_above : List C.Arity) → (β : C.Arity) → (τ_below : List C.Arity) →
    (i : C.Binder β) → (Γ ⋈* (τ_above ++ β :: τ_below)) ∋ i.arity
  | [],        _, _, i => .here i
  | _ :: rest, β, τ_below, i => .there (tauSlot Γ rest β τ_below i)

/-- Extend a shape by a representable map. -/
def Shape.extByMap {C : Carrier} (Γ : Shape C) (f : RepresentableListMap C.Arity) : Shape C :=
  { baseShape := Γ.baseShape, ctx := Γ.ctx * f }

/-- A representable map is determined by its action on `[]`. -/
theorem map_eq_ofList_toFun {C : Carrier} (f : RepresentableListMap C.Arity) :
    f = RepresentableListMap.ofList (f.toFun []) := by
  refine RepresentableListMap.ext ?_
  funext l
  simpa using f.toFun_append l

/-- Context map of iterated extension by a list. -/
theorem Shape.extList_ctx {C : Carrier} (Γ : Shape C) (τ : List C.Arity) :
    (Γ ⋈* τ).ctx = Γ.ctx * RepresentableListMap.ofList τ := by
  induction τ with
  | nil =>
      simp [Shape.extList, RepresentableListMap.ofList_nil]
  | cons β rest ih =>
      calc
        (Γ ⋈* (β :: rest)).ctx = ((Γ ⋈* rest).ctx) * RepresentableListMap.ofList [β] := by
          rfl
        _ = (Γ.ctx * RepresentableListMap.ofList rest) * RepresentableListMap.ofList [β] := by
          simp [ih]
        _ = Γ.ctx * (RepresentableListMap.ofList rest * RepresentableListMap.ofList [β]) := by
          simp [RepresentableListMap.mul_assoc (Γ.ctx) (RepresentableListMap.ofList rest)
            (RepresentableListMap.ofList [β])]
        _ = Γ.ctx * RepresentableListMap.ofList (β :: rest) := by
          rw [← RepresentableListMap.ofList_append, List.singleton_append]

/-- Iterated extension preserves the base shape. -/
@[simp] theorem Shape.extList_baseShape {C : Carrier} (Γ : Shape C) (τ : List C.Arity) :
    (Γ ⋈* τ).baseShape = Γ.baseShape := by
  induction τ with
  | nil =>
      rfl
  | cons β rest ih =>
      simp [Shape.extList, Shape.ext, ih]

@[simp] theorem Shape.extList_ctx_nil {C : Carrier} (Γ : Shape C) (τ : List C.Arity) :
    (Γ ⋈* τ).ctx.toFun [] = τ ++ Γ.ctx.toFun [] := by
  rw [Shape.extList_ctx]
  change Γ.ctx.toFun ((RepresentableListMap.ofList τ).toFun []) = τ ++ Γ.ctx.toFun []
  change Γ.ctx.toFun ([] ++ τ) = τ ++ Γ.ctx.toFun []
  simpa using Γ.ctx.toFun_append τ

@[simp] theorem Shape.ext_ctx_nil {C : Carrier} (Γ : Shape C) (β : C.Arity) :
    (Γ ⋈ β).ctx.toFun [] = β :: Γ.ctx.toFun [] := by
  change Γ.ctx.toFun ((RepresentableListMap.ofList [β]).toFun []) = β :: Γ.ctx.toFun []
  change Γ.ctx.toFun ([] ++ [β]) = β :: Γ.ctx.toFun []
  simpa using Γ.ctx.toFun_append [β]

/- `Γ.extByMap f` coincides with iterated list extension by `f.toFun []`. -/
theorem shape_extByMap_eq_extList {C : Carrier} (Γ : Shape C) (f : RepresentableListMap C.Arity) :
    Γ.extByMap f = Γ ⋈* f.toFun [] := by
  apply Shape.eq_of_fields
  · simp [Shape.extByMap]
  · calc
      (Γ.extByMap f).ctx = Γ.ctx * f := rfl
      _ = Γ.ctx * RepresentableListMap.ofList (f.toFun []) := by
        exact congrArg (fun g => Γ.ctx * g) (map_eq_ofList_toFun (C := C) f)
      _ = (Γ ⋈* f.toFun []).ctx := by
        rw [Shape.extList_ctx]

/-- Cast a base slot through `extByMap`. -/
def Shape.slotByMap {C : Carrier} (Γ : Shape C) (f : RepresentableListMap C.Arity) {α : C.Arity}
    (p : Γ ∋ α) : (Γ.extByMap f) ∋ α := by
  simpa [shape_extByMap_eq_extList (Γ := Γ) f] using (Shape.weakenList Γ (f.toFun []) p)

/-- Cast a slot in `Γ ⋈* τ` through `extByMap`, given `f.toFun [] = τ`. -/
def Shape.slotByList {C : Carrier} (Γ : Shape C) (f : RepresentableListMap C.Arity)
    {τ : List C.Arity} {α : C.Arity} (h : f.toFun [] = τ)
    (p : (Γ ⋈* τ) ∋ α) : (Γ.extByMap f) ∋ α := by
  simpa [h, shape_extByMap_eq_extList (Γ := Γ) f] using p

/-- Cast a `tauSlot` through `extByMap` along an explicit decomposition of `f.toFun []`. -/
def Shape.tauSlotByMap {C : Carrier} (Γ : Shape C) (f : RepresentableListMap C.Arity)
    {β : C.Arity} {τ_above : List C.Arity} {τ_below : List C.Arity}
    (i : C.Binder β) (h : f.toFun [] = τ_above ++ β :: τ_below) : (Γ.extByMap f) ∋ i.arity :=
  Shape.slotByList Γ f h (tauSlot Γ τ_above β τ_below i)

private theorem Shape.base_ne_ext {C : Carrier} (γ : C.BaseShape) (Γ : Shape C) (β : C.Arity) :
    Shape.base γ ≠ Γ ⋈ β := by
  intro h
  have hctx : Γ.ctx.toFun [β] = [] := by
    have hctx' : (Shape.base γ).ctx.toFun [] = (Γ ⋈ β).ctx.toFun [] := by
      exact congrArg (fun Δ : Shape C => Δ.ctx.toFun []) h
    simpa [Shape.base, Shape.ext, RepresentableListMap.id, RepresentableListMap.mul,
      RepresentableListMap.ofList] using hctx'.symm
  have hcons : β :: Γ.ctx.toFun [] = [] := by
    change [β] ++ Γ.ctx.toFun [] = []
    rw [← Γ.ctx.toFun_append [β]]
    exact hctx
  cases hcons

private theorem Shape.ext_inj {C : Carrier} {Γ Δ : Shape C} {α β : C.Arity}
    (h : Γ ⋈ α = Δ ⋈ β) : Γ = Δ ∧ α = β := by
  have hbase : Γ.baseShape = Δ.baseShape := by
    have hbase' := congrArg (fun Ε : Shape C => Ε.baseShape) h
    simpa [Shape.ext] using hbase'
  have hctx_nil : α :: Γ.ctx.toFun [] = β :: Δ.ctx.toFun [] := by
    have hctx' : (Γ ⋈ α).ctx.toFun [] = (Δ ⋈ β).ctx.toFun [] := by
      exact congrArg (fun Ε : Shape C => Ε.ctx.toFun []) h
    have hctx'' : Γ.ctx.toFun [α] = Δ.ctx.toFun [β] := by
      simpa [Shape.ext, RepresentableListMap.mul, RepresentableListMap.ofList] using hctx'
    rw [Γ.ctx.toFun_append [α], Δ.ctx.toFun_append [β]] at hctx''
    simpa using hctx''
  have hhead : α = β := (List.cons.inj hctx_nil).1
  have htail : Γ.ctx.toFun [] = Δ.ctx.toFun [] := (List.cons.inj hctx_nil).2
  cases hhead
  constructor
  · apply Shape.eq_of_fields hbase
    apply RepresentableListMap.ext
    funext l
    rw [Γ.ctx.toFun_append l, Δ.ctx.toFun_append l, htail]
  · rfl

inductive SlotAt.ExtView {C : Carrier} (Γ : Shape C) (β : C.Arity) :
    {α : C.Arity} → SlotAt (Γ ⋈ β) α → Type where
  | here (i : C.Binder β) : SlotAt.ExtView Γ β (SlotAt.here (Γ := Γ) i)
  | there {α : C.Arity} (p : Γ ∋ α) :
      SlotAt.ExtView Γ β (SlotAt.there (Γ := Γ) (β := β) p)

private def SlotAt.extViewAux {C : Carrier} :
    {S : Shape C} → {α : C.Arity} → (p : SlotAt S α) →
    {Γ : Shape C} → {β : C.Arity} → (h : S = Γ ⋈ β) →
    SlotAt.ExtView Γ β (h ▸ p)
  | _, _, .base x, Γ, β, h => by
      exact False.elim (Shape.base_ne_ext _ Γ β h)
  | _, _, .here i, Γ, β, h => by
      have hinj := Shape.ext_inj h
      rcases hinj with ⟨hΓ, hβ⟩
      cases hΓ
      cases hβ
      exact SlotAt.ExtView.here i
  | _, _, .there p, Γ, β, h => by
      have hinj := Shape.ext_inj h
      rcases hinj with ⟨hΓ, hβ⟩
      cases hΓ
      cases hβ
      exact SlotAt.ExtView.there p

def SlotAt.extView {C : Carrier} {Γ : Shape C} {β α : C.Arity}
    (p : SlotAt (Γ ⋈ β) α) : SlotAt.ExtView Γ β p :=
  SlotAt.extViewAux p rfl

@[simp] theorem SlotAt.extView_here {C : Carrier} {Γ : Shape C} {β : C.Arity}
    (i : C.Binder β) :
    SlotAt.extView (SlotAt.here (Γ := Γ) i) = SlotAt.ExtView.here i := by
  dsimp [SlotAt.extView, SlotAt.extViewAux]
  rcases Shape.ext_inj (rfl : Γ ⋈ β = Γ ⋈ β) with ⟨hΓ, hβ⟩
  cases hΓ
  cases hβ
  rfl

@[simp] theorem SlotAt.extView_there {C : Carrier} {Γ : Shape C} {β α : C.Arity}
    (p : Γ ∋ α) :
    SlotAt.extView (SlotAt.there (Γ := Γ) (β := β) p) = SlotAt.ExtView.there p := by
  dsimp [SlotAt.extView, SlotAt.extViewAux]
  rcases Shape.ext_inj (rfl : Γ ⋈ β = Γ ⋈ β) with ⟨hΓ, hβ⟩
  cases hΓ
  cases hβ
  rfl

/-- Position of a slot in `Γ.extByMap f` at arity `α`: either a Γ-slot weakened
through `f`, or a binder whose arity occurs in the representing list of `f`. -/
inductive XPos {C : Carrier} (Γ : Shape C) :
    {f : RepresentableListMap C.Arity} → {α : C.Arity} → SlotAt (Γ.extByMap f) α → Type where
  | base : {f : RepresentableListMap C.Arity} → {α : C.Arity} →
      (p : Γ ∋ α) → XPos Γ (Shape.slotByMap Γ f p)
  | ext : {f : RepresentableListMap C.Arity} → {τ_above : List C.Arity} →
      {β : C.Arity} → {τ_below : List C.Arity} →
      {h : f.toFun [] = τ_above ++ β :: τ_below} →
      (i : C.Binder β) → XPos Γ (Shape.tauSlotByMap Γ f i h)

inductive XPosList {C : Carrier} (Γ : Shape C) :
    (τ : List C.Arity) → {α : C.Arity} → (Γ ⋈* τ ∋ α) → Type where
  | base : {τ : List C.Arity} → {α : C.Arity} → (p : Γ ∋ α) →
      XPosList Γ τ (Shape.weakenList Γ τ p)
  | ext : {τ_above : List C.Arity} → {β : C.Arity} → {τ_below : List C.Arity} →
      (i : C.Binder β) →
      XPosList Γ (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)

def classifyList {C : Carrier} {Γ : Shape C} :
    (τ : List C.Arity) → {α : C.Arity} → (p : Γ ⋈* τ ∋ α) → XPosList Γ τ p
  | [], _, p => by
      simpa [Shape.weakenList] using (XPosList.base (Γ := Γ) (τ := []) p)
  | β :: rest, _, p => by
      change SlotAt ((Γ ⋈* rest) ⋈ β) _ at p
      match SlotAt.extView p with
      | .here i =>
          exact XPosList.ext (Γ := Γ) (τ_above := []) (β := β) (τ_below := rest) i
      | .there p' =>
          match classifyList (Γ := Γ) rest p' with
          | XPosList.base q =>
              simpa [Shape.weakenList] using
                (XPosList.base (Γ := Γ) (τ := β :: rest) q)
          | XPosList.ext (τ_above := ta) (β := b) (τ_below := tb) i =>
              simpa using
                (XPosList.ext (Γ := Γ) (τ_above := β :: ta) (β := b) (τ_below := tb) i)

theorem Shape.slotByList_weakenList {C : Carrier} (Γ : Shape C)
    (f : RepresentableListMap C.Arity) {τ : List C.Arity} {α : C.Arity}
    (h : f.toFun [] = τ) (p : Γ ∋ α) :
    Shape.slotByList Γ f h (Shape.weakenList Γ τ p) = Shape.slotByMap Γ f p := by
  cases h
  rfl

theorem Shape.slotByList_tauSlot {C : Carrier} (Γ : Shape C)
    (f : RepresentableListMap C.Arity) {τ_above : List C.Arity}
    {β : C.Arity} {τ_below : List C.Arity}
    (h : f.toFun [] = τ_above ++ β :: τ_below) (i : C.Binder β) :
    Shape.slotByList Γ f h (tauSlot Γ τ_above β τ_below i) =
      Shape.tauSlotByMap Γ f i h := by
  rfl

private def XPosList.toMap {C : Carrier} {Γ : Shape C}
    (f : RepresentableListMap C.Arity) {τ : List C.Arity} {α : C.Arity}
    {p : Γ ⋈* τ ∋ α} (h : f.toFun [] = τ) (x : XPosList Γ τ p) :
    XPos Γ (Shape.slotByList Γ f h p) := by
  cases x with
  | base q =>
      cases h
      exact XPos.base q
  | ext i =>
      exact XPos.ext (Γ := Γ) (f := f) (h := h) i

/-- Classify a slot in an iterated extension. -/
def classify {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) {α : C.Arity} (p : (Γ ⋈* τ) ∋ α) :
    XPos Γ (Shape.slotByList Γ (RepresentableListMap.ofList τ) (by rfl) p) :=
  XPosList.toMap (Γ := Γ) (f := RepresentableListMap.ofList τ)
    (h := rfl) (classifyList (Γ := Γ) τ p)

/-- Classify a slot in a represented map-extension, by map argument. -/
def classifyMap {C : Carrier} {Γ : Shape C} (f : RepresentableListMap C.Arity) :
    {α : C.Arity} → (p : (Γ.extByMap f) ∋ α) → XPos Γ p := by
  intro α p
  have hshape : Γ.extByMap f = Γ ⋈* f.toFun [] := shape_extByMap_eq_extList (Γ := Γ) f
  let p' : (Γ ⋈* f.toFun []) ∋ α := hshape ▸ p
  have hp : Shape.slotByList Γ f rfl p' = p := by
    have hp₁ : Shape.slotByList Γ f rfl p' ≍ p' := by
      unfold Shape.slotByList
      rw [eq_mpr_eq_cast]
      exact cast_heq _ p'
    have hp₂ : p' ≍ p := by
      subst p'
      exact eqRec_heq (φ := fun S : Shape C => SlotAt S α) hshape p
    exact eq_of_heq (HEq.trans hp₁ hp₂)
  exact hp ▸
    (XPosList.toMap (Γ := Γ) (f := f) (h := rfl)
      (classifyList (Γ := Γ) (τ := f.toFun []) p'))

@[simp] theorem classifyList_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) {α : C.Arity} (p : Γ ∋ α) :
    classifyList (Γ := Γ) τ (Shape.weakenList Γ τ p) =
      XPosList.base (Γ := Γ) (τ := τ) p := by
  induction τ with
  | nil =>
      rfl
  | cons β rest ih =>
      simp [classifyList, Shape.weakenList, SlotAt.extView_there, ih]

@[simp] theorem classifyList_tauSlot {C : Carrier} {Γ : Shape C}
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) :
    classifyList (Γ := Γ) (τ_above ++ β :: τ_below)
      (tauSlot Γ τ_above β τ_below i)
      =
    XPosList.ext (Γ := Γ) (τ_above := τ_above) (β := β) (τ_below := τ_below) i := by
  induction τ_above with
  | nil =>
      simp [classifyList, tauSlot, SlotAt.extView_here]
  | cons δ rest ih =>
      simp [classifyList, tauSlot, SlotAt.extView_there, ih]

theorem classify_weakenList {C : Carrier} {Γ : Shape C}
    (τ : List C.Arity) {α : C.Arity} (p : Γ ∋ α) :
    classify τ (Shape.weakenList Γ τ p) = XPos.base p := by
  unfold classify
  change
    XPosList.toMap (Γ := Γ) (f := RepresentableListMap.ofList τ) (h := rfl)
      (classifyList (Γ := Γ) τ (Shape.weakenList Γ τ p)) = XPos.base p
  rw [classifyList_weakenList]
  simp [XPosList.toMap]

/-- Classifying a `tauSlot` recovers the corresponding `XPos.ext`. -/
theorem classify_tauSlot {C : Carrier} {Γ : Shape C}
    (τ_above : List C.Arity) (β : C.Arity) (τ_below : List C.Arity)
    (i : C.Binder β) :
    classify (τ_above ++ β :: τ_below) (tauSlot Γ τ_above β τ_below i)
      =
    XPos.ext (τ_above := τ_above) (β := β) (τ_below := τ_below) i := by
  unfold classify
  change
    XPosList.toMap (Γ := Γ) (f := RepresentableListMap.ofList (τ_above ++ β :: τ_below))
      (h := rfl)
      (classifyList (Γ := Γ) (τ_above ++ β :: τ_below)
        (tauSlot Γ τ_above β τ_below i)) =
    XPos.ext (τ_above := τ_above) (β := β) (τ_below := τ_below) i
  rw [classifyList_tauSlot]
  simp [XPosList.toMap]

@[simp] theorem Shape.extList_nil {C : Carrier} (Γ : Shape C) : Γ ⋈* [] = Γ := by
  cases Γ
  simp [Shape.extList]

@[simp] theorem Shape.extList_cons {C : Carrier} (Γ : Shape C) (β : C.Arity)
    (rest : List C.Arity) : Γ ⋈* (β :: rest) = (Γ ⋈* rest) ⋈ β := by
  rfl

/-- Associativity of iterated extension w.r.t. list append:
extending by `ys` then by
`xs` equals extending by `xs ++ ys`.  This is now the map-composition form of the
same fact. -/
theorem Shape.extList_append {C : Carrier} (Γ : Shape C) (xs ys : List C.Arity) :
    (Γ ⋈* ys) ⋈* xs = Γ ⋈* (xs ++ ys) := by
  induction xs generalizing Γ with
  | nil =>
      simp [Shape.extList_nil]
  | cons x rest ih =>
      simp [Shape.extList_cons, ih]

/-- Recoverable equation for a shape's context action. -/
theorem shape_ctx_apply {C : Carrier} (Γ : Shape C) (l : List C.Arity) :
    Γ.ctx.toFun l = l ++ Γ.ctx.toFun [] := by
  simpa using Γ.ctx.toFun_append l
