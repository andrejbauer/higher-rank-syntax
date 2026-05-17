# Higher-Rank Syntax — Carrier-Free Action Design

This file is the working plan for the `Action/` refactor.  The first half is the mathematical
description of the structure we are implementing; the second half is the executable step list.

The description is written as a self-contained reference, so it can be lifted directly into a
top-level docstring once the refactor lands.

---

## 1.  Mathematical structure

A higher-rank binding signature describes a syntax in which every variable carries its own
"binder shape": variables are not just names, but heads of trees of fixed arity.  We package
such a signature in a `Carrier`, and build the binding-syntax framework on top.

### 1.1  The `Carrier`

The carrier provides the base, signature-level data:

| Component         | Meaning                                                              |
| ----------------- | -------------------------------------------------------------------- |
| `BaseShape`       | Base context shapes (e.g. raw lists of free-variable names).         |
| `BaseShapeSlot γ` | The variables of base shape `γ`.                                     |
| `Arity`           | Binder shapes — what kind of "thing" a slot abstracts over.          |
| `AritySlot α`     | The binder positions of arity `α`.                                   |
| `baseSlotArity`   | The arity of each base slot.                                         |
| `arityArity`      | The arity of each binder slot of `α`.                                |
| `aritySubWf`      | Well-foundedness of the sub-arity relation induced by `arityArity`.  |

### 1.2  Shape

`Shape C` is the inductive type built from the carrier's base shapes and arities:

```
inductive Shape (C : Carrier) where
  | base : (γ : C.BaseShape) → Shape C
  | ext  : (Γ : Shape C) → (α : C.Arity) → Shape C
```

Notation: `Γ ⋈ α := Shape.ext Γ α` extends a shape by the binders of arity `α`.

### 1.3  Slot

The slots of a shape are inductive, with a constructor for each layer of the shape:

```
inductive Slot {C : Carrier} : Shape C → Type where
  | base  : {γ : C.BaseShape} → (p : C.BaseShapeSlot γ) → Slot (.base γ)
  | here  : {Γ : Shape C} → {α : C.Arity} → (z : C.AritySlot α) → Slot (.ext Γ α)
  | there : {Γ : Shape C} → {α : C.Arity} → (s : Slot Γ) → Slot (.ext Γ α)
```

* `base p` — a slot belonging to the base shape.
* `here z` — one of the binders introduced at this `ext` layer.
* `there s` — a slot inherited from the shape below.

Each slot has an arity, defined by recursion:

```
def Slot.arity {C : Carrier} {Γ : Shape C} : Slot Γ → C.Arity
  | .base p  => C.baseSlotArity p
  | .here z  => C.arityArity z
  | .there s => s.arity
```

`Slot.arity` computes by pattern matching — the equations hold by `rfl`.

### 1.4  Renaming

A renaming `Γ →ʳ Δ` is an arity-respecting slot map:

```
structure Renaming {C : Carrier} (Γ Δ : Shape C) where
  toFun : Slot Γ → Slot Δ
  arity : ∀ (s : Slot Γ), (toFun s).arity = s.arity
```

Identity and composition are immediate.  For each `α : C.Arity` the canonical weakening
`Renaming.weaken : Renaming Γ (Γ ⋈ α)` sends `s` to `Slot.there s`, with the arity proof `rfl`.

### 1.5  Expressions

`Expr Γ` is the free relative-monad type:

```
inductive Expr {C : Carrier} : Shape C → Type where
  | apply : {Γ : Shape C} → (x : Slot Γ)
         → (args : (y : C.AritySlot x.arity) → Expr (.ext Γ (C.arityArity y)))
         → Expr Γ
```

An expression is a head slot `x` together with one child per binder slot of `x`'s arity; the
child lives in `Γ` extended by the binder's arity.

The functorial pieces:

* `Expr.J (Γ : Shape C) (α : C.Arity) := { x : Slot Γ // x.arity = α }` — the variables of
  arity `α` at `Γ`.
* `Expr.T (Γ : Shape C) (α : C.Arity) := Expr (Γ ⋈ α)` — expressions in `Γ` under one
  α-binder.
* `Expr.η {Γ : Shape C} {α : C.Arity} : Expr.J Γ α → Expr.T Γ α` — η-expansion of a variable
  into the unique tree that names it.
* `Renaming` acts on `Expr` by mapping the head slot and recursing into children, using
  `Renaming.arity` to land in the right index.

### 1.6  Substitution, instantiation, Kleisli extension

* `Subst (Γ Δ : Shape C) := (x : Slot Γ) → Expr (Δ ⋈ x.arity)` — slot-indexed substitution.
* `Inst (α : C.Arity) (Γ : Shape C) := (z : C.AritySlot α) → Expr (Γ ⋈ C.arityArity z)` —
  data for instantiating one α-binder above `Γ`.
* `inst {α : C.Arity} {Γ : Shape C} : Inst α Γ → Expr (Γ ⋈ α) → Expr Γ` — α-instantiation.
* `lift {Γ Δ : Shape C} : Subst Γ Δ → Expr Γ → Expr Δ` — Kleisli extension.

Both `inst` and `lift` recurse on `Expr`'s structure, with `Slot`'s `.base` / `.here` /
`.there` constructors giving the case analysis at each head.  Each case reduces by `rfl`.

### 1.7  Relative monad

In the framework of `RelativeMonad/Basic.lean`:

* Source category: `Shape C`, morphisms are renamings.
* Target category: `C.Arity → Type`, morphisms α-pointwise functions.
* `J : Shape C ⥤ (C.Arity → Type)`, `Γ ↦ (α ↦ Expr.J Γ α)`.
* `T : Shape C ⥤ (C.Arity → Type)`, `Γ ↦ (α ↦ Expr.T Γ α)`.
* Unit `η` and lift as above.

The relative-monad laws (`unit_right`, `unit_left`, `comp_lift`) hold by induction on
`Slot` / `Expr`, with constructor-based case analysis available directly.

---

## 2.  Refactor plan

The refactor proceeds bottom-up: change `Carrier`, then introduce `Shape` / `Slot`, then port
`Expr` and downstream.  Each step ends with a successful
`lake build HigherRankSyntax.Action.<file>` on the touched file.

1.  **`Action/Carrier.lean`** — base data only.
    * `Carrier` exposes `BaseShape`, `BaseShapeSlot`, `baseSlotArity`, `Arity`, `AritySlot`,
      `arityArity`, `aritySubWf`.

2.  **`Action/Shape.lean`** (new file).
    * `inductive Shape (C : Carrier)` with `base` / `ext`; notation `Γ ⋈ α := Shape.ext Γ α`.
    * `inductive Slot {C : Carrier} : Shape C → Type` with `base` / `here` / `there`.
    * `def Slot.arity`.

3.  **`Action/Renaming.lean`** — re-implement.
    * `structure Renaming {C : Carrier} (Γ Δ : Shape C)` with `toFun` and `arity`.
    * `Renaming.id`, `Renaming.comp`, category laws.
    * `Renaming.weaken : Renaming Γ (Γ ⋈ α)` via `Slot.there`.

4.  **`Action/Expr.lean`** — re-implement.
    * `inductive Expr {C : Carrier} : Shape C → Type` with the single constructor `apply`.
    * `Expr.J`, `Expr.T`, `Expr.η`.
    * `Renaming.actExpr`, with `Expr.J.map` / `Expr.T.map` functoriality lemmas.
    * `Expr.Subterm` inductive and its `WellFounded` proof / `WellFoundedRelation` instance.

5.  **`Action/Subst.lean`** — re-implement.
    * `Subst`, `Inst`.
    * `inst` and `lift`, each by structural recursion on `Expr` (with `aritySubWf` on the
      Arity side where needed), packaged via the `Expr.Subterm` well-founded relation.
    * Case analysis at each head is direct pattern matching on `Slot`.

6.  **`Action/SyntaxMonad.lean`** — re-fit.
    * `ShapeCat`, `ArityType`, `ArityTypeCat` adapt straightforwardly.
    * `J`, `T`, `Subst.ofKleisli`, `lift_morph` carry over.
    * The three relative-monad laws (`unit_right`, `unit_left`, `comp_lift`) by induction on
      `Slot` / `Expr`.

7.  **README + docstrings** — update `Action/README.md` and the file headers to describe the
    structure as in §1.

8.  **Commit boundary** — one commit per step is fine; the final commit closes out the three
    relative-monad laws.

### Stop conditions

* First wall (typeclass-stuck, motive-not-type-correct, an induction principle that doesn't
  fire, an unexpected case in a pattern match) — stop and report.
* Any deviation from the step list — stop and report.

### Out of scope

* `RelativeMonad.Hom` and the category of relative monads on `J`.
* Translation between syntaxes (the `Hom`-based translation layer).
* Anything in `src/` or `_build/`.
