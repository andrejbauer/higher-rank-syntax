# Plan: Lean development of higher-rank syntax with substitution

## Goal

Build a Lean library for higher-rank binding syntax — expressions whose head positions carry arities (lists of binders), with a substitution operation that respects the binder structure.  The endpoint is an instance of `RelativeMonad` (from `HigherRankSyntax/RelativeMonads/RelativeMonad.lean`) on a J-functor whose objects are variables (slots of a given arity in a given shape) and whose action is `Expr`.

## File structure

  - `HigherRankSyntax/HigherRankSyntax/Action/Carrier.lean` — the `Carrier` typeclass.
  - `HigherRankSyntax/HigherRankSyntax/Action/Expr.lean` — the `Expr` inductive, basic operations on it.
  - `HigherRankSyntax/HigherRankSyntax/Action/Subst.lean` — the substitution data type and the `subst` algorithm with termination.
  - `HigherRankSyntax/HigherRankSyntax/Action/RelMonad.lean` — the relative-monad instance and proofs of the three laws.

One file per concern.  Everything lives under a fresh `Action/` namespace.

## 0. The Carrier as a pair of containers

The structure has a clean reading in container terms (Abbott–Altenkirch–Ghani), worth keeping in view as we build out.

The Carrier exposes **two containers** in the standard "shapes-and-positions" sense `S ◅ P`, with interpretation `⟦S ◅ P⟧ X = Σ s : S, P s → X`.  Both carry an extra *position-decoration* into `Arity`:

  - **Shape container** `Shape ◅ ShapeSlots` with decoration `shapeArity : (γ : Shape) → ShapeSlots γ → Arity`.  The decorated interpretation `⟦Shape ◅ ShapeSlots, shapeArity⟧ : (Arity → Type) → (Shape → Type)` is `X γ ↦ Σ x : ShapeSlots γ, X (shapeArity γ x)` — at every shape γ, the data is a choice of head-slot together with an X-value of matching arity at every position introduced by that head.

  - **Arity container** `Arity ◅ AritySlots` with decoration `arityArity : (α : Arity) → AritySlots α → Arity`.  Same shape of data, one level down: an arity is a "node" with sub-arities at its positions.  Decorated interpretation: `X α ↦ Σ y : AritySlots α, X (arityArity α y)`.

The two containers share **the same position-decoration type** (`Arity`), which is what lets the action structure couple them.

On top of these two containers sits the **action** `∷ : Shape × Arity → Shape`, with the slot-equivalence

```
slots (γ ∷ α) ≃ slots γ ++ AritySlots α
```

and the single `shapeArity` compatibility law

```
shapeArity (γ ∷ α) = Sum.elim (shapeArity γ) (arityArity α) ∘ slotsExt γ α
```

i.e. the decoration of the extended container is the **copair** of the two original decorations along `slotsExt`.  In container language this is *naturality of the position-decoration under the action* — a coherence on top of the two-container data.

What this perspective predicts:

  - **`Expr` is the free relative monad of `Shape ◅ ShapeSlots` (with `shapeArity` decoration), with the action handling binding.**  The inductive `Expr γ α = apply x args …` is the standard W-type for that container, with the recursive call's *shape index* shifted by `∷ (arityArity _ y)` — the difference between the free monad of a plain container (no binding) and the free relative monad of a container with an action (binding).
  - **`subst` is the Kleisli extension of that relative monad.**  Termination is the lex product of the W-types' well-founded sub-structure relations: descend on the arity container (the aux step) or on the shape-container-W-type (the children step).
  - **`ηVar` is constructed by recursion on the arity container.**  A variable-as-expression at slot `x` of arity `α = shapeArity γ x` is `apply x (η-expanded children)`, where each child is built by induction on the *arity*-W-type — exactly the unit of a free relative monad.
  - **The three relative-monad laws** follow from container-theoretic naturality plus the carrier's compatibility laws.  The hardest one (`comp_lift`) is essentially distributivity of Kleisli extension over container morphisms.

References:

  - Abbott, Altenkirch, Ghani — *Containers: Constructing strictly positive types* (2005).  Containers and W-types.
  - Altenkirch, Chapman, Uustalu — *Monads need not be endofunctors* (2010) and *Relative monads formalised* (2014).  The relative-monad framing of binding signatures.
  - Hancock, McBride — *interaction structures* / directed containers.  The "container with position-decoration into the parameter type" is the directed-container view.

The container layer is not formalised separately; mathlib's polynomial-functor/W-type machinery exists but using it would be a separate project.  Framing each definition and law in container terms in the file-level docstrings keeps the structure visible.

## 1. The `Carrier` typeclass

Every "slot of γ" is a member of a shape-indexed type, and the slot algebra collapses to one `Equiv` plus an arity-compatibility equation.

```lean
class Carrier where
  Shape : Type
  Arity : Type
  ShapeSlots : Shape → Type
  AritySlots : Arity → Type
  shapeArity (γ : Shape) : ShapeSlots γ → Arity
  arityArity (α : Arity) : AritySlots α → Arity
  /-- The one-step sub-arity relation is well-founded: descending
      through `arityArity` (taking `arityArity α y` for some
      `y : AritySlots α`) cannot continue forever. -/
  aritySubWf : WellFounded
    (fun α' α => ∃ y : AritySlots α, arityArity α y = α')
  ext : Shape → Arity → Shape
  slotsExt : (γ : Shape) → (α : Arity) →
              ShapeSlots (ext γ α) ≃ ShapeSlots γ ++ AritySlots α
  /-- The decoration of the extended container is the copair (along
      `slotsExt`) of the two original decorations on the left and
      right summands. -/
  slotsExtCompat : ∀ γ α (s : ShapeSlots (ext γ α)),
    shapeArity (ext γ α) s = Sum.elim (shapeArity γ) (arityArity α) (slotsExt γ α s)
```

The algorithm builds dependent families `(y : AritySlots α) → …` without enumeration, so no finiteness is assumed on `AritySlots` or `ShapeSlots`.  Termination consumes `aritySubWf` directly.

Notation `γ ∷ α := Carrier.ext γ α`.  The infix character is open — anything that doesn't clash with mathlib (`**` clashes with `HPow`).

Derived:

```lean
def extList (γ : Shape) : List Arity → Shape
  | [] => γ
  | α :: rest => extList γ rest ∷ α    -- cons-as-snoc
infixl:67 " ++ " => extList
```

`γ ++ [] = γ` and `γ ++ (α :: rest) = (γ ++ rest) ∷ α` hold by `rfl`.

Two example instances:

  - `ListCarrier` — `Shape = List Arity`, `AritySlots α = Fin α.length`, `ShapeSlots γ = Fin γ.length`, `ext xs α := xs ++ α.toList`, `slotsExt` is `Fin.addCases`-shaped.  `γ ∷ emptyArity = γ` definitionally.
  - `TreeCarrier` — `Shape`/`Arity` are mutually inductive trees, `ShapeSlots`/`AritySlots` defined by recursion on the tree, `ext` builds `Oplus`, `slotsExt` matches the `L`/`R` structure.  `γ ∷ emptyArity` is not `rfl`-equal to `γ` — the honest case, no smart constructors involved.

For both instances `aritySubWf` is automatic from the inductive structure of `Arity`.

## 2. The `Expr` inductive

Arity-indexed, to land properly in the relative monad:

```lean
inductive Expr [C : Carrier] : C.Shape → C.Arity → Type where
  | apply (γ : C.Shape) (x : C.ShapeSlots γ)
          (args : (y : C.AritySlots (C.shapeArity γ x)) →
                  Expr (γ ∷ C.arityArity _ y) (C.arityArity _ y))
        : Expr γ (C.shapeArity γ x)
```

Strict positivity: the recursive use of `Expr` sits under a dependent function whose domain (`C.AritySlots …`) is independent of `Expr`.  Lean accepts.

Every `Expr γ α` is well-formed by construction.

Two well-founded relations carry termination for the development:

  - **Sub-expression relation on `Expr`.**  `e' ≺ e` iff `e = apply _ _ args` and `e' = args y` for some `y`.  Well-founded by the structural induction principle of `Expr` (the recursive `args y` is a subterm in the strict-positivity sense).
  - **Sub-arity relation on `Arity`.**  `α' ≺ α` iff `∃ y, arityArity α y = α'`.  Well-founded by the carrier field `aritySubWf`.

## 3. The substitution

A substitution from `γ ∷ α` to `γ ++ δ` is a dependent function on slots:

```lean
def Substitution [C : Carrier] (γ : C.Shape) (α : C.Arity) (δ : List C.Arity) : Type :=
  (s : C.ShapeSlots (γ ∷ α)) →
    Expr (γ ++ δ) (C.shapeArity (γ ∷ α) s)
```

`σ` assigns, to every slot of the input shape `γ ∷ α`, an expression of matching arity in the output shape `γ ++ δ`.  Split along `slotsExt γ α`:

  - For a slot in the γ-summand (`(slotsExt γ α).symm (.inl _)`), `σ` typically returns the η-expansion of that slot as a variable in `γ ++ δ` — γ-slots map to themselves.
  - For a slot in the α-summand (`(slotsExt γ α).symm (.inr _)`), `σ` returns the substitution image — the expression that replaces the α-binder's slot.

The `α`-parameter carries the termination measure for §4: it shrinks along the sub-arity relation in the aux step.

## 4. The `subst` algorithm

```lean
def subst {γ : C.Shape} {α : C.Arity} {δ : List C.Arity}
          (σ : Substitution γ α δ) (τ : List C.Arity) {β : C.Arity}
          (e : Expr ((γ ∷ α) ++ τ) β) :
          Expr ((γ ++ δ) ++ τ) β
```

`β` rides through — substitution preserves the head's arity.

The recursion:

  - Destructure `e = apply x args`.
  - For each `y : AritySlots (shapeArity _ x)`: `newArgs y := subst σ (arityArity _ y :: τ) (args y)`.
  - Classify `x` by walking `τ` cons-by-cons.  At `τ = []` apply `(slotsExt γ α).symm` to split `x` into `.inl p` (γ-side) or `.inr z` (α-side).  Each peeled τ-layer also splits `.inl`/`.inr` (into the layer's binder or into the body below).  The walk lifts the resulting head-slot through each peeled layer on the way back.
  - Three reassembly cases:
      - **γ-side**: head becomes `shiftThrough γ δ p` (the iterated `slotsExt .inl`-injection through the δ-extensions); reassemble as `apply head newArgs`.
      - **τ-layer**: head stays at the relevant τ-position (with per-layer shifts applied during classify); reassemble as `apply head newArgs`.
      - **α-side**: let `ez := σ ((slotsExt γ α).symm (.inr z)) : Expr (γ ++ δ) (arityArity α z)`.  Build `σ' : Substitution (γ ++ δ) (arityArity α z) τ` inline: `slotsExt`-decompose a slot of `(γ ++ δ) ∷ arityArity α z`; on the `(γ ++ δ)`-side return `ηVar` lifted through `τ` via `shiftThrough`; on the `arityArity α z`-side return `newArgs`.  Recurse: `subst σ' [] ez`.

Termination: `termination_by α e` with `Prod.Lex` of the sub-arity and sub-expression relations from §2.  The children call holds `α` fixed and shrinks `e` (each `args y` is a direct subterm).  The aux call uses `α' := arityArity α z`, a one-step sub-arity of `α` with witness `⟨y, rfl⟩` for `aritySubWf`.

## 5. The relative monad

Instantiate `RelativeMonad` (from `RelativeMonads/RelativeMonad.lean`):

```lean
structure RelativeMonad (J : A ⥤ E) where
  map : A → E
  η (X) : J.obj X ⟶ map X
  lift {X Y} (f : J.obj X ⟶ map Y) : map X ⟶ map Y
  unit_right : ∀ X, lift (η X) = 𝟙 (map X)
  unit_left : ∀ f, f = η _ ≫ lift f
  comp_lift : ∀ f g, lift (f ≫ lift g) = lift f ≫ lift g
```

Setup:

  - **A = C.Shape**, the category of shapes.  Morphisms: arity-respecting slot maps `(f : ShapeSlots γ → ShapeSlots δ)` with `∀ s, shapeArity γ s = shapeArity δ (f s)`.
  - **E = C.Arity ⥤ Type** (or `C.Arity → Type` with pointwise maps; choice depends on whether `J` should be renaming-natural).
  - **J : C.Shape ⥤ E** sending `γ` to `α ↦ { s : ShapeSlots γ // shapeArity γ s = α }`.  On morphisms: post-compose the slot map.
  - **T = Expr** as object map: `γ ↦ α ↦ Expr γ α`.

Unit and lift:

```lean
def ηVar (γ : C.Shape) (α : C.Arity)
          (s : { s : C.ShapeSlots γ // C.shapeArity γ s = α }) : Expr γ α := …
-- apply s.val (η-expanded children), recursing on the arity.

def lift {γ δ : C.Shape}
         (f : ∀ α, { s : ShapeSlots γ // shapeArity γ s = α } → Expr δ α)
         (α : C.Arity) (e : Expr γ α) : Expr δ α := …
```

`Substitution γ α δ` (§3) is the Kleisli morphism for source `γ ∷ α` and target `γ ++ δ`.  `subst` (§4) is `lift` specialised to that source, with `α` carrying the termination measure.  The general `lift` runs the same algorithm with `α := emptyArity` — no aux step then arises on the α-side.

## 6. Theorems

In order of dependency:

**Carrier-level lemmas** (mostly `rfl` or one-line `Equiv` cancellations):

  - `extListNil : γ ++ [] = γ`     `(rfl)`
  - `extListCons : γ ++ (α :: rest) = (γ ++ rest) ∷ α`     `(rfl)`
  - `slotsExtInlApplySymm : (slotsExt γ α).symm (.inl s) = …`     (inverse property of `Equiv`)

**Well-foundedness facts**:

  - The sub-arity relation `α' ≺ α := ∃ y, arityArity α y = α'` is well-founded — `aritySubWf` (§1).
  - The Expr-subterm relation is well-founded — automatic from the inductive structure of `Expr`.

**`subst` lemmas** (equational):

  - `substApply : subst σ τ (apply x args) = apply head (subst σ (β :: τ) ∘ args)` — for the appropriate `head` per classify case.
  - `substVarDom : subst σ [] (ηVar (γ ∷ α) … ((slotsExt γ α).symm (.inr z))) = σ (.inr z)`.
  - `substVarPre : subst σ τ (ηVar … (slot in γ)) = …` — matching the γ-side lifting.

**Three relative-monad laws**:

  - **`unit_right`**: `lift ηVar = id`.  Structural induction on `Expr γ α`.  Children are recursively `id`-substituted; the head, when classified as γ-side (each slot maps to itself), reassembles to the same slot.  Discharges via `slotsExt` inverse cancellations.
  - **`unit_left`**: `ηVar ; (lift f) = f`.  Trivial — `subst` on a `var` expression at arity α looks up `f` at that slot.
  - **`comp_lift`**: `lift (f ; lift g) = lift f ; lift g`.  Structural induction.  The most substantive proof: the induction threads through two substitutions, each contributing aux steps along the sub-arity relation.

Estimated proof difficulty: `unit_left` trivial, `unit_right` moderate (well-founded induction on the lex product of the sub-arity and Expr-subterm relations), `comp_lift` hard.

## 7. Design decisions

  - **Finiteness of `AritySlots`**: not assumed.  The algorithm builds dependent families pointwise; termination needs only the sub-arity well-founded relation (`aritySubWf`).
  - **Category structure on `Shape`**: arity-respecting slot maps.  Morphisms `γ ⟶ δ` are `(f : ShapeSlots γ → ShapeSlots δ)` with `∀ s, shapeArity γ s = shapeArity δ (f s)`.  Required for renamings (the inclusions `γ ⟶ γ ∷ α`, σ.cod-shifts) to be morphisms.
  - **Substitution form**: a single dependent function on slots — `Substitution γ α δ` is the relative-monad Kleisli morphism for source `γ ∷ α`, target `γ ++ δ`.

## 8. Open issues

  - **`ηVar`'s body.**  Constructing a variable-as-expression requires η-expanding the children — another well-founded recursion on the sub-arity relation, same shape as `subst`'s outer measure.  Manageable but adds a definition.
  - **Shape of `J`.**  The existing `SyntaxRelativeMonad.lean` defines its J on a `Var γ δ` that packs each variable with a renaming `(α, var, ren : α →ʳ δ)`; `Substitution γ α δ` here does not carry a renaming.  Either (a) match that shape and reformulate `Substitution` accordingly, or (b) define a renaming-free `J` and instantiate `RelativeMonad` on that.  A small re-arrangement either way; settle when implementing §5.

## 9. Suggested incremental path

  1. `Carrier.lean` — the typeclass and `ListCarrier` instance.  Verify it elaborates.
  2. Define `extList` and check `rfl`-reductions.
  3. `Expr.lean` — the inductive; state the sub-expression and sub-arity well-founded relations.
  4. `Subst.lean` — `Substitution` and `subst` with well-founded recursion.
  5. Translate the `ExampleSubst1`/`2` cases from `ocaml/syntaxAction2.ml` to check `subst` against expected outputs.
  6. `RelMonad.lean` — `ηVar`, `lift`, and the three relative-monad laws.

Steps 1–3 are mostly definitional.  Step 4 is where well-founded recursion needs careful termination clauses.  Step 6 is the bulk of the proof work.

## 10. Git workflow

The `RelativeMonad` framework lives on the `relative-monad` branch (six files under `HigherRankSyntax/HigherRankSyntax/RelativeMonads/`).  `main` is a fast-forward ancestor of `relative-monad`, which also adds WIP syntax files on top (`Renaming.lean`, `Substitution.lean`, `Syntax.lean`, `SyntaxRelativeMonad.lean` — the last has `sorry`s).

Two options for getting the framework onto `main`:

  - **A. Fast-forward merge `relative-monad` into `main`.**  `git checkout main && git merge --ff-only relative-monad`.  Brings the framework and the WIP syntax work.  Simple; `main` then carries `sorry`s in `SyntaxRelativeMonad.lean`.
  - **B. Cherry-pick only the framework commits.**  Apply only the commits that touch `RelativeMonads/` (plus the lake-project skeleton: `lakefile.toml`, `lean-toolchain`, `HigherRankSyntax.lean`, `lake-manifest.json`).  `main` ends up with the framework only.

Either way, branch off `main` to a fresh branch (e.g., `action`) for the present development under the `Action/` namespace.  The new branch depends only on `RelativeMonads/RelativeMonad.lean`.

## 11. Coding style

Apart from the general advice in global memory:

* Write comments that explain the formalization and relate the concrete development to
  the categorical structure, containers and relative monads, even in case we're not formalizing
  such structure explicitly (analogous to section `0` above). Make sure the comments can be
  understood by someone who is not privy to our conversation. Do not over-explain design decisions,
  no negatives such as "we don't use finite rank".

* If you hit a serious obstacle in formalization, don't deep dive. Instead you should stop and report back to me.

* Make intermediate commits, obviously on the separate branch that you're plannign to make.

* The formalization should be clean: no hacking, keep things straightfowrard, don't use nasty classical stuff, whenever possible, produce direct constructions.

## 12. Cleanup tasks

* **[DONE]** No nested-namespace blocks; use dotted names and dot notation.
  Drop the `namespace Carrier`, `namespace Renaming`, `namespace
  Expr` blocks inside `namespace Action`.  Everything in the
  `Action/` directory lives in a single `namespace Action`.  Names
  with dot prefixes (`Renaming.id`, `Renaming.comp`,
  `Renaming.extend`, `Carrier.extList`) stay — the dot is just
  punctuation in the identifier, not a namespace-block requirement.
  Scoped notations (`∷`, `++`, `→ʳ`) live at the `Action` scope;
  consumers `open scoped Action` to bring them in.

  At call sites, **use dot notation**: write `f.extend β`,
  `f.comp g`, `f.actExpr e` rather than `Renaming.extend f β`,
  `Renaming.comp f g`, `Renaming.actExpr f e`.

* **[DONE]** Rename `Expr.rename` to `Renaming.actExpr`.  This places the
  action of a renaming on an expression alongside the other
  renaming-related definitions, and matches the existing
  `Renaming.lean`'s `actFree`/`actBound` convention.  Companion
  lemmas follow: `Renaming.actExpr.map_id`,
  `Renaming.actExpr.map_comp`, `Renaming.actExpr_applyAtArity`
  (or whatever name fits the bridge lemma after the
  `applyAtArity` rename below).

* **[DONE]** Use the `CoeFun` for `Renaming`.  The `CoeFun` instance is
  already declared, so `f x` should work where `f : γ →ʳ δ` and
  `x : ShapeSlots γ`.  Drop the explicit `.toFun` at every call
  site (`f.toFun x` → `f x`).

* **[DONE]** Rename `applyAtArity` to `Expr.apply'`.  Short name in the
  same namespace as `Expr.apply`.  Primed form signals "the
  variant with an explicit arity proof".  Renames the companion
  lemmas accordingly (`Expr.apply'_rfl`,
  `Renaming.actExpr_apply'`).

* **[DONE — verdict: keep]** Experiment: make `apply'` the primary
  constructor.  Performed and kept: `Expr` inductive now takes
  `apply'` (with explicit `α` and `hα`) as its sole constructor,
  and `apply x args` is a derived `@[reducible] def`.  Outcome
  matched the hypothesis:

  - The transport plumbing (`arityArity_eq_rec`, the helper
    definition of `apply'`, `apply'_rfl`, and the bridge lemma
    `Renaming.actExpr_apply'`) disappears entirely.
  - `Renaming.actExpr`, `Expr.η`, and the functoriality lemmas
    build/destruct expressions directly via `apply'`.
  - `Renaming.actExpr.map_comp` simplifies: both sides reduce to
    `apply'` expressions agreeing on head/arity/children-pointwise,
    differing only in a proof-irrelevant arity proof; `congr 1`
    closes the proof difference.
  - File shrinks from ~207 to ~144 lines (≈30%).

  Cost: structural pattern-matches bind four names
  (`x α hα args`) instead of two, but `α` and `hα` are recovered
  data that downstream callers would have asked for anyway.

* **[DONE]** Notations for renamings.  Add scoped notations in
  `namespace Action`, with `ʳ` consistently on the right of each
  operator to mark "the renaming version":

  ```lean
  scoped notation "𝟙ʳ"  => Renaming.id                -- identity
  scoped infixr:90 " ∘ʳ " => fun g f => Renaming.comp f g
                                                       -- `g ∘ʳ f` = "g after f"
                                                       -- (reverses textual order
                                                       --  vs `Renaming.comp f g`)
  scoped infixl:95 " ⇑ʳ " => Renaming.extend           -- extend through binder
  scoped notation:60 "⟦" f "⟧ʳ " e:61 => Renaming.actExpr f e   -- action on Expr
  ```

  The existing `→ʳ` for the `Renaming` type stays.  The
  `Renaming.lean` framework file uses the same conventions
  (`actFree` notated `⟦ f ⟧ʳ e`, etc.); placing `ʳ` on the right
  matches "f acts on the right of the symbol".

* **[DONE]** Named projections for `slotsExt`.  Introduce two abbreviations
  in `Carrier` (or alongside) that wrap the inverse equivalence:

  ```lean
  def Carrier.inlSlot (C : Carrier) (γ : C.Shape) (α : C.Arity) :
      C.ShapeSlots γ → C.ShapeSlots (γ ∷ α) :=
    fun p => (C.slotsExt γ α).symm (.inl p)

  def Carrier.inrSlot (C : Carrier) (γ : C.Shape) (α : C.Arity) :
      C.AritySlots α → C.ShapeSlots (γ ∷ α) :=
    fun y => (C.slotsExt γ α).symm (.inr y)
  ```

  Currently `(C.slotsExt γ α).symm (.inl _)` and
  `(C.slotsExt γ α).symm (.inr _)` appear at many sites (η, extend,
  shiftThrough, the private `shapeArity_symm_inl/inr` helpers).
  Using `inlSlot` / `inrSlot` shortens each site and makes the
  constructor intent explicit.  The `.symm` of `slotsExt` stays in
  exactly two places — the definitions of these two projections.

  The compatibility law `slotsExtCompat` keeps the existing
  decompose direction (forward `slotsExt`).  Companion simp lemmas:

  ```lean
  @[simp] theorem shapeArity_inlSlot : shapeArity (γ ∷ α) (inlSlot γ α p) = shapeArity γ p
  @[simp] theorem shapeArity_inrSlot : shapeArity (γ ∷ α) (inrSlot γ α y) = arityArity α y
  ```

  These subsume the current private `shapeArity_symm_inl/inr`.

## 13. Toward `lift`: the Kleisli extension

This section pins down the relative-monad structure precisely.  It
commits to **types**.  It does **not** commit to the body of
`Subst.extend`, the body of `lift`, the termination measure, or the
existence and shape of any auxiliary structure — those depend on
how the lift recursion is written and will be settled as the code
is written.

### 13.0 The relative monad

Fix a carrier `C : Carrier`.

**Source category:** `C.Shape` with morphisms `Renaming γ δ`
(already defined; identity `Renaming.id`, composition
`Renaming.comp`).

**Target category:** `C.Arity → Type` with `C.Arity` **discrete**.
Morphisms in this category collapse to Pi families
`(α : C.Arity) → F α → G α`.  We use the Pi form throughout (no
`CategoryTheory.NatTrans`).

**The J functor.**

```lean
def Expr.J {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  { x : C.ShapeSlots γ // C.shapeArity γ x = α }
```

(Already defined.)

**The T functor.**

```lean
abbrev Expr.T {C : Carrier} (γ : C.Shape) (α : C.Arity) : Type :=
  Expr (γ ∷ α)
```

(Already defined.)

**The unit.**

```lean
def Expr.η {C : Carrier} :
    (γ : C.Shape) → (α : C.Arity) → Expr.J γ α → Expr.T γ α
```

(Already defined.)

**The lift (to be defined; full type as in §13.4).**

```lean
def lift {C : Carrier} {γ δ : C.Shape}
    (σ : Subst γ δ) : (α : C.Arity) → Expr.T γ α → Expr.T δ α
```

where `Subst γ δ` is defined in §13.2 as
`(α : C.Arity) → Expr.J γ α → Expr.T δ α`.

### 13.1 `Renaming.weaken`

The canonical inclusion of `γ` into `γ ∷ β` as the γ-summand of
the slot equivalence.

```lean
def Renaming.weaken {C : Carrier} (γ : C.Shape) (β : C.Arity) :
    γ →ʳ γ ∷ β
```

### 13.2 `Subst`

The Kleisli-morphism type: a `J γ ⟶ T δ` natural transformation,
which in our Pi presentation is

```lean
def Subst {C : Carrier} (γ δ : C.Shape) : Type :=
  (α : C.Arity) → Expr.J γ α → Expr.T δ α
```

### 13.3 `Subst.extend`

Extension of a substitution through a fresh binder of arity `β`:

```lean
def Subst.extend {C : Carrier} {γ δ : C.Shape}
    (σ : Subst γ δ) (β : C.Arity) : Subst (γ ∷ β) (δ ∷ β)
```

The body — which γ-side and β-side cases produce, and what
auxiliary renamings/lemmas it uses — will be settled when the lift
is being implemented and we see what `lift` actually requires of
this operation.

### 13.4 `lift`

The Kleisli extension:

```lean
def lift {C : Carrier} {γ δ : C.Shape}
    (σ : Subst γ δ) : (α : C.Arity) → Expr.T γ α → Expr.T δ α
```

i.e. `lift σ α e : Expr (δ ∷ α)` for `e : Expr (γ ∷ α)`.

The body, the recursion strategy, the termination measure, and
whether an auxiliary "graft" operation is needed (and if so what
form it takes) are all to be determined when this is written.

### 13.5 The three relative-monad laws

Each law is a fully quantified proposition.  All variables are
stated explicitly.

* **unit_left** — pointwise form of `lift σ ∘ η = σ`:

  ```lean
  ∀ {C : Carrier} {γ δ : C.Shape} (σ : Subst γ δ)
      (α : C.Arity) (x : Expr.J γ α),
    lift σ α (Expr.η γ α x) = σ α x
  ```

* **unit_right** — pointwise form of `lift η = id`:

  ```lean
  ∀ {C : Carrier} {γ : C.Shape} (α : C.Arity) (e : Expr.T γ α),
    lift (Expr.η γ) α e = e
  ```

* **comp_lift** — pointwise form of `lift (lift τ ∘ σ) = lift τ ∘ lift σ`:

  ```lean
  ∀ {C : Carrier} {γ δ ε : C.Shape}
      (σ : Subst γ δ) (τ : Subst δ ε)
      (α : C.Arity) (e : Expr.T γ α),
    lift (fun α' x => lift τ α' (σ α' x)) α e
      = lift τ α (lift σ α e)
  ```

Each law's proof strategy is **not** specified here; it will
depend on the body of `lift`.