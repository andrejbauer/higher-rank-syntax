# Higher-rank syntax — status report

Snapshot taken 2026-05-12 from the local clone of
`git@github.com:andrejbauer/higher-rank-syntax.git`, after fetching all
remotes.  No files were edited; this report itself is the only new
artefact.

## 1. Where the project sits

The project aims to construct a relative monad whose Kleisli category
captures *higher-rank syntax* — i.e. a finitary algebraic syntax in
which each operation symbol binds a finite list of (sub)operations
that may themselves bind variables, recursively.  In de-Bruijn form,
a context is no longer a flat list of types but a tree of *arities*,
each arity carrying a further tree of arities for the binders below
it.

There are two repositories with the same five branch names:

  - `origin = github.com/andrejbauer/higher-rank-syntax`
    (your repo — branches surveyed in §§2–4 below);
  - `ivan   = github.com/ivankobe/higher-rank-syntax`
    (your student's fork — only `ivan/relative-monad` has divergent
    work, surveyed in §6).

Across the five branches on `origin` the work has migrated formalism:

```
   main  ──►  without-classes  ──►  relative-monad  ──►  local-view
     │
     └──►  structural-recursion          (side branch, abandoned)
```

  - Branch ancestry above is the literal git ancestry
    (`git merge-base` agrees on each step).
  - The Agda work lives on `main` (with the side branch
    `structural-recursion`).  `without-classes` rewrites the Agda once
    more and then everything from there on out leaves the Agda files
    untouched.  `relative-monad` adds a Lean tree.  `local-view`
    starts to convert the Lean substitution code into a new shape and
    then writes an OCaml prototype.
  - The most recent work is the OCaml prototype on `local-view` (last
    commit "Comments in the OCaml code", 2026-05-12).

## 2. Mathematical content

### 2.1 Shapes and arities

A *shape* `γ` is a finite (binary) tree of *arities*, and an *arity*
`α` is itself a shape — so the definitions are mutually recursive but
isomorphic to a single inductive type of finite, unordered trees with
no labels.  In every formalism the tree is presented with the
constructors

  - empty:           `𝟘`,
  - a single slot:   `[α]`  (one arity at the leaf),
  - concatenation:   `γ ++ δ`.

A position in a shape is a path from the root to a leaf
(`Here | Left p | Right p` in the OCaml; `var_in` / `Var` /
`_∈_` in the Agda and Lean).

An *expression in shape γ* applies a variable `x : α ∈ γ` to a tree of
sub-expressions, one for each leaf of α, recursively shape-checked
against `γ ++ β` (where β is the binder shape at that leaf).  This is
the higher-rank analogue of "head normal form": every term is a
variable applied to as many sub-trees as the variable's arity
demands.

### 2.2 The intended relative monad

Variables form a presheaf `𝕁 : Arity ⥤ Type` and expressions form
`𝕋 : Arity ⥤ Type` (both indexed by the ambient shape).  The
substitution structure should make `𝕋` a relative monad along `𝕁`,
with

  - unit         `η_val  : 𝕁 ⇒ 𝕋`        (a variable as an expression),
  - extension   `lift_val : (𝕁 ⇒ 𝕋) ⇒ (𝕋 ⇒ 𝕋)`  (capture-avoiding
                                              substitution),

satisfying the three relative-monad laws (unit_left, unit_right,
comp_lift).  The Kleisli category of this monad is the category of
substitutions between shapes.

### 2.3 The substitution algorithm (now in OCaml)

Given a substitution `f` with

  - `f.pre`  — a common prefix on both sides,
  - `f.dom`  — the domain shape,
  - `f.cod`  — the codomain shape,
  - `f.sub`  — for each `x : α ∈ f.dom`, an expression in
               `(f.pre ++ f.cod) ++ α`,

we define `subst f γ e`, taking `e` valid in `(f.pre ++ f.dom) ++ γ` and
producing an expression in `(f.pre ++ f.cod) ++ γ`.

The recursion splits on **where the head variable `x` lives** —
encoded directly by which branch of the path `x` takes:

  | path of `x`        | meaning                | action                           |
  |--------------------|------------------------|----------------------------------|
  | `Right y`          | `x` is in `γ`          | recurse into the arguments       |
  | `Left (Right y)`   | `x` is in `f.dom`      | substitute, then post-substitute |
  | `Left (Left y)`    | `x` is in `f.pre`      | re-index, recurse into arguments |

The interesting case is the middle one.  After the recursive call on
the children of `x` (which lowers them to `(f.pre ++ f.cod) ++ α`), we
build an auxiliary substitution `g` whose domain is the arity `α`
itself and whose `sub` is the recursively substituted children; we
then apply `g` to `e' = f.sub[x]` (extracted in shape `(f.pre ++ f.cod) ++ α`)
and return the result.

In OCaml this is implemented twice:

  - `ocaml/syntax.ml`     — shapes and arities as **lists**, indices
                            as integers, list lookup with shifting.
  - `ocaml/syntaxTree.ml` — shapes and arities as **binary trees**,
                            indices as tree paths, pattern-matched
                            cleanly.  The substitution body is now
                            a clean three-way case-split on the
                            shape of the path.

Throughout, the recursive `subst` calls happen at strictly smaller
`(f.pre ++ f.dom) ++ (γ ++ α)` *trees*, but the smallness is not on a
single argument: the outer recursion changes `γ` (going under
binders), and the inner one changes both `f.dom` and `e`.  This is
exactly the place where the formalizations have repeatedly hit
termination walls.

## 3. Branch-by-branch

### `main` (Agda, "Working on substitition, still.")

The original Agda formalism, with `Arity = Shape × Class` (operations
carry a *syntactic class* tag), `Expr : Shape → Class → Set`, and
substitution built from `lift : (γ →ʳ δ) → (γ →ˢ δ)` plus a helper
`sbs`.  Termination is asserted by `{-# TERMINATING #-}` and the
proofs `[lift]ˢ` and `[𝟙]ˢ` are unfinished.

### `structural-recursion` (Agda, "Give up on termination.")

A side branch off `main` exploring structural-recursion + Bove-Capretta
approaches (commits "WIP: Capretta-Bove method", "WIP: substitution as
a graph").  The final commit message announces defeat.  Two holes
`{!!}` in `[lift]ˢ` and `[𝟙]ˢ`.

### `without-classes` (Agda + first Lean, "Define the Var and Expr functors")

Drops the `Class` tag from arities (`Arity = Shape`).  The Agda
substitution is the experimental `Focus` (context-zipper) version
with the core `sbs` commented out — clearly mid-pivot.  A small Lean
tree appears with a single `RelativeMonad.lean` file and partial
`Syntax`/`Renaming`/`Substitution`.  This is where the project drops
Agda and switches to Lean.

### `relative-monad` (Lean, "Termination of η_val")

The Lean tree is fleshed out substantially.  Two layers:

  - **Categorical infrastructure**
    (`HigherRankSyntax/HigherRankSyntax/RelativeMonads/*.lean`):
    relative monads, Kleisli triples, relative adjunctions, relative
    algebras, relative Kleisli categories, and an `Examples.lean`.
    None of these files contain `sorry`; they are formally complete
    modulo roadmap comments noting which abstract theorems remain
    (e.g. "every adjunction gives a relative adjunction", "every
    relative adjunction gives a relative monad").
  - **The syntax instance** (`Syntax.lean`, `Renaming.lean`,
    `Substitution.lean`, `SyntaxRelativeMonad.lean`): on this branch
    `Expr` has *two* constructors `applyFree` / `applyBound`, splitting
    free and bound variables explicitly.  `Renaming` is essentially
    complete (two minor `sorry`s).  `Substitution` attempts a mutual
    recursion between an action `act'` and an instantiation `inst'`;
    `inst'` is left stubbed (three `sorry`s).  `SyntaxRelativeMonad`
    has `η_val` defined; `lift_val` and the three relative-monad laws
    are open (five `sorry`s).

### `local-view` (Lean + OCaml, "Comments in the OCaml code")

Reverts the `applyFree` / `applyBound` split to a *single*
`apply (x : α ∈ γ) (ts : …)` constructor — this is what the commit
"trying local views" alludes to: viewing free and bound variables
uniformly through a path into the ambient shape.  This is also the
shape the OCaml prototype uses.  Then:

  - `ocaml/syntax.ml` and `ocaml/syntaxTree.ml` carry the working
    prototype described in §2.3.  `syntax.ml` (list-based) is the
    older draft; `syntaxTree.ml` (tree-based) is the current one.
    The substitution algorithm itself is converted; the two example
    modules `ExampleSubst1` / `ExampleSubst2` at the bottom of
    `syntaxTree.ml` were not updated and still use list syntax
    (`Shape [...]`, integer indices), so the file does not compile
    as-is — the in-line comment on l. 265 acknowledges this.
  - The Lean side has the same categorical infrastructure as
    `relative-monad`.  `Substitution.lean` is mid-rewrite ("Barely
    starting to convert the OCaml code into Lean"); the action is
    stubbed and several intended helpers (`act_left`, `act_right`,
    `act_middle`, `inst_left`, `inst`) are commented out.
  - The Agda src on this branch is **bit-identical to
    `without-classes`** (verified by `git diff --stat`).  It has not
    been touched since the pivot.

## 4. Formalization status, in plain words

  - **Agda** is dormant.  The most-developed Agda is on `main`, with
    `{-# TERMINATING #-}` annotations and unfinished proofs.  The
    side branch `structural-recursion` declares the structural
    approach a dead end.  `without-classes` reflects a half-finished
    pivot in formalism.
  - **OCaml** is the current source of truth for the substitution
    algorithm.  `ocaml/syntaxTree.ml` contains a complete `subst`
    that uses `validate` calls liberally as runtime shape checks —
    these are de-facto invariants that the eventual dependently
    typed Lean version will need to prove.  The bottom-of-file
    examples were not migrated and break compilation.
  - **Lean** has two pieces:
      * Generic relative-monad / Kleisli-triple / relative-adjunction
        infrastructure (`RelativeMonads/*.lean`): formally complete
        (no `sorry`s) but with explicit roadmap items still missing
        (interconversions between adjunctions and monads).
      * Instance for higher-rank syntax (`Syntax`, `Renaming`,
        `Substitution`, `SyntaxRelativeMonad`): on `relative-monad`
        the `applyFree`/`applyBound` formulation has Renaming
        essentially done and Substitution mostly stubbed; on
        `local-view` the formulation has been reverted to a single
        `apply` and substitution is mid-rewrite, tracking the OCaml.
    The relative-monad structure on syntax (`SyntaxRelativeMonad`)
    is not yet up: `lift_val` is open and all three monad laws are
    `sorry`.

## 6. Ivan's fork (`ivan/relative-monad`, 9 commits ahead)

Of Ivan's five tracked branches, only `relative-monad` has divergent
content; the other four are bit-identical to `origin`.  The nine new
commits, in order:

```
45391b5  WIP on unit
5536a52  unit done
56ea3ae  switched to QITs
4e12e91  minor correction
876bf50  unitality of arity concatenation
ffc6037  switch to DeBjurin indices
4cc7c11  shifting arguments to Expr, wip
f30dfde  lifting done
24d0ab6  wip transports
```

The narrative arc is interesting: commit `56ea3ae` briefly tried
making `Shape` a *quotient inductive type*, with path constructors for
the unitality/associativity of `++`, but `ffc6037` walked that back
and replaced the whole edifice with plain de-Bruijn indices.

### 6.1 The current (post-`24d0ab6`) data layout

In `HigherRankSyntax/HigherRankSyntax/Syntax.lean`:

  - `Position` is a notation for `Nat`, and `Nat.toType n := Fin n` —
    so a "position" is the *size* of a list and the elements of a
    position of size `n` are `Fin n`.
  - `Arity` is the inductive type
    ```
    inductive Arity : Type
      | mk : (dom : Position) → (Fin dom → Arity) → Arity
    ```
    i.e. a well-founded tree where each node has finitely many
    children and each child is itself an arity.  `Shape := Arity`.
  - Concatenation `α ++ β` is defined by adding the domain sizes and
    splitting `Fin (m + n)` into the two halves.  `Arity.unitR`,
    `Arity.unitL`, `Arity.assoc` are *proven lemmas* (propositional
    equalities), not constructors.
  - `Expr σ γ α` is a plain inductive (not a QIT) with three
    constructors `sym`, `free`, `bound`.  The signature `Expr σ γ α`
    has *both* an ambient signature `σ`, a context `γ`, and a target
    arity `α`, and the recursive children live in `α ++ β` for
    sub-arities β (so the binder shape grows on the *right* of the
    target arity, not on the context).

In `HigherRankSyntax/HigherRankSyntax/SyntaxRelMon.lean`:

  - `ArityCat`: a category structure on `Arity` whose morphisms are
    arity-preserving functions on positions.
  - `fV σ`: the "free variables" functor `Shape ⥤ (Arity → Type)`.
  - `RelModExpr σ : RelativeMonad (fV σ)`: the intended relative
    monad on `Expr σ`.

### 6.2 Status of the relative monad on `Expr`

`Syntax.lean` (≈ 680 new lines) contains all the plumbing — shift
operations `shiftRightR/L`, `shiftLeftR/L`, conversions `I`, `J`, `L`
that thread through the unitality lemmas, the unit `var`, and the
extension operator `lift`.  These are all defined with explicit
termination proofs (`γ.rank` for variables, `(γ.rank, E.rank)`
lexicographic for `lift`).  Direct check: **`Syntax.lean` contains
zero `sorry`s.**

`SyntaxRelMon.lean` builds the actual `RelativeMonad` record.
Direct check: **5 `sorry`s, all on the equational side**, distributed
as

  - 1 `sorry` for the auxiliary transport lemma
    `shiftRightR_shiftRightL_L`;
  - 1 `sorry` inside the auxiliary lemma `J_sym_wkR_L` (the inner
    rewrite case);
  - 1 `sorry` in the `.free` case of `RelModExpr_unit_right` (the
    first monad law, `lift η = id`);
  - 1 `sorry` for `unit_left`;
  - 1 `sorry` for `comp_lift`.

So at this point the relative-monad *structure* is in place, the
unit and extension are defined, the recursion terminates, and the
*right unit* law is proven up to one rewrite-bound transport (the
`free`-variable case).  The remaining mathematical content is the
two other relative-monad laws plus the two missing transport
lemmas.

### 6.3 How Ivan's branch relates to yours

Ivan's `relative-monad` and your `local-view` are independent
descendants of your `origin/relative-monad`.  They have committed to
two different syntactic representations:

  - **Yours (`local-view`)** is moving the OCaml tree-path
    representation into Lean: shapes/arities are inductive trees
    (`empty | slot | oplus`), positions are paths, free vs. bound is
    a single uniform `apply`.
  - **Ivan's (`ivan/relative-monad`)** uses a `Nat`-sized
    `Arity.mk : (dom : Nat) → (Fin dom → Arity) → Arity` (children
    indexed by `Fin n`, not by a path type), and keeps the
    `sym`/`free`/`bound` three-way split of `Expr`.

Both representations make the unitality lemmas
`α ++ 𝟘 = α`, `𝟘 ++ α = α` provable but not definitional;
Ivan paid that cost up-front and built shift operators that thread
the equalities through, while your OCaml side dodges the cost by
not having to type-check the recursive call.

The `RelativeMonads/*.lean` infrastructure on `ivan/relative-monad`
is unchanged from your `origin/relative-monad`.  Ivan also added a
`.claude/napkin.md` file with a single project-local rule recording
where the Lake package lives.

## 7. Where the next move probably is

  - Either finish the OCaml prototype's example coverage (the two
    `ExampleSubst*` modules) and convert the algorithm faithfully
    into `local-view`'s `Substitution.lean`,
  - or accept the `applyFree`/`applyBound` split of `relative-monad`
    and finish the mutually recursive `act'`/`inst'`, then prove
    termination.

In either branch, the open problems are the same: a structural
termination argument for `subst` (the OCaml uses unchecked
recursion), the three relative-monad laws on `𝕋`, and the
not-yet-glued connection between the syntax instance and the
generic `RelativeMonads/*` infrastructure (so far the syntax files
do not import a `RelativeMonad` and instantiate it — that step is
still pending).

Ivan's `ivan/relative-monad` has already done much of this work in
a separate representation (`Arity = (dom : Nat) → (Fin dom → Arity)`
with `Expr` split into `sym`/`free`/`bound`): the relative-monad
record is constructed, the recursions terminate, and `unit_right` is
proven up to three transport `sorry`s.  The two remaining laws
(`unit_left`, `comp_lift`) and the transport lemmas are the only
open items there.  A pragmatic next move is either to merge from
`ivan/relative-monad` (and finish those proofs) or to decide that
the `local-view` representation is preferable and port Ivan's proof
strategy across — the equations themselves are the same statements,
only the underlying data differs.
