# PLAN - Simple Types for Higher-Rank Syntax

## Goal

Refactor the raw higher-rank syntax formalization so expressions are
intrinsically indexed by a simple result type.

The key design is to keep arities as context-extension shapes and add a
separate type index to slot fibres:

```lean
slotAt : Arity -> Arity -> Ty -> WellOrder
```

This is not just the old carrier applied to `Arity × Ty`: the current carrier
requires `Arity : Submonoid (Function.End A)`, while a bare `Ty` has no
canonical endofunction or monoid structure. The refactor separates the two
roles:

* `Arity`: monoidal context-extension/binding shape.
* `Ty`: result type/sort of expressions.

## Carrier Interface

Change `Carrier` to:

```lean
structure Carrier (A : Type) where
  Ty : Type
  Arity : Submonoid (Function.End A)
  slotAt : Arity -> Arity -> Ty -> WellOrder
  unit_empty : forall alpha tau, IsEmpty (slotAt 1 alpha tau)
  slotAt_mul :
    forall Gamma Delta alpha tau,
      Sum.Lex (slotAt Gamma alpha tau).r (slotAt Delta alpha tau).r
        ≃r (slotAt (Gamma * Delta) alpha tau).r
  subWf :
    WellFounded (fun Delta Gamma =>
      exists tau : Ty, Nonempty (slotAt Gamma Delta tau))
```

Use typed slot notation throughout the codebase:

```lean
notation:35 Gamma " ∋[" tau "] " alpha => SlotAt Gamma alpha tau
```

`Ext` and `⋈` remain unchanged:

```lean
abbrev Ext (Gamma Delta : C.Arity) : C.Arity := Delta * Gamma
```

All carrier product helpers (`inl`, `inr`, `copair`, `cover`, relation lemmas,
associativity coherences, unit coherences) get an extra implicit result type
parameter.

## Expression Layer

Change expressions from context-indexed to context-and-type-indexed:

```lean
inductive Expr : C.Arity -> C.Ty -> Type where
  | ap : {Gamma alpha : C.Arity} {tau : C.Ty} ->
      (x : Gamma ∋[tau] alpha) ->
      (forall {Delta : C.Arity} {sigma : C.Ty},
        alpha ∋[sigma] Delta -> Expr (Gamma ⋈ Delta) sigma) ->
      Expr Gamma tau
```

The subterm relation must range over triples:

```lean
Sigma (fun Gamma => Sigma (fun tau => Expr Gamma tau))
```

Eta expansion becomes type-preserving:

```lean
Expr.eta : Gamma ∋[tau] alpha -> Expr (Gamma ⋈ alpha) tau
```

The recursive eta call decreases on the argument arity found in a typed slot;
`subWf` supplies this because it forgets the result type existentially.

## Renaming and Substitution

Renamings preserve both argument arity and result type:

```lean
abbrev Renaming (Gamma Delta : C.Arity) :=
  forall {alpha : C.Arity} {tau : C.Ty},
    Gamma ∋[tau] alpha -> Delta ∋[tau] alpha
```

The existing identity, composition, and extension definitions keep the same
shape, with typed slots threaded through all binders.

Substitution becomes:

```lean
abbrev Subst (Delta Gamma : C.Arity) :=
  forall {alpha : C.Arity} {tau : C.Ty},
    Delta ∋[tau] alpha -> Expr (Gamma ⋈ alpha) tau
```

`Subst.act` keeps the current three-way dispatch by origin of the head slot
(`left`, `middle`, `right`), but every branch carries the result type of the
head. Recursive calls on arguments use the type `sigma` supplied by the typed
argument slot.

## Syntax Monad

Change the target family category from arity-indexed families to
arity-and-type-indexed families:

```lean
structure ArityTyFunc (C : Carrier A) where
  toFun : C.Arity -> C.Ty -> Type
```

The relative-monad functors become:

```lean
J.obj Gamma alpha tau = Gamma ∋[tau] alpha
T.obj Gamma alpha tau = Expr (Gamma ⋈ alpha) tau
```

The object category remains arities with renamings as morphisms. The monad
unit is typed eta, and Kleisli maps are typed substitutions.

## Refactor Order

1. Refactor `Carrier.lean` and keep all carrier helper theorem names stable.
2. Refactor `Renaming.lean` to typed slots.
3. Refactor `Expr.lean`, including typed `Args`, `Subterm`, eta, and renaming action.
4. Refactor `Subst.lean` and `Dispatch.lean`.
5. Refactor `Instantiation.lean`, `Interchange.lean`, and `MonadLaws.lean`.
6. Refactor `SyntaxMonad.lean` and the root import file.
7. Add an untyped compatibility instance/pattern with `Ty := Unit` once the typed
   theory builds.

## Validation

After each module-level step, run the narrowest possible Lean check for that
module. After theorem signatures that are imported downstream change, run the
corresponding `lake build` target rather than only `lake env lean`.

Acceptance criteria:

* The typed carrier helpers compile with stable names.
* `Ty := Unit` reproduces the raw intuition: typed slots are equivalent to the
  old untyped slots with a unit result type.
* Renaming action preserves expression result type.
* Substitution action preserves expression result type.
* The relative monad laws are restored for the typed syntax monad.

## Open Design Boundary

Do not try to encode `Ty` into `Arity` unless a concrete typed arity monoid is
provided. The planned carrier intentionally does not require types to act on
contexts.
