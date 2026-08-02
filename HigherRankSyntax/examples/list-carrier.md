# Plan: the general list carrier

Target: the motivating carrier of MATH.md §2 in Lean — the free
simply-typed carrier on a set of classes — as
`HigherRankSyntax/Examples/ListCarrier.lean`.  All examples
(groups, λ-calculus, raw MLTT, schemata) are then signatures over
this one instance.

**Remark (what the carrier means).**  Arities/contexts are finite
sequences of declarations, so the monoid is a free monoid `List E`
with concatenation as context extension.  A declaration shape — an
*entry* — is an interface `(arity, class)`, where the arity is again
a sequence of entries: entries of rank 0 are variables (and nullary
symbols), rank 1 are first-order operation shapes, rank 2 binder
shapes, and so on.  A concrete theory touches only the entries
reachable from its signature (for groups: three of them); the
general carrier contains them all.

## 1. Entries

```
inductive Entry (Ty : Type) where
  | mk : List (Entry Ty) → Ty → Entry Ty
```

(nested inductive; an entry is its arity-list and its class).  API:
`Entry.arity`, `Entry.class`; no bespoke recursors — downstream
recursion goes through `SizeOf`, which Lean derives for the nest.
Key size fact, proved once:

```
e ∈ ℓ  →  sizeOf e.arity < sizeOf ℓ        (an entry's arity is smaller than any list containing it)
```

## 2. The Cayley monoid

`A := List (Entry Ty)`; monoid hom `φ : A →* Function.End A`,
`φ ℓ := (ℓ ++ ·)` (direction to be fixed against Mathlib's
`Function.End` conventions, `one = id`, `mul = comp`; the requirement
is `underlyingList (Γ * Δ) = underlyingList Γ ++ underlyingList Δ`).
Injectivity by evaluating at `[]`.

```
Arity := φ.mrange : Submonoid (Function.End A)
underlyingList Γ := Γ.val []
```

This is the strictification device: multiplication in the submonoid
is composition of functions, definitionally associative and unital —
the reason `Carrier` demands this presentation.

## 3. The reusable position lemma

For an arbitrary predicate on entries, positions in a concatenation
decompose lexicographically:

```
positions P (ℓ₁ ++ ℓ₂)  ≃r  Sum.Lex (positions P ℓ₁) (positions P ℓ₂)
```

where `positions P ℓ := {i : Fin ℓ.length // P (ℓ.get i)}`, ordered
via `Fin`.  Build the `Equiv` by index arithmetic
(`Fin.addCases`-style; membership in the left part is decidable by
`i < ℓ₁.length` independently of `P`), then `map_rel_iff'` by the
four `inl/inr` cases.  This is the fiddly proof of the file; it is
stated once, parameterized, so every instance and every later
carrier reuses it.

## 4. The carrier fields

```
slotAt Γ α τ := well-order on positions (fun e => e.arity = underlyingList α ∧ e.class = τ)
                              (underlyingList Γ)
unit_empty   : underlyingList 1 = []                       — immediate
slotAt_mul   : instance of §3 at this predicate
subWf        : InvImage of Nat.lt via sizeOf ∘ underlyingList,
               using the §1 size fact (a slot of Γ with arity Δ
               exhibits Δ as the arity of an entry of Γ)
```

Assembly: `listCarrier (Ty : Type) : Carrier (List (Entry Ty))`.

## 5. Smoke tests

- `Expr` instantiates over `listCarrier Ty` (a `#check`, no proof);
- generic slot computations for later signatures: slots of a
  one-entry list `[e]` at matching interface ≅ `PUnit`; slots of
  `List.replicate n e` ≅ `Fin n` (order-isomorphically).

## Risks

- nested-inductive ergonomics (recursion via `SizeOf`/well-founded,
  not via the auto-generated nested recursor);
- the `RelIso` bookkeeping in §3 (mitigated by proving it once,
  predicate-parameterized);
- definitional-equality expectations downstream: children at
  arity-`1` slots must live in `Γ ⋈ 1 = Γ` on the nose — verify early
  with a `#check`-level test, since the examples' recursions rely on
  it.

## Order of work

§1 (with the size fact) → §2 → §4 `subWf` → §3 stated and `sorry`d →
§4 assembled against the `sorry` → §5 smoke tests → discharge §3.
Breadth-first: the point of `sorry`-staging §3 is to validate the
carrier assembly and the downstream signatures before the index
juggling.
