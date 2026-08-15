# Boundaries, equations, and T2

Three answers, in the vocabulary of the live code.

## 1. What a boundary is

### 1.1 Cartmell's principle

In a generalized algebraic theory a signature has three kinds of declaration,
each a symbol together with a *telescope of arguments*:

```
sort symbol       s(x₁ : S₁, …, xₙ : Sₙ) sort
operation symbol  f(x₁ : S₁, …, xₙ : Sₙ) : S
equation          x₁ : S₁, …, xₙ : Sₙ ⊢ e = e' : S
```

The structural point — this is the whole of the principle — is that **the type
of a term is never a bare class; it is always an instance `s(a₁,…,aₙ)` of a
declared sort symbol.** Write `∂s := (x₁ : S₁, …, xₙ : Sₙ)` for the sort
symbol's argument telescope. Then:

> **A boundary at sort `s` is an instantiation of `∂s`.**

Two further Cartmell conditions matter here. The sort symbols are declared in
sequence, so `∂s` mentions only earlier sorts: sorts are **ranked**. And the
argument telescope is a *dependent* telescope — `Sⱼ` may mention `x₁,…,xⱼ₋₁`.

MLTT is two declarations:

```
ty sort                ∂ty = ()
tm(A : ty) sort        ∂tm = (A : ty)
```

and then `Π(A : ty, B : [x : tm A] ty) : ty`, `app(A, B, f : tm (Π A B), a : tm A) : tm (B a)`.
Result sorts are `ty()` and `tm(B a)` — instances, never bare classes.

### 1.2 The sort signature in the live framework

Dictionary against `Typing/Decoration.lean`:

| Cartmell | live code |
|---|---|
| sort symbols | `C.Ty` |
| `∂s` | `bd : C.Ty → Option C.Ty` — degenerate |
| ranking | absent |

`bd` allows a sort at most **one** argument, of one class, non-dependent. So it
can express `∂tm = (A : ty)` and nothing else — in particular no equality
boundary, which needs `(A : ty, u : tm A, v : tm A)`.

The replacement:

```
rank : C.Ty → ℕ
∂    : (s : C.Ty) → DecoratedTelescope ∂ 1        -- all slots of rank < rank s
```

circular as written, well defined by recursion on `rank`. MLTT: `rank ty = 0`,
`rank tm = 1`, `∂ty = 1` (the unit arity), `∂tm = ⟨(1, ty)⟩`.

This answers the handoff's "must sort dependencies be ranked?" — **yes, the
ranking is what makes `∂` exist at all**, and it is nothing but Cartmell's
requirement that a signature be a sequence. It is a *second*, independent
ordering from the precedence order on a context: precedence orders the
*declarations* of a theory, rank orders the *judgment forms*.

### 1.3 Boundaries are Kleisli maps

Write `|∂s| : C.Arity` for the erased argument telescope. Define

```
Boundary ∂ Ω s  :=  Subst |∂s| Ω
                 =  ∀ ⦃α τ⦄, |∂s| ∋[τ] α → Expr (Ω ⋈ α) τ
```

By `syntaxKleisliHomEquiv` (`SyntaxMonad.lean:91`) this is exactly

> **a boundary at sort `s` over `Ω` is a Kleisli map `|∂s| ⟶ Ω` for
> `SyntaxMonad C`** — a generalized element of the sort's argument telescope.

Consequences, all immediate:

- **The boundary former `P` is a coproduct of representables.**
  `P(−) = ∐_{s : C.Ty} Kl(T)(|∂s|, −)`. This is precisely why it is not a black
  box: a familially representable (polynomial) functor has its substitution
  action, binder lifting and positivity determined by the indexing data `|∂s|`,
  and its well-foundedness by `rank`.
- **The substitution action on boundaries is Kleisli composition**, `Subst.comp`.
  `DecorationModule.lean`'s hand-written `ClassifierAt.substituteAt` becomes
  postcomposition.
- **Instantiating a head's boundary by its arguments is one composition.**
  `Raw-plus-typing-redesign.md` did this by hand per symbol (§6.4's `cl(app)`);
  it is `bnd(x) ∘ args`.
- **The equality action is Kleisli composition in `quotientMonad E`.** Same
  formula, different monad. This is §3.
- **It is conservative.** `Subst 1 Ω ≅ PUnit` by `unit_empty`, and
  `Subst ⟨(1,υ)⟩ Ω ≅ Expr Ω υ` by `unit_right`. So on the MLTT sort signature
  `Boundary ∂ Ω s` reproduces `ClassifierAt bd Ω s` on the nose.

### 1.4 Decorations

`Decoration` (`Decoration.lean:114`) is unchanged except in its codomain:

```
Decoration ∂ Ω Δ  :=  ∀ ⦃Φ α τ⦄, DecorationPath Δ Φ α τ → Boundary ∂ (Ω ⋈ Φ ⋈ α) τ
```

`DecorationPath` — `here x` / `nested x p`, indices carrying `P.before x` — is
untouched. So a decoration assigns to every recursively nested slot `x` a
Kleisli map

```
bnd(x) : |∂(c_x)| ⟶ Ω ⋈ before x ⋈ α_x
```

read: *the boundary of `x`, written in the base, the earlier siblings, and `x`'s
own bound variables.* The three-part context is the existing one; only the
codomain generalizes.

`DecorationModule`, `TelescopeTensor`, `DecoratedTelescopeMonoid` and the
quotient mirrors survive, because they use classifiers only through `rename`,
`substitute` and equality of classifiers — all of which `Subst` supports.

**T1 asserts nothing.** A decoration says *which* boundary a slot has, not that
the boundary is well formed or that the slot inhabits it. That discipline is
unchanged.

## 2. How equations live over raw syntax

### 2.1 Equality forms are not sorts

For each sort symbol `s`, define the **equality form** `Eq_s`, with argument
telescope

```
∂(Eq_s)  =  ∂s ⋈ (u : s(x⃗), v : s(x⃗))
```

`Eq_s` is *not* a member of `C.Ty`. It may appear only as the boundary of a
context entry; it never classifies a slot, so it never becomes an `Expr.ap`
head. This is the handoff's point/path distinction, obtained by construction.

(Propositional equality is a different thing and is unaffected: `Id` is an
ordinary declared sort with `∂Id = (A : ty, u : tm A, v : tm A)`, which *does*
get slots and heads. The framework carries both; the distinction is whether the
form is a declared sort symbol or a derived equality form.)

### 2.2 An equation is a parallel pair of Kleisli maps

By §1.3, an `Eq_s`-boundary over `Ω` unpacks as: an instantiation of `∂s`,
together with **two** expressions of sort `s` over `Ω`. Since
`Expr Ω s ≅ Subst ⟨(1,s)⟩ Ω`, an equation at `s` over `Ω` is

> a **parallel pair of Kleisli maps** `⟨(1,s)⟩ ⇉ Ω`, together with their common
> sort instantiation.

Declaring it asks for their **coequalizer**. Object entry = free extension by a
generator, equation entry = coequalizer of a parallel pair. Same two universal
properties as before, now with the parallel pair named.

### 2.3 A context

```
Γ  =  ( |Γ| : C.Arity                       -- point entries; the raw erasure
      , D   : Decoration ∂ 1 |Γ|            -- their boundaries
      , E   : EquationPresentation C |Γ| )  -- the path entries
```

with `E` **positioned**: each axiom carries the slot of `|Γ|` after which it was
declared, so `E_{<x}` is defined for every slot. `Precedence` already supplies
the order.

An equation entry `q : [Θ] Eq_s(β)` contributes to `E` the single pair
`(β(u), β(v)) : Expr (|Γ| ⋈ |Θ|) s`, and contributes **no slot** to `|Γ|`.
Nothing else about it is retained — that is the proof-irrelevance.

Note the shape already matches: `EquationPresentation.axioms` is indexed
`{Γ Φ : C.Arity}` over `Expr (S ⋈ Γ ⋈ Φ) τ` (`Presentation.lean:25`), where `S`
is the protected context, `Γ` the substitutable metavariables and `Φ` the local
bound variables. Take `S := |Γ|` and `Γ := |Θ|`: **an equation entry's own arity
is the axiom schema's metavariable telescope.** No change to the type.

### 2.4 The three levels, all built

| level | object | status |
|---|---|---|
| axiom | a positioned parallel pair | `EquationPresentation C S` |
| congruence | `~` = least equivalence closed under `application` and two-sided `substitute` | `DerivEq`, proved least (`Derivation.lean:90`) |
| quotient | `QExpr`, `quotientMonad E : RelativeMonad (J C)` | `QuotientMonad.lean:163` |

So: **equations live over raw syntax as a congruence on `Expr`, presented by
positioned parallel pairs, and the equational theory is the quotient relative
monad.** `Expr |Γ|` itself is untouched.

`DerivEq.application` is structural congruence at every head, uniformly. A
theory author declares no congruence rule for any symbol.

### 2.5 Why not slots

A slot *adds* an inhabitant; an equation *removes* a distinction. Free extension
and coequalizer are opposite operations, and a single mechanism cannot be both.
Concretely: an equality slot `q : x = y` would give proof-relevant equality
terms and would still leave `x ≠ y`. Also, the erasure `|Γ|` must be a raw arity
for `RawExpr_Γ = Expr |Γ|`; equation slots would pollute it.

## 3. T2

### 3.1 What is and is not deferred to T2

- The **congruence** `~` on raw `Expr` is T1, and built.
- Its action on **decorations** is T1, and built: `QDecoration`, `QDTel`,
  `QDTelMon` — decorated telescopes modulo derivable equality of boundaries.
- **Conversion** is T2, and is not a rule. It is the choice to index T2's
  judgments by *quotient* boundaries.

So the effect of equations is visible before T2; what T2 adds is the assertion
that a well-formed expression's boundary is determined only up to `~`.

### 3.2 The judgments

Fix `C`, `∂`, `Precedence`, and `Γ = (|Γ|, D, E)`. Write

```
QBoundary E Ω s  :=  Hom_{Kl(quotientMonad E)}(|∂s|, Ω)     -- boundaries mod ~
```

T2 is two proof-irrelevant predicates:

```
Γ ⊢ Θ tel                     Θ : QDTel E ∂ |Γ|
Γ ⋈ Θ ⊢ e ⇐ β                 e : Expr (|Γ| ⋈ |Θ|) s,   β : QBoundary E (|Γ| ⋈ |Θ|) s
```

**Conversion is now a triviality:** if `β ~ β'` then `β` and `β'` are the same
element of `QBoundary`, so `⊢ e ⇐ β` and `⊢ e ⇐ β'` are the same proposition.
No rule, no admissibility, no coherence.

### 3.3 The clauses

**(V) Slot.** For a slot `x` with declared boundary `bnd(x)` from the
decoration,

```
Γ ⋈ Θ ⋈ α_x ⊢ Expr.η x ⇐ [bnd(x)]
```

**(A) Application.** For `x : (|Γ| ⋈ |Θ|) ∋[s] α` and `args : Expr.Args (|Γ|⋈|Θ|) α`:

```
args : α ⇒ Γ⋈Θ  a layer substitution        args ⊨ E_α
──────────────────────────────────────────────────────────
Γ ⋈ Θ ⊢ ap x args ⇐ [ bnd(x) ∘ args ]
```

- *layer substitution*: for each slot `i` of `α`, `args i ⇐ [bnd_α(i) ∘ args]`
  — each argument sits at its declared boundary instantiated by the earlier
  siblings. Sibling dependency, as before, is `Decoration.substitute`.
- `args ⊨ E_α`: if the head's arity `α` carries equation entries, `e[args] ~ e'[args]`
  for each. **This is the only place equation-carrying hereditary arities are
  used, and it is a side condition on an already-defined relation, not a
  recursive occurrence — which is why there is no circularity.**
- `bnd(x) ∘ args` is `Subst.comp`.

**(T) Telescope.** `Γ ⊢ Θ tel` iff for each slot `z` of `|Θ|`: `α_z` is a
well-formed telescope over `Γ ⋈ before z`, and `bnd(z)`, as an instantiation of
`∂(c_z)`, sends each slot of `∂(c_z)` to a well-formed expression at the
boundary `∂(c_z)`'s own decoration assigns it, instantiated by the earlier
components. **Recursion on `rank (c_z)`** — this is the second place the ranking
is load-bearing.

**(C) Context, the sequential clause.** `Γ` is well formed iff, walking `|Γ|`
in precedence order:

- point entry `x`: `α_x` is a well-formed telescope over `Γ_{<x}` and `bnd(x)`
  is a well-formed `∂(c_x)`-instantiation over `Γ_{<x} ⋈ α_x` — **using only
  `E_{<x}`**;
- equation entry `q : [Θ] Eq_s(β)` positioned at `x`: `Γ_{<x} ⊢ Θ tel`, the
  `∂s`-part of `β` is well formed, and `β(u), β(v)` are both well formed at that
  `∂s`-part — **using only `E_{<x}`**.

`E_{<x}` is the whole of interleaving. The raw data of a theory is
order-independent; only this predicate is sequential.

**(S) Stability.** Renaming and substitution stability as in
`Raw-plus-typing-redesign.md` (L3),(L4), plus one clause: a layer substitution
`σ : Γ ⇒ Δ` must **satisfy `E_Γ`** — send each axiom of `Γ` to a `~_Δ`-equality.
This is the clause that makes `EqCtx` a non-full subcategory of
`Kl(quotientMonad)` and that makes the handoff's `(x,y,q:x=y) → (u,v)`
counterexample come out right.

### 3.4 Where each piece lands

| piece | role in T2 |
|---|---|
| raw `Expr` | the subject of the judgment; unchanged; still what induction runs on |
| sort signature `∂` | the shape of a boundary, `Boundary ∂ Ω s = Kl(T)(\|∂s\|, Ω)`; `rank` drives (T) |
| `Precedence` | orders declarations; supplies `before x` in (V),(A) and `E_{<x}` in (C) |
| decorations `D` | supply `bnd(x)` in (V),(A),(C) |
| equations `E` | quotient the boundary index → conversion; constrain `args` in (A); filter by position in (C) → interleaving; constrain substitutions in (S) |
| `QDTel` monoid | the base for `Γ ⊢ Θ tel`; makes (T) conversion-stable |
| `Subst.comp` | boundary instantiation in (V),(A) |

### 3.5 `beta_snd` once more, in these clauses

`β(u) = snd A B (pair A B a b)`. By (A) its boundary is
`[bnd(snd) ∘ args] = [B (fst A B (pair A B a b))]`. Clause (C) requires it well
formed at the `∂tm`-part of `beta_snd`'s declared boundary, namely `[B a]`.
These are equal in `QBoundary E_{<beta_snd}` because

```
DerivEq.of_axiom beta_fst      :  fst A B (pair A B a b)  ~  a
DerivEq.application B̂ _ _ (…)  :  B (fst A B (pair A B a b))  ~  B a
```

so the two are literally the same element and nothing further is required.
Position `beta_snd` before `beta_fst` and `E_{<beta_snd}` no longer contains the
axiom, so the check fails. The order is load-bearing, as it must be.

## 4. Consequences for the plan

Step 1 of the previous note sharpens to: **replace the codomain of `Decoration`
by `Subst |∂τ| (—)` and add `rank`.** Everything else in §1–3 is a consequence
or already exists. Two things become simpler rather than harder — boundary
instantiation is `Subst.comp`, and the classifier module action is Kleisli
postcomposition.

Still open before starting:

- whether `∂s` may be a *decorated* telescope over the empty base with genuine
  dependency (needed as soon as a sort has two arguments, e.g. `Eq_tm`), or
  whether the rank ordering alone suffices. `Eq_tm = (A : ty, u : tm A, v : tm A)`
  already needs the dependent version, so: it must be decorated;
- whether `Eq_s` is derived for every sort or declared per sort;
- `Q_Γ` remains a subquotient with no primitive induction principle.
