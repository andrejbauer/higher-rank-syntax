# Response to the handoff: equations and typed higher-rank syntax

Verdict on the handoff, in one line: **the constraints are right, the diagnosis
is right, the prescription is backwards.** The raw layer is not the obstacle to
the mutual definition; it is the only thing that makes it well founded. Three
concrete defects of `Raw-plus-typing-redesign.md` explain why that document felt
unsatisfactory, and none of them requires a QIIT to repair.

## 1. Which handoff claims survive

**Survives — interleaving is forced.** Checked in §4 below. `beta_snd`'s
boundary is not well formed unless `~` already contains `beta_fst`.

**Survives — equation entries must not be `Expr.ap` heads.** And this
contradicts `Raw-plus-typing-redesign.md` §8.1, which proposes exactly the
rejected thing: a coarse class `eq` whose expressions are derivations. That row
of the catalogue is proof-relevant equality and should be struck.

**Survives — `Kl(SyntaxMonad C)` is too small to be `EqCtx`.** The
`(x, y, q : x = y) → (u, v)` counterexample is correct.

**Survives, and is the sharpest thing in the document — the sort signature.**
`s : [∂s] sort` is Cartmell's sort symbol with its argument telescope. It is not
a speculative candidate for `P`; it is the known right answer, and it is exactly
what the live code is missing (§2).

**Backwards — "construct contexts, expressions, equality, boundaries and
substitutions simultaneously, rather than using the present pipeline".** The
mutuality the handoff identifies is real and is cut by the raw layer:

```
RawExpr Γ  :=  Expr |Γ|              -- plain inductive; mentions no equality
~_Γ        :=  DerivEq E_Γ           -- defined on ALL of RawExpr Γ
WF_Γ       ⊆   RawExpr Γ             -- structural recursion; may consume ~_Γ freely
Q_Γ        :=  image of WF_Γ in RawExpr Γ / ~_Γ
```

Step 3 is where an application `ap x args` demands that `args` respect the
equations of the head's arity `Θ`. That demand is a *side condition* mentioning
`~_Γ`, not a recursive occurrence, so the substituted equation `e[args]` being
larger than `ap x args` costs nothing. Each layer consumes only the one below.
Drop the raw layer and this stratification is destroyed; the QIIT in the
handoff's §"Simplified untyped/equational case" is self-inflicted.

Price of the extrinsic route, stated honestly: `Q_Γ` is a subquotient, so it has
no primitive induction principle — induction runs on `Expr` (given) and on
derivations (given). Congruence and conversion are *not* part of that price;
see §3.

**Backwards — "The old relative monad cannot have `EqCtx` as its Kleisli
category" read as a defect.** It is not a defect, it is a correct type-check.
In the algebraic direction the handoff's own two Hom-formulas are the two
universal properties of a presentation:

| entry | Hom-formula | universal property |
|---|---|---|
| `d : [Θ] box` | `Hom(Γ.d, Δ) ≅ Σ_{σ ∈ Hom(Γ,Δ)} Q_Δ(Θ)` | free extension by a generator |
| `q : [Θ](e=e')` | `Hom(Γ.q, Δ) ≅ {σ ∈ Hom(Γ,Δ) ∣ e[σ] = e'[σ]}` | coequalizer / quotient |

So `EqCtx` is the category of **finitely presented models with chosen
presentation**; `Kl(SyntaxMonad C)` is its subcategory of *free* ones. A context
is a presentation, `Q_Γ` is the model it presents, and the equation-erasing map
`Expr |Γ| ↠ Q_Γ` is the free cover. That answers the handoff's question 3
without new machinery, and it is the reason a *single* global relative monad on
`J` cannot be the whole story: it only ever sees free objects.

The handoff's "context-indexed family of quotient monads" is then the standard
polynomial construction: `Θ ↦ Q_{Γ⋈Θ}` is `Q_Γ`-with-fresh-indeterminates. The
repository already has its raw half — `PrefixedSyntaxMonad C S` at
`HigherRankSyntax/PrefixedSyntaxMonad.lean:34`, object map
`Γ ↦ (α,τ) ↦ Expr (S ⋈ Γ ⋈ α) τ` — and its quotient half,
`Equations.quotientMonad` at `HigherRankSyntax/Equations/QuotientMonad.lean:163`.

## 2. What is actually wrong with `Raw-plus-typing-redesign.md`

Three defects, all local. Note first what is *not* wrong: T1 is finished and
sorry-free — `Decoration`, `DTel` as a module over `SyntaxMonad C`, `DTelMon` as
an internal monoid for the context-extension tensor, and the entire quotient
mirror (`QDecoration`, `QDTel`, `QDTelMon`). That is roughly 2500 proved lines
that a QIIT rewrite discards.

**(D1) `bd : C.Ty → Option C.Ty` is too weak — this is the real one.** A slot
gets at most one classifier of one class. The four MLTT boundaries need
argument *telescopes*:

```
box type        ∂ty   = ()
box : A         ∂tm   = (A : ty)
A = B type      ∂tyEq = (A : ty, B : ty)
u = v : A       ∂tmEq = (A : ty, u : tm A, v : tm A)
```

`bd` can express the second and neither equality form. So under `bd`, equation
entries are *inexpressible as declarations* — which is precisely why §8.1 had to
smuggle them in as a proof-relevant class. Fix: replace `bd` by a sort signature
and `ClassifierAt bd Ω τ` by an instantiation of `∂τ` over `Ω`. This is a
generalization of one definition (`Typing/Decoration.lean:55`) plus its image
through `DecorationModule`; the recursion, the module laws and the monoid laws
are untouched because they never inspect `bd` beyond `Option.rec`.

**(D2) `S` and the equation set are both global.** `EquationPresentation C S`
(`Equations/Presentation.lean:24`) fixes the protected prefix once and for all.
Nothing can be declared *after* an equation. Fix in §3.

**(D3) There is no T2, hence no conversion.** The word does not occur in the
document. `𝒯exp(Γ;Δ,c,A)` carries its classifier only in a parenthesis and
Theorem B drops it. Fix in §3, and it is a one-word fix.

Two further items from the survey worth recording: (L3)/(L4) are *hypotheses* of
Theorem B, so the document proves no metatheorem, only isolates the interface;
and (L1)/(L2) conflate "prefix of `Γ`" with "telescope over `Γ`" and do not
typecheck as written.

## 3. The proposal

### 3.1 One ordered context, with equations erased at the raw level

A **context** is

```
Γ = ( |Γ| : C.Arity                    -- the point entries, erased
    , Precedence on |Γ|                -- the order (already a class in the code)
    , D : Decoration ∂ 1 |Γ|           -- boundaries, now sort-signature valued
    , E : positioned equation entries ) -- each carrying a slot of |Γ| as its position
```

Equation entries never enter `C.Arity`, so they never become `Expr.ap` heads —
the handoff's point-vs-path distinction, obtained by construction rather than by
a new `Expr` restriction. `|Γ|` is the handoff's equation erasure, and
`RawExpr_Γ = Expr |Γ|` on the nose.

`E_{<x}` is well defined for every slot `x`, so **well-formedness is checked in
prefix order** and `~` grows along the order. This is the whole of "interleaving":
the raw data of the theory is order-independent, only its well-formedness
predicate is sequential. No tower of types, no induction-induction — the
existing `Precedence` structure already supplies the order, and
`EquationPresentation` is already prefix-parametric, so a context with equations
is literally *a longer protected prefix plus more axioms*.

Users see one sequential notion of context, as the handoff wants.

### 3.2 Point sorts and derived equality forms

Declare only point sorts, each with a boundary telescope `∂s`. For every point
sort, the equality form `Eq_s` with boundary `∂s ⋈ (u : s, v : s)` is *derived*,
not declared. A context entry whose boundary is an `Eq_s` form contributes to
`~` the raw equation `u ~ v` over `|Γ| ⋈ Θ`, and contributes no head. MLTT is
`ty : [] sort`, `tm : [A : ty] sort` and nothing else.

Observe that the declaration's own arity `Θ` is exactly the metavariable context
`Γ` in `EquationPresentation.axioms : STerm S Γ Φ τ → STerm S Γ Φ τ → Prop`
(`Equations/Presentation.lean:25`). The existing axiom-schema shape is already
the right shape for a declared equation entry.

### 3.3 Conversion is a choice of base, not a rule

**Build T2 over `QDTel`, not `DTel`.**

That is conversion. A judgment indexed by a *quotient* decorated telescope is
by definition insensitive to replacing a classifier by a derivably equal one.
`Equations/DecorationQuotient.lean` and `Equations/QuotientTelescopeMonoid.lean`
already construct that base and prove it is a monoid for the same tensor, so
this costs nothing new. The handoff's "conversion is transport in `Tm(Γ,-)`" and
this are the same statement, one intrinsic, one extrinsic.

### 3.4 Congruence is already proved

`DerivEq.application` (`Equations/Derivation.lean:59`) is congruence for every
head, uniformly, argument-by-argument in the correct binding contexts, over all
of raw `Expr` — and `DerivEq.least` proves it is the least such. A theory author
declares no congruence rule for any symbol, ever. This is the handoff's
requirement 5, and it is discharged by code that exists. It is also the strongest
argument for the raw layer: structural congruence over a free inductive type is
free, whereas in the QIIT it must be threaded through every path constructor.

### 3.5 Hereditary arities with equations

`ap x args` stays unrestricted at the raw level. When the head's arity `Θ`
carries equation entries, the T2 clause for applications requires `args`, read
as an instantiation of `Θ`, to satisfy `E_Θ` up to `~_Γ`. Categorically the
operation's arity is the non-free model `Q_Θ` and the operation is a natural
transformation `Hom(Q_Θ,-) ⇒ U`; the raw `Expr` is the free cover along
`Expr |Θ| ↠ Q_Θ`.

### 3.6 Substitutions

Layer substitutions get one more closure clause: `σ : Γ ⇒ Δ` must send every
equation entry of `Γ` to a derivable equality in `Δ`. `EqCtx` is then the T2
Kleisli category modulo `~`, a non-full subcategory of `Kl(quotientMonad)` — the
handoff's `Sub(Γ,Δ)`, with the missing `σ(q)` component absent for the reason
the handoff gives.

## 4. The Σ test

Sort signature `∂ty = ()`, `∂tm = (A : ty)`; derived `∂Eq_tm = (A : ty, u : tm A, v : tm A)`.

```
Σ        : [ A : ty, B : [x : tm A] ty ]                        ty
pair     : [ A, B, a : tm A, b : tm (B a) ]                     tm (Σ A B)
fst      : [ A, B, p : tm (Σ A B) ]                             tm A
snd      : [ A, B, p : tm (Σ A B) ]                             tm (B (fst A B p))
beta_fst : [ A, B, a : tm A, b : tm (B a) ]  Eq_tm( A,     fst A B (pair A B a b), a )
beta_snd : [ A, B, a : tm A, b : tm (B a) ]  Eq_tm( B a,   snd A B (pair A B a b), b )
```

`B`'s nested decoration assigns `x` the classifier `A`, its earlier sibling —
legal because a decoration of slot `s` lives over `before s`. `b`'s classifier
`B a` and `snd`'s result classifier `B (fst A B p)` are ordinary raw
expressions, so every line above *exists* raw, unconditionally.

`beta_fst` is well formed with `E = ∅`: `fst A B (pair A B a b)` has declared
classifier `A`, and `a : tm A`, so the three components of `∂Eq_tm` match on the
nose.

`beta_snd` at position after `beta_fst`. Instantiating `∂Eq_tm`:

```
A := B a                                   ty-expression                     ✓
v := b                    declared classifier  B a                           ✓
u := snd A B (pair A B a b)
     declared classifier  B (fst A B (pair A B a b))
     required classifier  B a
```

The two differ. In `QDTel` they are the same element:

```
DerivEq.of_axiom  beta_fst        :  fst A B (pair A B a b)  ~  a
DerivEq.application B̂ _ _ (…)     :  B (fst A B (pair A B a b))  ~  B a
```

— `application` instantiated at the head `B̂`, one argument. So the boundary of
`beta_snd` is well formed exactly when `beta_fst` precedes it, and the
conversion step is congruence under a declared symbol, obtained from the generic
`application` constructor with nothing declared by the author. This is the test
the handoff asked for, and it passes with `DerivEq` as it stands.

Reorder `beta_snd` before `beta_fst` and the fourth line above fails: the
ordering is load-bearing, so the handoff's central constraint is respected.

## 5. Answers to the handoff's five questions

1. **Untyped QIIT spec.** Not needed. §1's four-line stratification, with §3.5
   for equation-carrying arities. What is genuinely lost is the induction
   principle of `Q_Γ`, nothing else.
2. **MLTT spec.** §3.1–3.3 plus §4. The four boundaries are `ty`, `tm` and their
   two derived equality forms.
3. **Global substitution structure.** §1: `EqCtx` = finitely presented models
   with presentations; object entry = free extension, equation entry =
   coequalizer; `Kl(SyntaxMonad C)` = the free part; `Expr |Γ| ↠ Q_Γ` = the
   equation-erasing free cover.
4. **Generalizing the two object boundaries.** The dependent classifier
   telescope *is* the right presentation, and it is Cartmell's sort signature.
   Its three open sub-questions: the telescope language inside `∂s` is the same
   decorated-telescope language (no second language); sort dependencies must be
   ranked, and the ranking is the same `Precedence` order; classifier telescopes
   may contain equation constraints, by §3.5.
5. **Congruence structural.** §3.4 — already proved, `Derivation.lean:59`.

## 6. Next steps, smallest first

1. Generalize `bd : C.Ty → Option C.Ty` to a sort signature and
   `ClassifierAt` to an `∂s`-instantiation. Touches `Typing/Decoration.lean`,
   propagates mechanically through `DecorationModule`, `DecoratedTelescopeMonoid`
   and their quotient mirrors. **This is the load-bearing change and should be
   attempted first, because it is the one that could still fail.**
2. Position the equation entries: give `EquationPresentation` a slot-indexed
   position and define `E_{<x}`.
3. Define T2 over `QDTel`, with clauses (L0)–(L5) plus the equation-preservation
   clause of §3.6. Instantiate on §4 and check `beta_snd` in Lean.
4. Only then the categorical repackaging of §1 (algebras, coequalizers, the
   f.p.-model identification).

## 7. Open, and worth deciding before step 1

- Does `∂s` need to be a *decorated* telescope over the empty base, or may it
  mention earlier sorts only through the ranking? The MLTT instance does not
  distinguish these; a universe hierarchy might.
- Whether `Eq_s` should be derived for every point sort or declared per sort.
  Derived is cleaner and suffices for MLTT; a theory wanting equality at only
  some sorts would want declared.
- The subquotient `Q_Γ` has no primitive induction principle. Every metatheorem
  we want should be checked to run on `Expr`-induction plus derivation-induction
  before we commit.
