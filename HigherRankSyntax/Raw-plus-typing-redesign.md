# Raw syntax plus typing layer: a redesign

This note redesigns the dependent generalization around the principle
that **typed syntax is structure over raw syntax**.  The architecture
inverts the one contemplated in MATH.md §6 and in
`J-pseudofunctor-double-category.md` (henceforth *the carrier note*):
instead of generalizing the carrier first and instantiating it with
syntax later, we keep the existing simply-typed development as the
foundation — the *raw layer* — and define a *typing layer* as
structure over its monad.  The generalized carrier and the dependent
relative monad of the carrier note are then **derived** objects, and
the carrier note becomes the specification that the derived objects
provably satisfy.

Throughout, `C₀` is a fixed carrier in the current sense
(`Carrier.lean`): a monoid `M` of raw arities, a set `Ty₀` of raw
classes, slot fibres `Γ₀ ∋[c] α` with the additivity structure
(`unit_empty`, `slotAt_mul`, `cover`, `copair_uniq`) and
well-foundedness `subWf`.  We write `P₀(Γ₀) := Σ_{α,c} Γ₀ ∋[c] α` for
the total raw slot set, `(α_x, c_x)` for the raw boundary of a slot
`x`, `Expr₀` for its expressions, `⟦ρ⟧ʳ` for the renaming action, and
`Subst₀`, `act` for raw substitution as in `Subst.lean`; recall the
signatures

```
Subst₀ Δ (Γ ⋈ Ξ)  =  ∀ α c, Δ ∋[c] α → Expr₀ (Γ ⋈ Ξ ⋈ α) c
σ.act Φ           :  Expr₀ (Γ ⋈ Δ ⋈ Φ) c → Expr₀ (Γ ⋈ Ξ ⋈ Φ) c
```

with a fixed prefix `Γ` and a depth parameter `Φ`.  Both parameters
were introduced for the internal recursion; in this note they acquire
external meaning: **the prefix will carry the signature, the depth
will carry the telescope-prefix under which a classifier lives.**

We fix a *signature* `S ∈ M` (the symbols of the theory, MATH.md §3)
and a partial map `bd : Ty₀ ⇀ Ty₀` assigning to a raw class the class
of its classifiers (for Martin-Löf type theory: `Ty₀ = {ty, tm}`,
`bd(tm) = ty`, `bd(ty)` undefined).

## 1. Overview of the architecture

```
Layer 0 (raw)      the existing formalization, unchanged:
                   C₀, Expr₀, renamings, act, the three monad laws.

Layer 1 (typing)   (T1) decorations: raw data equipped with
                        precedence and raw-expression classifiers;
                   (T2) a typing layer: a class of decorated data
                        closed under the raw structural operations.

Derived            the dependent carrier 𝔻 of the carrier note,
                   J, T, η, the dependent monad, the classifier
                   action σ⋆ — all by restriction of layer 0.
```

The point of the design is the direction of the arrows: nothing in
layer 1 is defined by recursion on layer-1 data.  Every operation of
layer 1 is the corresponding operation of layer 0, restricted; the
only recursions are those already performed (and proved terminating)
in layer 0, plus one harmless one (§2.3) along `C₀.subWf`.  In
particular the *cliff* — the classifier action of substitutions —
is the raw `act` with a well-chosen depth parameter, and the
theorem "every carrier generates its syntax monad" holds by
construction.

## 2. (T1) Decorations

Decorations are the data sub-layer: raw objects equipped with the
two structures that MATH.md §6.2 and §6.5(1) identified as genuinely
new — a *global precedence* on slots, and *classifiers over
prefixes* — both valued in raw syntax.

### 2.1 Decorated telescopes

**Definition 2.1 (decorations).**  Let `Ξ₀ ∈ M` (a *base*; in use it
will always contain the signature: `Ξ₀ = S ⋈ B₀ ⋈ …`).  For `Δ₀ ∈ M`
we define the set `Dec(Ξ₀; Δ₀)` of **decorations of `Δ₀` over `Ξ₀`**
by well-founded recursion on `Δ₀` along `C₀.subWf`.  A decoration `D`
assigns to every raw slot `x ∈ P₀(Δ₀)`, with raw boundary
`(α_x, c_x)`:

- **(d1) precedence**: raw arities `pre₀(x), rest₀(x) ∈ M` with

  ```
  pre₀(x) * rest₀(x) = Δ₀
  ```

  and the *localization law*: under the additivity structure at this
  decomposition, `x` lies in the right summand — there is
  `x̄ ∈ rest₀(x) ∋[c_x] α_x` with `x = C₀.inr x̄` (via
  `slotAt_mul pre₀(x) rest₀(x)`).  Informally: `pre₀(x)` is the part
  of `Δ₀` *before* `x`.

- **(d2) arity decoration**: a decoration of the slot's own arity
  over the extended base,

  ```
  D_x ∈ Dec(Ξ₀ * pre₀(x); α_x).
  ```

  The recursive call is legitimate: `α_x ≺ Δ₀` in `C₀.Sub`, witnessed
  by `x` itself — the same relation that grounds `Expr.η`.

- **(d3) classifier**: if `bd(c_x)` is defined, a raw expression

  ```
  cl(x) ∈ Expr₀ (Ξ₀ * pre₀(x) * α_x) (bd c_x),
  ```

  the *type of the slot*, living over the base, extended by the
  slot's own prefix and its own arity.  (If `bd(c_x)` is undefined,
  no datum: e.g. `ty`-slots of MLTT carry no classifier.)

**Definition 2.2 (decorated telescopes, contexts, erasure).**  A
*decorated telescope over a base `Ξ₀`* is a pair `Δ = (Δ₀, D)` with
`D ∈ Dec(Ξ₀; Δ₀)`; its *erasure* is `|Δ| := Δ₀`.  A *decorated
context* is a decorated telescope over the signature base:
`Γ = (B₀, D)` with `D ∈ Dec(S; B₀)`, written `|Γ| := B₀`.  (This is
the *rooted* convention: contexts are telescopes over the empty
context, decorated relative to `S`.)

**Remark 2.3 (what a decoration adds to a raw arity).**  Nothing but
the two §6 items.  If `bd` is nowhere defined, `Dec(Ξ₀; Δ₀)` is the
set of precedence structures on `Δ₀`, and the carrier note's exactness
statement "one-object generalized carriers = `Carrier` × precedence"
reappears: decorations over a trivial `bd` are inert.  All genuinely
new information is (d3), and it is *raw syntax* — this is the design
decision.

**Definition 2.4 (structure of decorations).**  The following
operations are defined directly (no recursion beyond Definition 2.1):

1. *Empty telescope* `∅`: the unique decoration of `1 ∈ M`
   (no slots, by `unit_empty`).
2. *Concatenation*: for `Δ = (Δ₀, D)` over `Ξ₀` and `Δ' = (Δ₀', D')`
   over `Ξ₀ * Δ₀`, the decoration `Δ·Δ'` of `Δ₀ * Δ₀'` over `Ξ₀`:
   slots are classified by `cover`/`slotAt_mul`; on the left summand
   the decoration is unchanged except `rest₀(x) := rest₀(x) * Δ₀'`;
   on the right summand `pre₀(y) := Δ₀ * pre₀(y)`, all else
   unchanged (well-typed strictly, since the bases agree:
   `Ξ₀ * (Δ₀ * pre₀ y) = (Ξ₀ * Δ₀) * pre₀ y`).
3. *Extension*: for a decorated context `Γ` and a decorated
   telescope `Δ` over `S * |Γ|`, the decorated context
   `Γ ⋈ Δ := (|Γ| * |Δ|, Γ·Δ)`.

The directed-container laws — `Γ⋈∅ = Γ`, `Γ⋈(Δ·Δ') = (Γ⋈Δ)⋈Δ'`,
unit and associativity of `·` — hold **on the nose**, inherited from
the strict monoid `M` and the coherence lemmas of `Carrier.lean`
(`inl_inl`, `inr_inl`, `inr_inr`, `unit_right`, `unit_left`).  The
carrier note's laws (B1) hold *by definition of concatenation*; its
(B0) is the localization law (d1).

### 2.2 The renaming action on decorations

**Construction 2.5.**  Let `ρ : Ξ₀ →ʳ Ξ₀'` be a raw renaming of
bases.  Define `ρ⋆ : Dec(Ξ₀; Δ₀) → Dec(Ξ₀'; Δ₀)` — note: **the raw
arity `Δ₀` does not move** — by the same recursion as Definition 2.1:

```
pre₀, rest₀   unchanged
(ρ⋆D)_x    := (ρ ⇑ʳ pre₀(x))⋆ D_x                        (recursion)
ρ⋆(cl x)   := ⟦ (ρ ⇑ʳ pre₀(x)) ⇑ʳ α_x ⟧ʳ (cl x)          (raw action)
```

**Lemma 2.6 (functoriality).**  `id⋆ = id` and `(ρ;ρ')⋆ = ρ'⋆ ∘ ρ⋆`.
*Proof source*: `Renaming.act_id`, `Renaming.act_comp`,
`Renaming.extend_id`, `Renaming.extend_comp`, by the recursion of
2.5.  ∎

This is axiom (b) of the carrier note — pushforward and its
splitness — no longer postulated but computed; the invariance of the
erasure (`|ρ⋆Δ| = |Δ|`) is the rank axiom (r3), definitional here.

### 2.3 The substitution action on decorations

This is the construction that dissolves the cliff.  Let
`σ ∈ Subst₀ B₀ (S ⋈ B₀')` be a raw substitution between context
underliers, over the fixed signature prefix `S` (so `σ` replaces the
`B₀`-slots and leaves `S` alone — the `T'_S` discipline of MATH.md
§3).

**Construction 2.7.**  Define, for every *depth* `Θ₀ ∈ M`,

```
σ⋆_{Θ₀} : Dec(S * B₀ * Θ₀; Δ₀) → Dec(S * B₀' * Θ₀; Δ₀)
```

by the recursion of Definition 2.1:

```
pre₀, rest₀     unchanged
(σ⋆_{Θ₀} D)_x := σ⋆_{Θ₀ * pre₀(x)} D_x                    (recursion)
σ⋆_{Θ₀}(cl x) := σ.act (Θ₀ * pre₀(x) * α_x) (cl x)        (raw act, depth = Θ₀ * pre₀(x) * α_x)
```

The classifier clause typechecks *exactly* against the signature of
`Subst.act` quoted in the preamble: `cl(x)` lives over
`S ⋈ B₀ ⋈ (Θ₀ * pre₀(x) * α_x)`, i.e. prefix `S`, domain `B₀`, depth
`Θ₀ * pre₀(x) * α_x`; the result lives over the same depth with `B₀`
replaced by `B₀'`.  **The depth parameter of the existing `act` is
precisely the classifier-transport mechanism.**  No new recursion, no
new termination argument: Construction 2.7 recurses only along
`C₀.subWf` (through `D_x`), and each clause invokes the
already-terminating raw `act`.

**Lemma 2.8 (module laws).**  Writing `σ;θ` for raw Kleisli
composition (`Subst.comp`):

```
(η)⋆ = id            (σ;θ)⋆ = θ⋆ ∘ σ⋆            ρ-naturality
```

*Proof source*: `act_inst_id` (`Instantiation.lean:94`, the
prefix-general unit), `act_comp` (`MonadLaws.lean:40`, proved at
general prefix), and the renaming lemmas; all applied under the
recursion of 2.7.  The only currently missing raw ingredient in the
repository is the prefix-general `act_η`, needed for the unit law in
the form `(η∘ρ)⋆ = ρ⋆`.  ∎

**Remark 2.9.**  Lemma 2.8 says: *decorations form a module over the
raw relative monad* (in the sense of Hirschowitz–Maggesi, transposed
to the relative setting as in Ahrens).  This module was the "D7
postulate" of the abstract approach; here it is a construction, and
its laws are corollaries of the raw monad laws.  This is the precise
sense in which the raw-first architecture removes the circularity:
the classifier action is founded on a monad that exists *before* any
typed object is defined.

## 3. (T2) Typing layers

Decorations are raw data; a *typing layer* selects the well-formed
part.  The selection is not arbitrary: it must be **closed under the
raw structural operations** — and the list of closure conditions is
exactly the list of admissible structural rules of a type theory.

Throughout, fix `C₀`, `S`, `bd` as above.  Write:

- `DCxt` for the set of decorated contexts (Def. 2.2);
- `DTel(Γ)` for decorated telescopes over `S * |Γ|`;
- for `Γ, Γ' ∈ DCxt`, a **decoration-compatible renaming**
  `ρ : Γ →ʳ Γ'` is a raw renaming `|Γ| →ʳ |Γ'|` such that transport
  matches the target's decoration:
  `(id_S ⋈ ρ)⋆ (dec Γ) = restriction of dec Γ'` slotwise, i.e.
  `pre/ar/cl` of `ρx` are the transports of those of `x`;
- for `Γ, Γ' ∈ DCxt`, a **decoration-compatible substitution**
  `σ : Γ ⇒ Γ'` is a raw `σ ∈ Subst₀ |Γ| (S ⋈ |Γ'|)`; its
  *compatibility data* is the statement that each filler sits at the
  transported boundary (this is a condition on where fillers land,
  made precise in (L4) below — note that the transported boundary
  `σ⋆(D_x)`, `σ⋆(cl x)` is *already defined* by Construction 2.7, so
  the condition is not circular).

**Definition 3.1 (typing layer).**  A *typing layer* `𝒯` over
`(C₀, S, bd)` consists of predicates

```
𝒯cxt ⊆ DCxt
𝒯tel(Γ) ⊆ DTel(Γ)                                  (Γ ∈ 𝒯cxt)
𝒯exp(Γ; Δ, c) ⊆ Expr₀ (S ⋈ |Γ| ⋈ |Δ|) c           (Γ ∈ 𝒯cxt, Δ ∈ 𝒯tel(Γ), c ∈ Ty₀)
```

("well-formed contexts", "well-formed telescopes", "well-formed
expressions at interface `Δ` and class `c`"), subject to the closure
laws (L0)–(L5):

- **(L0) root and extension.**  The empty context is in `𝒯cxt`;
  `∅ ∈ 𝒯tel(Γ)`; if `Δ ∈ 𝒯tel(Γ)` then `Γ⋈Δ ∈ 𝒯cxt`, and
  concatenation preserves `𝒯tel` (for `Δ ∈ 𝒯tel(Γ)`,
  `Δ' ∈ 𝒯tel(Γ⋈Δ)`: `Δ·Δ' ∈ 𝒯tel(Γ)`); conversely prefixes: if
  `Δ·Δ' ∈ 𝒯tel(Γ)` then `Δ ∈ 𝒯tel(Γ)` and `Δ' ∈ 𝒯tel(Γ⋈Δ)`.
- **(L1) boundaries are well-formed.**  If `Δ ∈ 𝒯tel(Γ)` and
  `x ∈ P₀(|Δ|)`, then the slot's decorated prefix and arity are
  well-formed telescopes (`pre(x) ∈ 𝒯tel(Γ)` as the decorated prefix
  of `Δ`, `ar(x) := (α_x, D_x) ∈ 𝒯tel(Γ ⋈ pre x)`), and its
  classifier is a well-formed expression:
  `cl(x) ∈ 𝒯exp(Γ ⋈ pre x; ar x, bd c_x)`.
- **(L2) variables.**  η-expansion of a well-formed slot is
  well-formed: for `Γ ∈ 𝒯cxt` and a context slot `x` (a slot of the
  telescope `r_Γ`), `Expr.η x ∈ 𝒯exp(Γ_x; ar x, c_x)`-weakened —
  concretely, the η-expansions used by the identity substitution lie
  in `𝒯exp`.
- **(L3) renaming stability.**  If `ρ : Γ →ʳ Γ'` is
  decoration-compatible with `Γ, Γ' ∈ 𝒯cxt`, then `ρ⋆` maps
  `𝒯tel(Γ)` into `𝒯tel(Γ')` and `⟦(id_S ⋈ ρ) ⇑ʳ |Δ|⟧ʳ` maps
  `𝒯exp(Γ; Δ, c)` into `𝒯exp(Γ'; ρ⋆Δ, c)`.  Weakenings
  `C.inl`-style are decoration-compatible (so weakening is
  admissible).
- **(L4) substitution stability** (the load-bearing law).  Call
  `σ : Γ ⇒ Γ'` a *layer substitution* if for every context slot `x`
  of `Γ`,

  ```
  σ(x) ∈ 𝒯exp(Γ'; σ⋆(ar x), c_x)      at the transported classifier σ⋆(cl x).
  ```

  Then: layer substitutions are closed under raw composition and
  contain the identity substitution (`Subst.id`, via (L2)); and for
  every layer substitution `σ` and every depth `Δ ∈ 𝒯tel(Γ)`, the
  raw action preserves the layer:

  ```
  σ⋆ : 𝒯tel(Γ) → 𝒯tel(Γ')          σ.act |Δ| : 𝒯exp(Γ; Δ, c) → 𝒯exp(Γ'; σ⋆Δ, c).
  ```

- **(L5) heads** *(optional strengthening, for adequacy of
  instances)*: an expression `ap x args ∈ 𝒯exp(…)` iff its head is a
  well-formed slot of the signature-or-context and its arguments are
  well-formed at the head's (instantiated) boundaries.  (L5) is what
  a *particular* theory's inference rules provide; the abstract
  format needs only (L0)–(L4).

**Remark 3.2 (the closure laws are the admissible rules).**  The
dictionary:

| closure law | classical counterpart |
|---|---|
| (L0) | context formation, telescope formation |
| (L1) | "contexts are built from well-formed types" |
| (L2) | the variable rule |
| (L3) | weakening/renaming admissibility |
| (L4) | the substitution lemma |
| (L5) | the congruence/formation rules of the theory |

For a layer *generated by inference rules* (the FTT situation),
(L0)–(L2), (L5) hold by construction and (L3), (L4) are the
classical admissibility *theorems* of that theory.  The format turns
them into the interface: a rule system qualifies as a typing layer
exactly when its substitution lemma holds.

**Remark 3.3 (proof irrelevance).**  Definition 3.1 takes judgements
as predicates.  A proof-relevant variant (judgements as sets of
derivations, the layer as data over raw syntax rather than a
subobject of it) is the same design with "subset" replaced by "map
into"; everything in §4–§5 goes through with fibres in place of
subsets.  We work with predicates for the first iteration.

## 4. The derived dependent structure

Fix a typing layer `𝒯`.  Everything the carrier note axiomatized is
now constructed by restriction, and its axioms become theorems.

**Theorem A (the derived carrier).**  The data

```
objects   𝒯cxt
tight     decoration-compatible renamings between layer contexts
loose     Δ ∈ 𝒯tel(Γ), as Γ ⇸ Γ⋈Δ
squares   decoration-compatible raw squares preserving the layer
P(Γ,Δ)    := P₀(|Δ|)        (the raw slots — no new slot sets)
bnd       := (pre, ar, cl)  (the decoration)
```

satisfies every axiom of the carrier note §3: the concreteness of
`W : 𝔻 → Sq(ℛ)` (cells are raw commuting frames, hence determined by
them), the split opfibration (Construction 2.5 + Lemma 2.6), the
root (Def. 2.2), pseudo-ness/additivity of `P` (the raw
`slotAt_mul`, restricted — invertibility is inherited), inversion of
opcartesian squares (raw arities do not move under `ρ⋆`), the
boundary laws (B0) = (d1) and (B1) = Definition 2.4, transport (B2)
= Construction 2.5, and well-foundedness = `C₀.subWf`.  *Status*:
each item is a finite check against layer-0 lemmas; no new
termination arguments.

**Theorem B (the derived monad).**  Define, for `Γ ∈ 𝒯cxt`:

```
𝒦_Γ      := Σ_{Δ ∈ 𝒯tel(Γ)} classifier data of Δ           (boundaries at Γ)
J Γ      := context slots of Γ, fibred over 𝒦_Γ by bnd
T Γ      := (Δ, c) ↦ 𝒯exp(Γ; Δ, c)
η        := Expr.η, restricted                                (by (L2))
lift σ   := σ.act, restricted                                 (by (L4))
```

Then `(J, T, η, lift)` is a relative monad in the fibred sense of
the carrier discussion: `J, T` are functors `ℛ₁ → Fam` over the
classifier functor `𝒦`, `η` is vertical, Kleisli maps are the layer
substitutions (each carrying its transport `σ⋆` from Construction
2.7), and the three laws hold — **by restriction of `act_id`
(`act_inst_id`), `act_η`, `act_comp`**: the restriction of equal raw
maps to a preserved subset are equal.  *Status*: modulo the one
missing raw lemma (prefix-general `act_η`), the only genuinely new
obligations are the preservation statements themselves, which are
(L3)–(L4), i.e. *hypotheses* of the theorem; instances discharge
them once, as their substitution lemma.

**Theorem C (degeneration).**  If `bd` is nowhere defined and the
predicates are everywhere true, the typing layer is the *trivial*
one; `𝒯cxt` = raw arities with inert precedence, `σ⋆ = id` on the
(empty) classifier data, and Theorem B's monad is `SyntaxMonad C₀`
up to the inert precedence component.  Every raw carrier is thus a
carrier of the new architecture, and "the class of carriers that
generate" is all of them — by construction.

**Target D (representation).**  Conversely, every abstract
generalized carrier in the sense of the carrier note, enhanced with
skeleton-and-module data, should arise as the derived structure of
an essentially unique typing layer.  This replaces the carrier
note's §5 conjecture and is the precise statement that the carrier
note is the *specification* of typing layers.

## 5. The categorical description of a typing layer

The typing layer admits a compact categorical identity, built in
three steps.  All double categories below are strict and thin.

### 5.1 The raw Kleisli double category

**Definition 5.1.**  `𝕂l₀ = 𝕂l₀(C₀, S)` is the double category:
objects raw arities `B₀ ∈ M`; tight arrows raw renamings
`B₀ →ʳ B₀'`; loose arrows `B₀ ⇸ B₀'` the raw substitutions
`Subst₀ B₀ (S ⋈ B₀')`, with loose identity `Subst.id`-over-`S` and
loose composition `Subst.comp`; squares: `(ρ, ρ')` bounds
`σ → σ'` iff the whiskering equation `σ' ∘ ρ = (id_S ⋈ ρ')⋆ ∘ σ`
holds (thin: a square is a property of its frame).  Loose unitality
and associativity are `act_inst_id`/`act_η` and `act_comp`; every
tight `ρ` has the loose companion `η ∘ ρ`.

### 5.2 The decoration expansion

**Definition 5.2.**  `𝔇ec = 𝔇ec(C₀, S, bd)` is the double category:
objects decorated contexts `Γ ∈ DCxt`; tight arrows `Γ → Γ'` the
decoration-compatible renamings (§3); loose arrows `Γ ⇸ Γ'` the
pairs (raw substitution `σ`, the assertion that its fillers sit at
the `σ⋆`-transported boundaries — decoration compatibility); squares
the decoration-compatible raw squares.  There is an evident
forgetful double functor

```
Π : 𝔇ec ⟶ 𝕂l₀,        Γ ↦ |Γ|,   everything else ↦ its underlying raw datum.
```

**Proposition 5.3.**  `Π` is a **discrete double opfibration**: for
every raw arrow (tight or loose) out of `|Γ|` there is exactly one
lift with source `Γ`, given by transporting the decoration
(Constructions 2.5 and 2.7); functoriality of the lifts is Lemmas
2.6 and 2.8.  In particular the entire double structure of `𝔇ec` is
canonically induced from `𝕂l₀` plus the module of decorations —
`𝔇ec` contains no information beyond layer 0 and (T1).

### 5.3 Typing layers as closed sub-double categories

**Definition 5.4 (categorical form of Definition 3.1).**  A typing
layer is a sub-double category `𝕋 ⊆ 𝔇ec` such that:

1. `𝕋` contains the root object and is closed under extension: with
   `Γ` and a `𝕋`-telescope `Δ` it contains `Γ⋈Δ` and the weakening
   tight arrow (this is (L0), (L3)-weakening);
2. `𝕋` is closed under loose identities and loose composition
   ((L2), (L4)-composition);
3. `𝕋` is closed under the companions of its tight arrows: if
   `ρ ∈ 𝕋` tight then `η∘ρ ∈ 𝕋` loose, with its binding squares
   ((L2)+(L3));
4. `𝕋` has **Kleisli comprehension**: for a `𝕋`-telescope `Δ` over
   `Γ`, the loose homs out of `Γ⋈Δ` decompose,

   ```
   𝕋(Γ⋈Δ ⇸ Ξ) ≅ Σ_{σ ∈ 𝕋(Γ ⇸ Ξ)} { well-formed fillers for Δ over σ },
   ```

   naturally — the pairing direction is (L4) (a substitution and
   well-formed fillers combine), the projection direction is the raw
   `threeway` dispatch restricted ((L0)-prefixes).

Here "well-formed telescope/filler" means: belonging to `𝕋` /
having its expression in the `𝒯exp`-fibre of `T` — the two
presentations (predicates, Definition 3.1; sub-double category,
Definition 5.4) determine each other, with `𝒯exp` recovered from
loose homs out of one-slot extensions.

**Remark 5.5 (three readings).**

1. *Refinement system.*  The composite `𝕋 ↪ 𝔇ec → 𝕂l₀` is faithful
   on tights, looses and squares: a typing layer is a
   **proof-irrelevant refinement system over the raw Kleisli double
   category** in the sense of Melliès–Zeilberger ("functors are type
   refinement systems"), in double-categorical form: judgements are
   the objects/arrows lying over their raw underliers, and the
   closure axioms say the refinement is stable under the structural
   geometry.  The proof-relevant variant of Remark 3.3 replaces
   "sub-double category" by "double functor into `𝔇ec`, faithful on
   nothing" — Melliès–Zeilberger's general case.
2. *FTT.*  Bauer–Haselwarter–Lumsdaine's finitary type theories are
   the layers *generated by rules*: `𝕋` = the least sub-double
   category of `𝔇ec` containing the rule-heads (an (L5)-style
   generation) and closed under 1–4.  Their metatheorems (renaming,
   substitution admissibility) are exactly the closure of the
   generated `𝕋` — the format isolates what those proofs establish.
3. *Voevodsky.*  The passage `𝕋 ↦` (Theorem B) `↦` contextual
   structure is the relative-monad-plus-module route to C-systems
   (Voevodsky, *C-system of a module over a `Jf`-relative monad*):
   our Construction 2.7/Lemma 2.8 is the module, our Theorem B its
   syntax.

**Remark 5.6 (where the carrier note's `𝔻` sits).**  Theorem A's
`𝔻` is the *static shadow* of `𝕋`: keep the objects and tights,
take as loose arrows only the `𝕋`-telescopes (as extensions
`Γ ⇸ Γ⋈Δ`, i.e. the companions-of-weakenings side), with the slot
functor `P` given by the raw slots.  The carrier note's concrete
`W : 𝔻 → Sq(ℛ)` is the restriction of `Π`; its "`P` measures the
failure of telescopes to be companions" is, in the present
architecture, the statement that `𝔻` embeds in `𝕂l`-land only after
η-expansion — the monad is the companion-completion, as observed
there.

## 6. Instances

**6.1 Trivial layer.**  Theorem C: the raw development itself.

**6.2 Rank 0: Martin-Löf type theory.**  `Ty₀ = {ty, tm}`,
`bd(tm) = ty`; all context slots of raw arity `1` (rank 0), so (d2)
is trivial and a decorated context is a list of `ty`-expressions
over increasing prefixes — a context in the ordinary sense.  `S` =
the signature of the theory (`Π, λ, app, El, …` as higher-rank
slots, e.g. `Π : (⟨(1,ty), (⟨(1,tm)⟩,ty)⟩, ty)`).  The predicates
are generated by the usual rules; (L3), (L4) are the classical
admissibility lemmas.  Theorem B then yields the dependent monad of
well-formed MLTT syntax; its `J`, restricted to rank 0, has the
signature of a natural model whose terms are variables
(comprehension = Definition 5.4.4 at a one-entry telescope).

**6.3 Rank 1: generalized algebraic theories.**  Operations
`f : (x₁:A₁,…,xₙ:Aₙ) → B` are rank-1 slots of `S` whose decorated
arities are the argument telescopes; child classifiers instantiate
along earlier children via (L4).  The derived monad at a
rule-generated layer is the raw GAT term monad; Cartmell's stratified
signatures are the generation order of `𝕋`.

**6.4 Rank 2: binders.**  We decorate the `Π`-symbol in full.

*The signature is itself decorated.*  `S` is a decorated telescope
over the empty base, built in dependency order (`El` before `Π`
before `λ, app`): the (d2)/(d3) data of a later symbol may mention
the *slots* of earlier symbols, which is legitimate because a
decoration of the slot `s` lives over `pre₀(s)` — the part of `S`
before `s`.  Write `S_{<Π} := pre₀(Π)`, so `El ∈ S_{<Π}`.

*The raw boundary of `Π`* (as in MATH.md §2) is

```
α_Π = ⟨ (1, ty), (⟨(1,tm)⟩, ty) ⟩,      c_Π = ty
```

— two children: a `ty`-child `A` with no bound variables, and a
`ty`-child `B` binding one `tm`-variable.  Since `bd(ty)` is
undefined, the `Π`-slot itself carries no (d3) classifier; all
content sits in the decoration `D_Π ∈ Dec(S_{<Π}; α_Π)`, which per
Definition 2.1 assigns:

```
slot A:  (d1) pre₀(A) = 1, rest₀(A) = α_Π
         (d2) D_A ∈ Dec(S_{<Π}; 1)                trivial (unit_empty)
         (d3) none                                 (a ty-slot)

slot B:  (d1) pre₀(B) = ⟨(1,ty)⟩, rest₀(B) = ⟨(⟨(1,tm)⟩,ty)⟩
         (d2) D_B ∈ Dec(S_{<Π} * ⟨(1,ty)⟩; ⟨(1,tm)⟩):
              the single slot x of ⟨(1,tm)⟩ gets
                pre₀(x) = 1,  D_x trivial,  and
                cl(x) = ap (C.inl El) (_ ↦ Expr.η a)  ∈ Expr₀(S_{<Π} ⋈ ⟨(1,ty)⟩) ty
              where a := the fresh slot of ⟨(1,ty)⟩ — i.e. cl(x) = "El a"
         (d3) none                                 (a ty-slot)
```

The classifier of the bound variable `x` is a raw expression over
`base * prefix`, mentioning the fresh slot `a` contributed by
`pre₀(B)` — the self-reference that the abstract approach struggled
to axiomatize, expressed here with no ceremony.

*Where dependency actually enters.*  At the raw level the children
of a `Π`-headed expression are independent: `Π(A◦, [x]B◦)` has
`A◦ ∈ Expr₀(S ⋈ |Γ|) ty` and `B◦ ∈ Expr₀(S ⋈ |Γ| ⋈ ⟨(1,tm)⟩) ty`,
with the bound `tm`-variable untyped — MATH.md §6.1's observation
that dependency does not live in raw syntax.  The typing layer's
formation rule for `Π` re-introduces it through Constructions
2.5/2.7: transport `D_B` to `Γ` along the *weakening*
`S_{<Π} ↪ S ⋈ |Γ|` (2.5) followed by the one-slot *substitution*
`(a ↦ A◦)` (2.7), obtaining the decorated telescope
`⟨x : El A◦⟩ ∈ DTel(Γ)`; the rule then reads

```
A◦ ∈ 𝒯exp(Γ; ∅, ty)        B◦ ∈ 𝒯exp(Γ; ⟨x : El A◦⟩, ty)
──────────────────────────────────────────────────────────
        Π(A◦, [x]B◦) ∈ 𝒯exp(Γ; ∅, ty)
```

— the instantiation of the bound variable's classifier by the
earlier sibling is precisely `(a ↦ A◦)⋆`, i.e. the raw `act` at the
depth given by (d1).  Dependency between siblings is a *layer*
phenomenon, computed by layer-0 machinery.

*A symbol whose classifier uses the arity part.*  The `Π`/`x`
example exercises only the `prefix` component of (d3)'s context
`base * prefix * arity`; the application symbol exercises the
`arity` component.  Fully annotated,

```
α_app = ⟨ (1,ty), (⟨(1,tm)⟩,ty), (1,tm), (1,tm) ⟩,      c_app = tm
```

with fresh slots `Â, B̂, f̂, û`.  Now `bd(tm) = ty`, so the
`app`-slot of `S` **does** carry a (d3) classifier, and it lives
over `S_{<app} * pre₀(app) * α_app` — a context in which `app`'s own
argument slots are available:

```
cl(app) = ap B̂ (_ ↦ Expr.η û)  =  "B̂(û)"          ∈ Expr₀(… * α_app) ty
```

and, inside `D_app`, the argument slots carry their own classifiers,
`cl(f̂) = El (Π(Â, B̂))` and `cl(û) = El Â`.  This is exactly the
FTT boundary discipline: a symbol's result classifier is a raw
expression over its own argument interface — which is *why* (d3)
places classifiers over `base * prefix * arity` rather than
`base * prefix` alone.

## 7. Consequences for the project

1. **Layer 0 is closed and load-bearing.**  `Carrier.lean` through
   `SyntaxMonad.lean` remain the foundation, unchanged.  The single
   outstanding raw obligation is prefix-general `act_η`.
2. **New development** (`Typing/…`): Definition 2.1 and Constructions
   2.5, 2.7 with Lemmas 2.6, 2.8 (mechanical, recursion along
   `subWf`); Definition 3.1; Theorems A–C by restriction.  No new
   termination proofs anywhere.
3. **MATH.md §6 reorients**: the intrinsic generalized carrier is
   demoted from definition to derived object/specification (Target
   D); §6.5's three open problems become: (1) *solved by (T1)*
   (decorations), (2) *solved by 2.5–2.8* (actions), (3) *identified
   with (T2)* (the judgement layer **is** the typing layer, not a
   further layer above it).
4. **The carrier note** stands as the specification of Theorem A's
   output and as the compressed story of §1–§2 (delooping,
   decompression, concreteness over `Sq`).

## References

- This repository: `Carrier.lean`, `Renaming.lean`, `Expr.lean`,
  `Subst.lean`, `Instantiation.lean` (`act_inst_id`),
  `MonadLaws.lean` (`act_η`, `act_comp`), `SyntaxMonad.lean`;
  MATH.md §§1–6; `J-pseudofunctor-double-category.md`.
- P. Melliès, N. Zeilberger, *Functors are type refinement systems*,
  POPL 2015 — refinement systems as functors; §5.5(1).
- A. Bauer, P. Haselwarter, P. L. Lumsdaine, *Finitary type
  theories* — raw syntax + judgements; the architecture of §3 and
  §5.5(2).
- A. Hirschowitz, M. Maggesi, *Modules over monads and linearity*;
  B. Ahrens, *Modules over relative monads for syntax and
  semantics* — the algebraic form of §2.3.
- V. Voevodsky, *C-system of a module over a `Jf`-relative monad*
  (arXiv:1602.00352) — §5.5(3).
- D. Ahman, T. Uustalu, *Directed containers as categories*
  (arXiv:1604.01187) — the shape layer of Theorem A.
- J. Bourke, R. Garner, *Algebraic weak factorisation systems I*
  (arXiv:1412.6559); B. Clarke, *Lifting twisted coreflections
  against delta lenses* (arXiv:2401.17250) — concrete double
  functors into `Sq`, used in Theorem A via the carrier note.
- G. Cruttwell, M. Shulman, *A unified framework for generalized
  multicategories* (arXiv:0907.2460) — monoids in (virtual) double
  categories; the genre of §5.
