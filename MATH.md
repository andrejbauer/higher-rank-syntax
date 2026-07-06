# The mathematics of the formalization

This note records the mathematical content of the formalization and the
facts established around it.  Sections 1–3 describe what is formalized;
§4 gives equivalent formulations in the language of containers; §5 records
what is known about the semantics (algebras of the relative monad); §6
records the intended generalization to dependent contexts.  Open problems
appear at the ends of §5 and §6.

## 1. Carriers

This section describes the base structure of the formalization
(`Carrier.lean`).

Contexts and arities are the same sort of thing, drawn from a single
monoid.  A **carrier** consists of:

- a monoid `M`, whose elements serve both as arities and as contexts;
  **context extension** is multiplication, written `Γ ⋈ Δ := Γ * Δ`;
- a set `Ty` of (result) types;
- for all `Γ, α ∈ M` and `τ ∈ Ty`, a set `Γ ∋[τ] α` of **slots** of arity
  `α` and result type `τ` in `Γ`, such that the unit has no slots and the
  slots of a product decompose as a coproduct:

  ```
  (Γ * Δ) ∋[τ] α ≅ (Γ ∋[τ] α) ⊔ (Δ ∋[τ] α)
  ```

- well-foundedness of the relation "`α` has a slot in `Γ` at some type".
  (Substitution recurses into a substituted filler along this relation; it
  is mathematical content, not a formalization device.)

An equivalent packaging, not itself formalized but used in §§4 and 6: for
each `(α, τ)`, the assignment `Γ ↦ Γ ∋[τ] α` is a strong
monoidal functor from the discrete monoidal category on `M` to
`(Set, ⊔, ∅)`.  A carrier is a monoid equipped with an `(α, τ)`-indexed
family of such functors, together with the well-foundedness condition.

**Coherence of coproduct isomorphisms.** There are two ways to witness
`(Γ * Δ * Ξ) ∋[τ] α ≅ (Γ ∋[τ] α) ⊔ (Δ ∋[τ] α) ⊔ (Ξ ∋[τ] α)`, depending
on how we associate `Γ * Δ * Ξ`. The development requires these to agree,
but since `(Set, ⊔)` is monoidal only up to coherence
isomorphism, there is no guarantee that this will be the case.
The formalization ensures the coherence by requiring that the slots be
well-ordered and that the coproducts are lexicographic sums. This way
the isomorphisms are unique.

Mathematically one may instead take values in any class of sets on which
coproducts are strictly associative and unital, and we do so in the exposition below.


## 2. Expressions

This section describes the syntax of the formalization (`Expr.lean`).

`Expr Γ τ` — expressions of arity `Γ` and result type `τ` — is the initial
algebra (a W-type) with one constructor:

```
ap : (x : Γ ∋[τ] α) → (∀ Δ σ, α ∋[σ] Δ → Expr (Γ ⋈ Δ) σ) → Expr Γ τ
```

A head is a slot of the context; the expression's result type is the
head's; children are indexed by the typed slots of the head's arity, each
living in the context extended by that slot's arity and at that slot's
result type.  Since the syntax has no other constructor, everything that
can head an expression — variable, metavariable, symbol, schema — is an
entry of the context, uniformly, in any carrier.

Every slot can be realized as an expression by **η-expansion**: for a slot
`x : Γ ∋[τ] α`, the expression `η x ∈ Expr (Γ ⋈ α) τ` applies `x`,
weakened to `Γ ⋈ α`, to the η-expansions of the slots of `α`, each taken
at its fresh occurrence in `Γ ⋈ α`.  The recursion is legitimate by the
well-foundedness condition of §1.  η-expansion is the unit of the relative
monad of §3.

### Example

The motivating carrier is that of higher-rank syntax.  Fix a set `Ty` and
define **arities** and **entries** by mutual induction: an arity is a
finite list of entries, and an entry is a pair `(α, τ)` of an arity and a
type.  Let `M` be the set of arities, with concatenation as multiplication
and the empty list as unit, and let `Γ ∋[τ] α` be the set of positions of
`Γ` carrying the entry `(α, τ)`.  This is a carrier: the empty list has no
positions; a position of `Γ * Δ` is a position of `Γ` or a position of
`Δ`, which is the coproduct law; and the relation "`α` is the arity of an
entry of `Γ`" is well-founded because arities are inductively generated.

Define the **rank** of an arity by `rank(Γ) = 0` for empty `Γ` and
otherwise `1 + max` of the ranks of the arities of its entries.  The rank
of an entry determines its syntactic role.  In the examples below,
`ι ∈ Ty` is any type, `⟨e₁, …, eₙ⟩` denotes the arity with entries
`e₁, …, eₙ`, and `1` is the empty arity:

- a rank-0 entry `(1, τ)` heads no children — an ordinary variable of
  type `τ`;
- a rank-1 entry such as `(⟨(1, ι), (1, ι)⟩, ι)` heads two children, both
  ordinary terms — a binary symbol, or a metavariable with two term
  arguments;
- a rank-2 entry such as `(⟨(⟨(1, ι)⟩, ι)⟩, ι)` heads one child which
  itself provides one fresh variable — a binder, e.g. λ-abstraction;
- entries of rank 3 and above head children that bind — rules and
  schemata.

All of these are entries of one and the same kind of context; the
framework does not distinguish variables from symbols or metavariables
except by rank.

## 3. The relative monad

This section describes the relative-monad structure of the syntax, proved
in the formalization (`MonadLaws.lean`, `SyntaxMonad.lean`).

Let `Fam(M × Ty)` be the category of `(M × Ty)`-indexed families of sets:
an object `X` assigns a set `X(α, τ)` to each arity `α ∈ M` and type
`τ ∈ Ty`, and a morphism `X → Y` assigns to each `(α, τ)` a function
`X(α, τ) → Y(α, τ)`.  Define two assignments into `Fam(M × Ty)`:

```
J Γ = ((α, τ) ↦ Γ ∋[τ] α)        T Γ = ((α, τ) ↦ Expr (Γ ⋈ α) τ).
```

The **base category** has the elements of `M` as objects, and its
morphisms `Γ → Δ` — the **renamings** — are by definition the family
morphisms `J Γ → J Δ`, i.e. arity- and type-preserving maps of slots.
Thus `J` is a functor into `Fam(M × Ty)` that is bijective on hom-sets,
and `T` is a functor on the same base: a renaming acts on an expression
by acting on all of its heads.  The syntax is a relative monad on `J`:
the unit is η-expansion, the Kleisli extension is simultaneous
(type-preserving) substitution, and a Kleisli map `J Γ ⟶ T Δ` is exactly
a substitution.  The three laws (`unit_right`, `unit_left`,
`comp_lift`) are proved in the formalization; the substitution-composition
law rests on an interchange lemma whose termination measure is an
unordered pair of arities (the symmetry of the two substitution domains).

### Prefix construction

There is a variant of the monad in which every context carries a fixed
prefix.  For a fixed `S ∈ M`, take

```
T'_S Γ = ((α, τ) ↦ Expr (S ⋈ Γ ⋈ α) τ)
```

on the same base, with unit the η-expansion weakened by `S` and with
Kleisli extension the substitution that leaves the `S`-part of the
context fixed.  This is expected to be a relative monad on `J`; at
present, the composition law is formalized in the required generality
(`act_comp` is proved for substitutions over an arbitrary fixed prefix),
while the unit laws are formalized for the empty prefix only.  Since
arities are context-independent, `(S ⋈ Γ) ⋈ Δ = S ⋈ (Γ ⋈ Δ)` holds
strictly, so the prefix does not interfere with context extension.

The purpose of the prefix is to represent algebraic theories.  In
universal algebra, a *signature* is a set of operation symbols, each with
an arity.  The framework has no separate notion of signature; a signature
is represented by a context `S`, with each symbol a slot of `S` and the
symbol's arity the slot's arity.  A term of the theory in variables `Γ`
is then an expression over `S ⋈ Γ`, where the symbols are available in
every context but are not substituted for — which is exactly what the
prefix-fixing monad `T'_S` provides, since its substitutions replace
variables and leave the prefix alone.  For example, for the theory of
groups (one type `ι`; symbols `u`, `m`, `i` with zero, two, and one
`ι`-argument), `S` is the arity with these three slots.  The algebras of
`T'_S` are taken up in §5.

The prefix construction relies on arities being context-independent; in
the dependent setting of §6 this fails, so the construction must be
re-derived there, not transported.

## 4. Container formulations

This section restates the structures of §§1–2 in the language of
containers.  It is not formalized; the purpose is to relate the
definitions to known notions and to prepare the generalization of §6,
which is phrased in the same language.

A **container** (Abbott–Altenkirch–Ghani) `S ◁ P` is a set `S` of shapes
with, for each `s ∈ S`, a set `P s` of positions; it denotes the functor
`X ↦ Σ_{s ∈ S} X^{P s}`.  A container morphism `(S ◁ P) → (T ◁ Q)` is a
map `u : S → T` together with, for each `s`, a map `Q (u s) → P s` —
forward on shapes, backward on positions; it is **cartesian** when each
backward map is a bijection.  The categorical product is

```
(S ◁ P) × (T ◁ Q)  =  (S × T) ◁ ((s, t) ↦ P s ⊔ Q t)
```

— shapes multiply, positions add — with terminal object `1 ◁ ∅`.

Our first observation is that a carrier is essentially a monoid in
`(Cont, ×)`.  Collect the slots of
each `Γ` into a single position set `P Γ = Σ_{α, τ} (Γ ∋[τ] α)`, remembering
the decoration `P Γ → M × Ty`.  Forgetting the decoration, a monoid object
in `(Cont, ×)` on `M ◁ P` is: a monoid structure on `M`; the backward
position map of the unit, `P 1 → ∅`, i.e. the unit has no slots; and the
backward position map of the multiplication, `P (Γ * Δ) → P Γ ⊔ P Δ`,
which is the classification of slots (`cover`).  The monoid laws are the
coherences of classification.  A carrier demands in addition that these
structure morphisms be cartesian — classification is a bijection — and
carries the decoration and well-foundedness on top.  (The composition
tensor on containers plays no role here; it appears at the next level, and
in §6.)

Our second observation is that `Expr` is a polynomial fixed point.  The
decorated position sets make the carrier an indexed container (equivalently a dependent polynomial
functor, Gambino–Hyland / Gambino–Kock) on the index set `M × Ty`: a shape
at index `(Γ, τ)` is a head `x : Γ ∋[τ] α`; its positions are the typed
slots of `α`; the next index of a position `i : α ∋[σ] Δ` is `(Γ ⋈ Δ, σ)`.
`Expr` is its initial algebra, and this is the precise sense in which the
syntax monad is polynomial.

## 5. Algebras of the relative monad

This section concerns the semantics of the syntax: algebras of the
relative monad of §3.  It contains the definition of an algebra unfolded
at this monad, two computations carried out by hand (not formalized), one
general existence fact, and the open problems these point to.

CLAUDE: are you actually going to test it? You said "The notion of algebra is tested against known doctrines"
which means you're claiming this document carries out such a test.

The notion of algebra is tested against known doctrines: at rank 0 (no
binding) it must recover models of Lawvere theories, per Voevodsky's
equivalence between Lawvere theories and relative monads on
`J_f : F → Set` (docs/1601.02158); at rank 1, the Σ-monoids of
Fiore–Plotkin–Turi; at rank 2, models of Fiore–Mahmoud second-order
theories.

**EM-algebras unfolded.**  Instantiating the Altenkirch–Chapman–Uustalu
definition at the `J` of §3, an EM-algebra is:

- a family `X(α, τ)` of sets;
- for every context `Γ` and every **valuation** `v` — an assignment, to
  each slot `x : Γ ∋[τ] α`, of an element `v(x) ∈ X(α, τ)` — an evaluation

  ```
  eval_v : Expr (Γ ⋈ α) τ → X(α, τ)     (for every α, τ)
  ```

subject to two laws:

1. *(unit)* `eval_v (η x) = v(x)`;
2. *(substitution)* `eval_v (σ† e) = eval_w (e)`, where `σ` is a
   substitution, `σ†` its Kleisli extension, and `w = eval_v ∘ σ`.

Note the index `α` in `eval_v`: an expression with a nonempty interface
`α` evaluates to an element of the higher fibre `X(α, τ)`, not to a
function.  The monad never instantiates the interface of the expression
being acted on (only the interfaces of fillers, inside a substitution), so
the higher fibres behave as abstract operation-carriers.

**Rank 0.**  With all context slots of arity `1`, a pure expression is a
single variable, `eval` is forced by the unit law, and EM ≃ `Set^Ty` —
matching the Lawvere fact that models of the initial Lawvere theory are
sets.

CLAUDE: what is the next thing about? A claim? An investigation? A comprehensive study? It's not clear.
Furthermore, you should introduce spines more expicitly, not just as a mid-sentence explanation. NEW TERMS MUST BE PROPERLY INTRODUCED.

**Above rank 0 the higher fibres carry forced structure.**  Computed
example: `Ty = {ι}`; entries `a` (arity `1`, type `ι`) and `p` (arity
`⟨a⟩`, type `ι`, where `⟨a⟩` is the singleton context with entry `a`);
`M` = finite lists of entries, slots = list positions.  An algebra has two
nontrivial carriers `X_a = X(1, ι)` and `X_p = X(⟨a⟩, ι)`.  Expressions
are *spines* — lists of `p`-slots ending in an `a`-slot or, at index `p`,
possibly in the interface slot.  Evaluating one-layer spines defines

- `app : X_p × X_a → X_a` (evaluate `f(x)` under `f ↦ F, x ↦ b`),
- `c ∈ X_p` (evaluate the bare interface slot in the empty context),
- `K : X_a → X_p` (evaluate an `a`-headed expression at index `p`),
- `comp : X_p × X_p → X_p` (evaluate `f(g(y))` with `y` the interface),

and the substitution law forces: `(X_p, comp, c)` is a monoid, `app` is a
monoid action of `X_p` on `X_a`, and `K` gives constants —
`app(K(b), b') = b`, `comp(K(b), G) = K(b)`.  Consequences, all by direct
computation: `app(c, b) = b` and `app(K(b), b') = b` give, when
`|X_a| ≥ 2`, that `c` and the `K(b)` are pairwise distinct, so
`|X_p| ≥ |X_a| + 1`; in particular no algebra has `X_p = 1`, so EM(T) is
not equivalent to `Set^Ty` above rank 0.  The free algebra on a set `S`
(`X_p ≅ 1 + S`) and the full function-space model (`X_p = S^S`) are
non-isomorphic algebras with the same `X_a = S`; the full model satisfies
an extensionality law `comp(F, K(b)) = K(app(F, b))` that is not forced in
general.  The higher fibres are intensional applicative structures — the
map `X_p → X_a^{X_a}` induced by `app` is in general neither injective nor
surjective — as in Kripke λ-models (Mitchell–Moggi).  Since the example
contains no binding (the argument of `p` has arity `1`), it shows that
models of second-order (metavariable) syntax must carry
operation-carriers.  That the forced structure is monoid actions parallels
the classical fact that unary algebraic theories are the same as monoid
actions.

CLAUDE: this should be a section.

**Restrictions.**  Three independent restrictions of the setup are
available, each established:

1. the prefix `S` (§3) — which theory;
2. restriction of the base category of contexts — which variables a
   valuation values (e.g. rank-1, `ι`-typed contexts only);
3. restriction of the codomain family index — at which classifiers
   `(α, τ)` the algebra carries fibres.  The atomic-index restriction is
   self-contained: expressions at atomic interfaces are closed under
   substitution by atomically-indexed fillers, so `J` and `T` restrict to
   a relative monad landing in `Set^Ty`, whose algebras carry only the
   fibres `X(1, τ)`.

Choice 3 separates first-order models (atomic indices: carriers are sets,
symbols become operations) from higher-order models (full family:
metavariable-carriers are semantic data, as in the computed example).

**Left Kan extension.**  The base category is small (its objects are the
elements of `M`) and the codomain `Fam(M × Ty)` is cocomplete, so `Lan_J T`
exists and `T` extends to a monad `T^#` on families, with
`T^# X = ∫^Γ Fam(J Γ, X) · T Γ`: an element is an expression over some `Γ`
with an `X`-valuation of `Γ`, modulo renaming — syntax with parameters
from `X`, the free algebra on generators `X`.

**Open problems.**
CLAUDE: this should be a section, with paragraphs rather than bullet lists.


- Identify EM(T) for the `⟨a, p⟩` carrier; the computation above makes
  "monoid actions with constants `K` satisfying the two laws" the
  candidate answer.
- Show EM(T'_S) ≃ `S`-pointed EM(T)-algebras; over the group signature,
  with restrictions 2 and 3 imposed and the group equations quotiented,
  derive EM ≃ groups.  Every step of this computation is specified; it
  should be the first of these problems to be settled.
- The equations layer: quotients of the monad by substitution-stable
  congruences (in the style of Fiore–Hur), with the monad laws descending.
  Without it only the equation-free half of any theory ↔ monad
  correspondence exists.

## 6. Dependency: from a monoid to a category of shapes

This section concerns a generalization that is not formalized: carriers
in which a telescope extends one specific context rather than every
context, as required for dependent type theories.  Two facts about the
simply-typed framework delimit the problem; the replacement for the
monoid of shapes is then identified as a known structure; what remains
open is listed at the end.

CLAUDE: stop making paragraphs with bold titles and use sections instead, and number them.

**Raw syntax of finitary type theories is already an instance.**  Take
`Ty` = the syntactic classes of FTT (`Ty`, `Tm`, and the equality classes
if desired) and let the carrier's arities be FTT's metavariable and symbol
arities; then raw expressions, raw substitution and instantiation are
exactly `Expr` and its substitution action.  Dependency in FTT does not
live in the raw syntax — it lives in the judgements over it.  So the
dependent generalization splits into two projects: generalize the carrier
so that classifiers are syntax (intrinsic), or keep the carrier simply
typed and build a judgement layer over the monad (extrinsic, FTT's
architecture).  What follows concerns the intrinsic carrier structure;
the judgement layer is untouched work.

**The carrier provides no dependency order.**  In a dependent telescope,
each slot's classifier refers to earlier slots.  The fibre well-orders of
§1 cannot serve as "earlier": they are strictification artifacts, and they
are fibrewise — each `Γ ∋[τ] α` separately, with no relation between slots
in different fibres.  A global precedence on `P Γ = Σ_{α,τ} (Γ ∋[τ] α)` is
genuinely new structure.

**The shape structure.**  In the simply-typed carrier any `Δ` extends any
`Γ`; with dependency, the telescopes that can extend `Γ` form a collection
varying with `Γ`.  The replacement for the monoid is the following data:

- a set `O` of shapes;
- for each `Γ ∈ O`, a set `Tele(Γ)` of telescopes over `Γ`;
- extension: `Γ ⋈ Δ ∈ O` for `Δ ∈ Tele(Γ)`;
- an empty telescope `∅_Γ ∈ Tele(Γ)`, with `Γ ⋈ ∅_Γ = Γ`;
- concatenation: `Δ · Δ' ∈ Tele(Γ)` for `Δ ∈ Tele(Γ)` and
  `Δ' ∈ Tele(Γ ⋈ Δ)`, with `Γ ⋈ (Δ · Δ') = (Γ ⋈ Δ) ⋈ Δ'`;

subject to strict unit and associativity laws (each well-typed by the two
displayed shape equations):

```
∅_Γ · Δ = Δ        Δ · ∅_{Γ ⋈ Δ} = Δ        (Δ · Δ') · Δ'' = Δ · (Δ' · Δ'')
```

This structure is precisely a **directed container** in the
sense of Ahman–Chapman–Uustalu, whose positions are the telescopes.  The
dictionary, against their data `(S, P, ↓, o, ⊕)`:

| directed container | shape structure |
|---|---|
| shape `s ∈ S` | shape `Γ ∈ O` |
| position `p ∈ P s` | telescope `Δ ∈ Tele(Γ)` |
| subshape `s ↓ p` | extension `Γ ⋈ Δ` |
| root `o_s` | empty telescope `∅_Γ` |
| `p ⊕ p'` | concatenation `Δ · Δ'` |

and the five directed-container laws are the laws above.  Directed
containers are the comonoids in containers under the composition tensor
(Ahman–Chapman–Uustalu, *When is a container a comonad?*), and they are
exactly small categories (Ahman–Uustalu, *Directed containers as
categories*, arXiv:1604.01187): objects `O`, morphisms
`Σ_{Γ ∈ O} Tele(Γ)` with `dom(Γ, Δ) = Γ` and `cod(Γ, Δ) = Γ ⋈ Δ`,
identities `(Γ, ∅_Γ)`, composition by `·`.  Summarized: **the monoid of
shapes is replaced by a small category, presented as a directed container
whose positions are the telescopes.**  Two specializations:

- one object (`O = {∗}`): `Tele(∗)` with `·` is a monoid — the
  simply-typed carrier of §1;
- syntactic telescopes over the contexts of a dependent type theory:
  `Γ ⋈ (−)` is injective, so the category is thin — the prefix order on
  contexts.

Neither extreme is part of the definition, just as §1 takes `M` to be an
arbitrary monoid, not a free one.

**Two container layers.**  The carrier thus acquires two layers with
different tensors:

- the *shape layer* `O ◁ Tele` — a comonoid in `(Cont, ∘)`, i.e. the
  category of shapes;
- the *slot layer*: slot sets attach to telescopes, `P(Γ, Δ)` for
  `Δ ∈ Tele(Γ)`, with

  ```
  P(Γ, ∅_Γ) = ∅        P(Γ, Δ · Δ') ≅ P(Γ, Δ) ⊔ P(Γ ⋈ Δ, Δ')
  ```

  — the direct generalization of the product axiom of §1, whose one-object
  case is the classification law of §1 (equivalently, the
  `(Cont, ×)`-monoid structure of §4).  Note the
  second summand is indexed by the base `Γ ⋈ Δ`.

**Status and open problems.**  The shape layer and the slot
layer above are established as definitions with the correct
specializations.  Not yet designed:

- *Decorations.*  A slot's arity must be a telescope over that slot's
  prefix, so the prefix assignment — the global precedence discussed at
  the start of this section — becomes structure the definitions consume,
  in contrast with §1, where the fibre orders serve only coherence.  The
  exact data and its compatibility with the slot-layer decomposition are
  open.
- *Renamings.*  Renamings must act on decorations
  (`arity(ρ x) = ρ⋆(arity x)`), whereas in the carrier of §1 decorations
  are renaming-invariant.  This action, and after it the re-derivation of `J`,
  `T` and the interchange proof over the category of shapes, are open.
- *The judgement layer* (extrinsic route) over the existing monad is
  untouched.

Target specializations that define success: CwFs / natural models at two
judgement forms (`Ty`, `Tm`); Uemura's representable-map framework as the
second-order fragment; Cartmell's GATs as the rank-1 dependent case.

## 7. Reading

- Altenkirch–Chapman–Uustalu, *Monads need not be endofunctors* — relative
  monads, algebras, Kleisli/EM, the Lan-based monoid view.
- Voevodsky, *Lawvere theories and Jf-relative monads* (docs/1601.02158) —
  the rank-0 correspondence and its constructive treatment.
- Arkor–McDermott, *The formal theory of relative monads* — modern
  relative-monad toolkit.
- Fiore–Plotkin–Turi, *Abstract syntax and variable binding*;
  Fiore–Mahmoud, *Second-order algebraic theories*; Fiore–Hur on
  second-order equational logic — the rank-1/rank-2 semantic checks and
  the equations layer.
- Uemura, *A general framework for the semantics of type theory*; also
  Kaposi–Xie on SOGAT signatures — target specializations for §6.
- Cartmell, *Generalised algebraic theories and contextual categories*.
- Bauer–Haselwarter–Lumsdaine, *Finitary type theories* (the
  `finitary-type-theories` repository) — boundaries, judgement forms,
  metavariable contexts; the extrinsic route of §6.
- Hirschowitz–Maggesi, *Modules over monads and linearity* — the expected
  home of a judgement layer over the monad.
- Mitchell–Moggi, *Kripke-style models of the λ-calculus* — intensional
  applicative structures, as arise for the non-standard EM algebras (§5).
- Abbott–Altenkirch–Ghani, *Containers: constructing strictly positive
  types*; Altenkirch–Ghani–Hancock–McBride–Morris, *Indexed containers* —
  containers and their indexed version (§4).
- Gambino–Kock, *Polynomial functors and polynomial monads* (also
  Gambino–Hyland) — the precise sense in which `T` is polynomial (§4).
- Ahman–Chapman–Uustalu, *When is a container a comonad?* — directed
  containers as comonoids in containers under composition;
  Ahman–Uustalu, *Directed containers as categories*
  (arXiv:1604.01187) — directed containers are small categories; the
  shape layer of §6.
