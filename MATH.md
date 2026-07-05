# Mathematical assessment and directions

This note records the mathematical content of the present formalization and
sketches two directions of investigation: (1) semantics — algebras for the
relative monad; (2) generalizing beyond simply-typed syntax to dependency and
arbitrary judgement forms.  Each idea is followed by an **Assessment**
listing known problems, so that no idea stands in this document unvetted.
Refuted ideas are kept only where the refutation blocks a tempting mistake,
and are explicitly marked.

## 1. What is in the repository now

### Carriers

A **carrier** consists of:

- a monoid `M` of arities;
- a set `Ty` of simple (result) types;
- for each `Γ α ∈ M` and `τ ∈ Ty` a set `Γ ∋[τ] α` of **slots** (positions
  of arity `α` and result type `τ` in `Γ`), such that the unit has no slots
  and slots of a product are the coproduct:
  `(Γ * Δ) ∋[τ] α ≅ (Γ ∋[τ] α) ⊔ (Δ ∋[τ] α)`;
- well-foundedness of the relation "α has a slot in Γ (at some type)", which
  makes substitution well-defined (the recursion into a substituted filler
  descends along it — this is mathematical content, not a device).

Equivalently: each `(− ∋[τ] α)` is a monoid morphism from `M` to sets under
coproduct — a monoidal functor from the one-object monoidal category `M` to
`(Set, ⊔, ∅)`.  A carrier is a monoid equipped with an `(α, τ)`-indexed
family of such valuations, i.e. a "content function" assigning to every
arity its multiset of typed sub-arities.

**Strictness devices.**  Since `(Set, ⊔)` is monoidal only up to coherence
isomorphism, a treatment must either carry the canonical isos (and appeal to
Mac Lane coherence) or strictify.  The formalization strictifies twice, and
neither device carries mathematical content:

- `M` is realized as a submonoid of an endomorphism monoid `End(A)`, making
  associativity and unit of arities definitional (Cayley);
- slot sets are realized as **well-orders** with lexicographic sum, so that
  by rigidity (any two order-isomorphisms between well-orders are equal) the
  coherence isomorphisms of the slot decomposition are unique, and all the
  `inl`/`inr` interchange laws become theorems rather than carried
  structure.

Mathematically one may instead take values in any sufficiently restricted
class of sets on which coproducts are strictly associative and unital.
Rigidity is used only for coherence; nothing else consumes the order on the
fibres.

**Equivalently (decorated containers).**  Collecting the fibres into one
structure, the content function assigns to each `Γ` a single set of
positions, each decorated by a classifier `(α, τ)` — a container in the
sense of Abbott–Altenkirch–Ghani, with decorations.  A carrier is then a
monoid homomorphism from `M` into decorated containers under concatenation.
In this reading `Expr` is the initial algebra of the induced *indexed
container* (equivalently, dependent polynomial functor, Gambino–Hyland /
Gambino–Kock): the index set is `M × Ty`; a shape at index `(Γ, τ)` is a
head `x : Γ ∋[τ] α`; its positions are the typed slots of `α`; the next
index of a position `i : α ∋[σ] Δ` is `(Γ ⋈ Δ, σ)`.  This is what "the
monad is polynomial" (§2) means precisely.  Note that the
decorated-container formulation carries slightly more than the fibrewise
axioms: the positions of `Γ` form one set of which the fibres are the
decoration-preimages.  Ordering that set globally is the same strengthening
as repair candidate 2 in §3 (the telescope skeleton) — the dependency
question and the container reading pull in the same direction.

Contexts and arities are the same sort; context extension is reversed
multiplication `Γ ⋈ Δ = Δ * Γ`.

### Syntax

`Expr Γ τ` — expressions of arity `Γ` and result type `τ` — is the initial
algebra (a W-type) with one constructor:

```
ap : (x : Γ ∋[τ] α) → (∀ Δ σ, α ∋[σ] Δ → Expr (Γ ⋈ Δ) σ) → Expr Γ τ
```

A head is a slot of the context; the expression's result type is the head's;
children are indexed by the typed slots of the head's arity, each living in
the context extended by that slot's arity and at that slot's result type.
Since the syntax has no other constructor, everything that can head an
expression — variable, metavariable, symbol, schema — is an entry of the
context, uniformly, in any carrier.  (For example, the carrier with
`Arity = List Arity` and list positions as slots gives higher-rank syntax
proper, where all of these coexist in one context distinguished only by
rank.)  η-expansion realizes a slot as an expression; it is the
generic-variables unit.

### The relative monad

The base category has arities as objects and renamings (slot maps preserving
arity and type) as morphisms.  With `J Γ = ((α, τ) ↦ Γ ∋[τ] α)` and
`T Γ = ((α, τ) ↦ Expr (Γ ⋈ α) τ)`, both landing in arity-and-type-indexed
families, the syntax is a relative monad on `J`: the unit is η-expansion, the
Kleisli extension is simultaneous (type-preserving) substitution, and a
Kleisli map `J Γ ⟶ T Δ` is exactly a substitution.  The three laws
(`unit_right`, `unit_left`, `comp_lift`) are proved; the
substitution-composition law rests on an interchange lemma whose termination
uses an unordered pair of arities (the symmetry of the two substitution
domains).

## 2. Direction 1: semantics as algebras

The guiding special case is Voevodsky's equivalence (docs/1601.02158) between
Lawvere theories and relative monads on `J_f : F → Set`.  There, algebras of
the relative monad are exactly the models of the theory.  The analogous
statements one level up:

- **Rank 0** (no binding): algebras of `SyntaxMonad` should recover models of
  the clone / Lawvere theory generated by the signature.
- **Rank 1** (first-order binding): algebras should recover the Σ-monoids of
  Fiore–Plotkin–Turi (presheaf models with substitution structure).
- **Rank 2**: Fiore–Mahmoud second-order syntax; models of second-order
  equational theories.

These are the sanity checks that pin down the right notion of algebra.

### Idea: unfold EM-algebras at our `J`

Unfolding the Altenkirch–Chapman–Uustalu definition at our `J`, an
**EM-algebra** is:

- a family `X(α, τ)` of sets — think "abstract operations of arity `α` and
  result type `τ`";
- for every context `Γ` and every **valuation** `v` — an assignment, to each
  slot `x : Γ ∋[τ] α`, of an element `v(x) ∈ X(α, τ)` — an **evaluation**

  ```
  eval_v : Expr (Γ ⋈ α) τ → X(α, τ)     (for every α, τ)
  ```

subject to two laws:

1. *(unit)* `eval_v (η x) = v(x)` — evaluating the η-expansion of a slot
   returns its value;
2. *(substitution)* `eval_v (σ† e) = eval_w (e)` where `σ` is a substitution,
   `σ†` its Kleisli extension, and `w = eval_v ∘ σ` — evaluating a
   substituted expression is evaluating under the evaluated valuation.

Note the index `α` in `eval_v`: an expression with a nonempty interface `α`
(free slots beyond `Γ`) evaluates to an element of the higher fibre
`X(α, τ)`, not to a function.  The monad interface never instantiates the
interface of the expression being acted on (only the interfaces of
*fillers*, inside the substitution); this is what makes the higher fibres
behave like abstract, intensional operation-carriers.

**Assessment.**  The algebras will be "big": Voevodsky's algebras live in
`Set`, ours in arity-and-type-indexed families, so an EM-algebra is a whole
family of operation-carriers rather than a set with structure.  Recovering
an ordinary model (a set with group structure, say) requires a
representability or nerve argument identifying the "standard" algebras.
The same gap affects the Fiore–Plotkin–Turi comparison.  Expect
"algebras = models" to hold only up to such an argument, not verbatim.

### Idea: the empty theory as a test case — are its algebras just sets?

Proposed test: over the bare carrier (no signature prefix, no equations),
the EM algebras of the syntax monad should form a category equivalent to
`Set` — everything in a pure expression is a variable, so there should be no
common structure for the algebras to carry.

**Assessment.**  Correct at rank 0; refuted above rank 0 by the worked
example below — but the analysis also corrects an earlier over- and
under-statement of what the laws force, so it is recorded in full.

*Rank 0.*  With all context slots of arity `1`, a pure expression is a
single variable, the monad is the variables monad, `eval` is forced by the
unit law, and EM ≃ `Set^Ty`.  This matches the Lawvere fact: models of the
initial Lawvere theory are sets.

*The worked example (one unary rank: the carrier `{a, p}`).*  Take
`Ty = {ι}`, `M` = finite lists over the two classifiers `a := (1, ι)` (a
term variable) and `p := (⌊a⌋, ι)` (a unary function variable), slots =
list positions of the given classifier; all other fibres empty.  An algebra
has two nontrivial carriers, `X_a` and `X_p`.  Write, for a context with
slots `f : p` and `x : a`:

- `app : X_p × X_a → X_a`, `app(F, b) := eval_{f↦F, x↦b}(f(x))` —
  well defined by the substitution law (independent of ambient context);
- `c := eval(y) ∈ X_p`, where `y` is the interface slot of the index `p`,
  evaluated in the empty context — a constant, by the substitution law;
- `K : X_a → X_p`, `K(b) := eval_{z↦b}(z-as-p-expression)` — the expression
  with head a context slot `z : a` and result read at index `p`, ignoring
  its interface.

Now the substitution law *forces* application behavior on the definable
elements.  Substituting `f' ↦ y-as-filler` into `f'(x)` yields `x`, whence
`app(c, b) = b`; substituting `f' ↦ z-as-filler` yields `z`, whence
`app(K(b), b') = b`.  So `c` behaves as the identity and `K(b)` as the
constant `b`; if `|X_a| ≥ 2` these behaviors are pairwise distinct, hence
`|X_p| ≥ |X_a| + 1`.  In particular `X_p = 1` carries **no** algebra
structure — the fibres above rank 0 cannot be squashed, and EM(T) is not
equivalent to `Set` via the individuals fibre: the free algebra on `S`
(with `X_p ≅ 1 + S`, the pure unary terms with parameters) and the full
model (`X_p = S^S`) are non-isomorphic algebras with the same `X_a = S`.

*What survives of the intuition.*  "The interpretation of `f` is
arbitrary" is correct, and is exactly **freeness**: a valuation may send
`f` to any element `F ∈ X_p`, and no law constrains `app(F, −)` for such
junk elements — no equations are imposed, and elements of `X_p` may even
have undefinable behavior (e.g. adjoin to the free algebra over
`S = {0, 1}` one element acting as the swap).  But "no equations" is not
"no structure": the operation-carriers and their application maps are part
of the object, and morphisms must preserve them.  The higher fibres are
intensional applicative structures (an `ε : X_p → X_a^{X_a}` neither
injective nor surjective in general) — the flavor of Kripke λ-models
(Mitchell–Moggi) and combinatory/applicative structures, not of `Set`.

*Corrected refined statements.*  (i) EM algebras of the pure monad should
be exactly the algebras of the indexed-container endofunctor of §1
**together with** the forced definable-operations structure (`c`, `K`,
composition, and their coherence) — "clones with junk"; a free-monad
argument should make this precise.  (ii) The full function-space models
form a subcategory equivalent to `Set^Ty`; identifying it inside all EM
algebras is the representability/nerve problem in its smallest instance.

Together with the group example this gives two concrete computations, one
with an empty theory and one with a nontrivial one; both should be done —
the `{a, p}` carrier above is small enough to compute EM(T) completely.

### Idea: monoid view via `Lan_J`

ACU show that when `Lan_J` exists, relative monads on `J` are monoids in the
functor category with the (skew) substitution tensor.  Identify the tensor
here; this would place the syntax in the Fiore–Plotkin–Turi tradition
(syntax = free monoid for a substitution tensor).  The Arkor–McDermott work
on relative monads and relative algebraic theories is the modern toolkit.

**Assessment.**  The skewness comes from the behavior of `Lan_J` and the
(non-)density of `J`, not from associativity of the context monoid, so the
strictness supplied by rigidity does not obviously remove it.  Whether the
skew structure is genuinely monoidal here is a question, not an expectation.

### Idea: polynomial structure

`T` is polynomial — the decorated-container reading in §1 exhibits it as the
free monad-like construction on an indexed container.  Its algebras ought to
admit a presentation by operations and equations read off from the carrier —
a "higher-rank algebraic theory".

**Assessment.**  Risk of reinvention: higher-rank clones/theories may
collide with existing notions (abstract clones, cartesian operads,
second-order algebraic theories, familial functors and clubs, opetopes —
higher-rank trees whose arities are themselves trees have an opetopic
flavor).  The examples programme is the mitigation: each worked example
either lands in a known theory (a correctness check) or genuinely does not
(new territory); both outcomes are informative.

### Idea: theory ↔ monad correspondence

Aim, following Voevodsky's paper, for an equivalence between a category of
"higher-rank theories" (presentations) and relative monads of this shape,
with algebras matching models on both sides.

**Assessment.**  This requires an equations layer that does not yet exist:
every concrete theory imposes equations, hence quotients of the monad by
substitution-stable congruences, with the monad laws descending — an
equational-systems layer in the style of Fiore–Hur.  Standard in shape but
genuine work; without it only the raw-syntax (equation-free) half of the
correspondence is available.

### Idea: signatures as context prefixes (the group example)

The framework has no separate notion of signature: a signature is a context.
For the theory of groups (one type `ι`; symbols `u`, `m`, `i` of arities
"no arguments", "two `ι`-arguments", "one `ι`-argument"), let `S` be the
arity containing these three slots.  A term of group theory in variables `Γ`
is then an expression over `S ⋈ Γ` — every context is prefixed by `S`, and
`S` is the new empty context.  Working this example out fully is a test the
setup must pass.

**Refuted first attempt (kept as a warning).**  Let `Shape(S)` be the
subcategory of shapes of the form `S ⋈ Γ` and renamings fixing the `S`-part,
and restrict the monad along the inclusion `Shape(S) → Shape` (restriction
along any functor into the base yields a relative monad).  This **does not
work**: only the renamings were restricted, and Kleisli maps are not
renamings — `J(S ⋈ Γ)` still contains the `S`-slots, so a Kleisli map
assigns fillers to `u`, `m`, `i`, and nothing constrains those fillers.  The
symbols come out substitutable (the Kleisli maps are theory translations),
not constant.  (Beware also: `Shape(S)` is not the image of the functor
`Γ ↦ S ⋈ Γ`, `ρ ↦ 1_S ⇑ ρ` — that functor is not full, since a renaming
fixing the `S`-part may send a `Γ`-slot *into* the `S`-part, e.g. rename a
variable `x : ι` to the symbol `u`, and it need not be injective on objects.
Whether variable-to-symbol renamings belong to the base is a real choice
that the Lawvere comparison will force: there, base maps are
variable-to-variable only.)

**Working construction.**  Keep `J` and change `T`: on the base `Shape`,
with the same `J` (slots), take `T' Γ = Expr (S ⋈ Γ ⋈ −)`, with Kleisli
extension the substitution that fixes the prefix `S`.  This is not a
restriction of the original monad but a different relative monad on the same
`J`, and it costs nothing at the simply-typed level: the monad laws are
already proved with an arbitrary fixed prefix (`SyntaxMonad` merely
instantiates it at `1`), and since arities are context-independent,
extension satisfies `(S ⋈ Γ) ⋈ Δ = S ⋈ (Γ ⋈ Δ)` strictly, so the prefix
never interferes with context extension.

**Assessment.**
- The prefix device is a simply-typed convenience: once classifiers mention
  the context (direction 2), a `Δ` extending `S ⋈ Γ` genuinely refers to
  `S`-slots and the separation "prefix ⋈ variable part" disappears.  The
  device must be re-derived, not transported, in the dependent setting.
- For the Lawvere comparison one more restriction is needed: with the full
  base category the "variables" include higher-rank slots, so the
  construction gives group theory *with metavariables*.  Recovering the
  Lawvere theory requires also restricting the base to rank-1, `ι`-typed
  contexts.  This is a feature — the choice of base subcategory is the
  choice of doctrine — but the example involves two independent
  restrictions: prefixing by `S` and bounding the rank.
- The remaining open question: do the algebras of the prefix-fixing monad,
  after imposing the group equations as a quotient, recover groups — the
  models of the Lawvere theory, matching Voevodsky's rank-0 picture?  This
  one example, fully worked out, would validate both the signature-as-prefix
  idea and the notion of algebra.

## 3. Direction 2: dependency and general judgement forms

The present syntax is simply typed: the classifier of a slot is a pair of an
arity `α ∈ M` and a result type `τ ∈ Ty`, where `Ty` is an unstructured
set — no classifier refers to expressions.  In finitary type theories (the
`finitary-type-theories` development), the classifier of a head is a
**boundary**: a judgement with a hole, e.g. `□ : A` or `A ≡ B by □`, and a
judgement is a boundary filled with a head.  There are several judgement
forms (`is-type`, `is-term`, and their equalities), and the general setup
should not fix them: judgement forms should be data ("is a type", "is a
fibered type", boundaries in general).

### Observation: a hole is a slot

A boundary is an expression with a distinguished position to be filled; the
framework already treats positions as first-class.  Filling a boundary is
substitution at that slot.  Boundaries need not be single-hole: a multi-hole
boundary is an expression over a context extended by several metavariables,
and filling is simultaneous instantiation.  FTT's rule boundaries are
already multi-hole (one metavariable per premise plus the conclusion hole),
judgement classifiers are the one-hole case, equations (filled by the dummy)
the zero-hole case.

**Assessment.**  Sound but nearly contentless at the simply-typed stage,
where a hole's classifier is just a pair `(α, τ)`.  The substance arrives
only when classifiers are themselves syntax — which is the very
generalization being sought.  No obstacle known, but no leverage yet either.

### Observation: a hole is a metavariable

In FTT a judgement lives over `Θ; Γ` where `Θ` is a metavariable context —
and in higher-rank syntax metavariables already live in the context.  A
boundary over `Θ; Γ` is a judgement over `Θ, M:𝔅; Γ`, and filling is
instantiation of the last metavariable.  So boundaries may need no new
machinery: they may be expressions of the same syntax at one higher rank,
with filling a special case of the existing substitution action.

**Assessment.**  Circular as a construction: to form the context entry
`M:𝔅` one needs entries *classified by syntax*, which is precisely the
dependent generalization being sought.  At the present stage entries carry
only `(α, τ)` with `Ty` unstructured.  The observation constrains the design
(filling must come out as substitution); it does not bootstrap it.

### Observation: the well-order carries the dependency

In a dependent telescope each position's classifier refers to earlier
positions; "earlier" should be the order on slots that the carrier already
provides.  If well-foundedness of that order is dropped, one gets
self-referential dependencies (mutually recursive contexts); the framework
has no intrinsic obstacle to that, so well-foundedness should be an optional
axiom, chosen per application.

**Assessment.**  Wrong as stated, and doubly so after demoting the
well-orders to a strictness device (§1): mathematically the carrier provides
*no* order — the fibre orders are strictification artifacts, and in any case
they are **fibrewise** (each `Γ ∋[τ] α` separately, per classifier pair,
with no axiom relating slots in different fibres).  Dependency needs a
**global** precedence on the whole position set `⨆_{α,τ} Γ ∋[τ] α`: a slot
of type `σ` must be able to depend on an earlier slot of type `τ ≠ σ`.
Concrete carriers (lists, telescopes) do carry such an order, but the
abstract structure omits it.  So the dependency order is genuinely *new*
structure to be added, not structure already present.  Candidates for adding
it:

1. Add a global precedence order on the total position set of each `Γ`,
   with the product axiom strengthened to the ordered sum of totals.
2. Change the primitive: assign to each `Γ` a single ordered position set
   `W_Γ` together with a labelling `W_Γ → M × Ty` (a "telescope skeleton");
   fibres are label-preimages, and the product axiom says
   `W_{Γ*Δ} ≅ W_Γ ⊕ W_Δ` over the labellings.  This is arguably the more
   natural primitive — it is exactly the decorated-container formulation of
   §1, with ordered positions — and the content function assigns to each
   arity an ordered typed list of sub-arities.  (In a formalization one
   would again take the orders to be well-orders for the rigidity trick;
   mathematically any precedence relation supporting the intended dependency
   does, and per the observation above it need not even be well-founded if
   self-referential contexts are wanted.)

Either version is a mild strengthening satisfied by the intended instances;
the fibrewise presentation is recovered by taking preimages.  It should be
adopted when dependency actually needs it, not before.

### What must change structurally

With dependency, the extension `Γ ⋈ Δ` no longer makes sense for an
arbitrary pair — `Δ` is an arity *over* `Γ` (mentions `Γ`-slots in its
classifiers).  The monoid must become a structure with dependent
multiplication.  Candidates:

1. **Comprehension-style.**  Contexts form a category with a
   display/comprehension structure (CwF/natural-model flavor); the carrier
   becomes a base for a fibration of classifiers, and the slot structure
   lives over it.

   **Assessment.**  The most conservative and most likely to work; also the
   most laborious.  The base is no longer a monoid's delooping but a genuine
   category of contexts, and every piece of the present development (J, T,
   the interchange proof) must be re-derived over it.

2. **Tower / bootstrap.**  Iterate the present construction: the arities of
   the object syntax are the expressions of a classifier syntax, itself a
   higher-rank syntax over a simpler carrier, down to a simply-typed base.
   Judgement forms are the "sorts" of the classifier level.

   **Assessment.**  Cannot express genuine dependency by itself: in
   dependent type theory types contain terms, so the classifier level is
   not *below* the expression level — a tower stratifies judgement *forms*
   (`Ty` before `Tm`) but the *expressions* at all forms are mutually
   defined.  At most an organizing device for the forms, layered over
   candidate 1 or 3.

3. **Self-referential carrier.**  Allow the carrier's arities to be
   expressions of the very syntax being defined (inductive-recursive /
   fixed-point flavor).

   **Assessment.**  The most direct match to the goal, and the most
   speculative: existence of the fixed point is itself a theorem to be
   proved, and the well-foundedness bookkeeping (which recursion is doing
   what) is delicate.  Likely the honest core of the problem.

### Target specializations

A **general theory** would be: a collection of judgement forms, each
assigned a boundary — a telescope of judgements over the earlier forms plus
a thesis with a hole — together with rules (symbols) whose arities are
rule-boundaries.  This should specialize:

- **CwFs / natural models**: two judgement forms, `Ty` and `Tm`, the
  boundary of `Tm` filled by a `Ty`-expression; representability of
  `Tm → Ty` is context extension.  The rank-2 test case for the semantics:
  algebras of the generalized monad at this carrier should be CwFs (or a
  mild variant).
- **Uemura's representable map categories / SOGATs**: judgement forms as
  generators of a category with representable maps; Uemura's framework
  should be the low-rank (second-order) fragment — judgement forms binding
  term-variables but not judgement-variables.
- **Cartmell's GATs** as the rank-1 dependent case.

These are goal posts, not ideas; they define success for direction 2.

### Open questions

- What is the correct notion of renaming/substitution between *dependent*
  contexts, and does the relative-monad structure survive?  `J` becomes
  slots-over-contexts; the monad laws should be re-provable by the same
  interchange scheme.
- Where do equational judgement forms fit?  In FTT equations are
  proof-irrelevant boundaries (filled by a dummy).  In the algebraic view
  they should correspond to imposing equations on the free algebra —
  connecting direction 2 back to direction 1.
- Does the semantics of the generalized setup — algebras of the generalized
  monad — specialize to CwF models in the rank-2 case and to Uemura's models
  in the SOGAT case?  This is the litmus test for "very general syntax with
  very general semantics".

## 4. How the two directions interact

The endpoint would be a single correspondence: carriers-with-judgement-forms
(presentations of theories) ↔ relative monads on the slots functor of the
associated context category, with algebras = models.  Direction 1 works this
out where the context structure is a monoid (simply typed); direction 2
identifies the context structure for which the same statement covers
dependent and multi-judgement theories.  Voevodsky's Lawvere-theory
equivalence is the rank-0 instance; CwFs and Uemura's framework should be
low-rank instances; higher rank is new territory.

## 5. Reading

- Altenkirch–Chapman–Uustalu, *Monads need not be endofunctors* — relative
  monads, algebras, Kleisli/EM, the Lan-based monoid view (skew monoidal).
- Voevodsky, *Lawvere theories and Jf-relative monads* (docs/1601.02158) —
  the rank-0 correspondence and its constructive treatment.
- Arkor–McDermott, *The formal theory of relative monads* and the relative
  algebraic theories line — modern relative-monad toolkit.
- Fiore–Plotkin–Turi, *Abstract syntax and variable binding*; Fiore–Mahmoud,
  *Second-order algebraic theories*; Fiore–Hur on second-order equational
  logic — the rank-1/rank-2 semantic checks and the equations layer.
- Uemura, *A general framework for the semantics of type theory* — the
  representable-map/SOGAT target; also Kaposi–Xie on SOGAT signatures and
  first-order semantics.
- Cartmell, *Generalised algebraic theories and contextual categories*.
- Bauer–Haselwarter–Lumsdaine, *Finitary type theories* (the
  `finitary-type-theories` repository) — boundaries, judgement forms,
  metavariable contexts, context-free judgements.
- Abbott–Altenkirch–Ghani, *Containers: constructing strictly positive
  types*; Altenkirch–Ghani–Hancock–McBride–Morris, *Indexed containers* —
  the decorated-container reading of carriers (§1).
- Gambino–Kock, *Polynomial functors and polynomial monads* (also
  Gambino–Hyland) — dependent polynomial functors; the precise sense in
  which `T` is polynomial.
- Kelly's clubs / familial functors, and the polynomial-monad and opetope
  literature (Kock et al.), for the combinatorics of trees whose arities
  are trees.
- Ahman–Chapman–Uustalu, *Directed containers* — a nearby container-plus-
  monoid-like-structure notion (they characterize comonads; the axioms
  differ from ours, but the flavor of "container with composition" is
  related).
