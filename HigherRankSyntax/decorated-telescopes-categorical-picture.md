# Decorated telescopes as an internal monoid of syntax modules

This note explains the mathematical picture behind the following result.

> Raw decorated telescopes form a module D over raw syntax. Their raw arity
> defines a natural transformation U from D to the constant arity functor.
> The slice category
>
>     ArMod_C = [Kl(T), Set] / Const(Arity)
>
> has a context-extension tensor, and D is a monoid object for that tensor.
> Its unit is the empty telescope and its multiplication is dependent
> telescope concatenation.

The example

    A : Type,  x : A

will run through the whole account. It is small enough to draw in one corner
of a blackboard, but it already exhibits the essential phenomenon: the
classification of a later declaration can mention an earlier declaration.

At this first layer, however, “A : Type” is still mnemonic. It says that A is
a raw slot of coarse class ty; it does not yet mean that a universe-formation
judgment has been derived. Likewise, a decoration contains raw classifier
expressions, not proofs that those expressions are well formed. That
distinction is the boundary between the present construction and the later
typing layer.


## 1. The raw syntax underneath the construction

Fix a raw carrier C. We use the following pieces of it.

- There is a set Ty of coarse syntactic classes. In the running example it
  contains two classes, ty and tm.

- There is a monoid of raw arities:

      (Arity, ⋈, 1)

  The product Γ ⋈ Δ means ordered juxtaposition. The unit 1 is the empty
  arity; the notation does not mean that it contains one variable.

- For arities Γ and α and a class τ, there is a set

      Γ ∋[τ] α

  of slots of Γ whose result class is τ and whose binding arity is α.
  The slots of Γ ⋈ Δ are, in order, the slots of Γ followed by those of Δ.
  The empty arity has no slots.

- Binding arities are well founded: the arity bound by a slot is smaller than
  the arity containing that slot. This permits recursively nested binding
  data.

A slot

    x : Γ ∋[τ] α

should be read as a possible head of an expression of class τ, with formal
arguments described by α. Every slot

    i : α ∋[σ] β

asks for an argument of class σ, formed in the ambient arity extended by the
variables β bound at that argument.

So an expression headed by x consists of one argument eᵢ for every slot i of
α:

    x : Γ ∋[τ] α
    eᵢ : Expr(Γ ⋈ βᵢ, σᵢ)  for every i : α ∋[σᵢ] βᵢ
    --------------------------------------------------
    x(eᵢ)ᵢ : Expr(Γ, τ)

This raw syntax has simultaneous substitution. A substitution

    σ : Ω → Ω′

assigns to every slot x : Ω ∋[τ] α an expression

    σ(x) : Expr(Ω′ ⋈ α, τ).

The extra α says that substitution respects the variables bound by the slot.
Eta-expansion gives identity substitutions, and simultaneous substitution
gives composition.

Categorically, raw expressions form a relative monad T. More precisely, its
object part is

    T(Ω)(α, τ) = Expr(Ω ⋈ α, τ),

and its Kleisli arrows are exactly the raw substitutions just described. Put

    K = Kl(T).

The objects of K are raw arities, and an arrow σ : Ω → Ω′ in K is a raw
simultaneous substitution. A module over this relative monad, in the
convention used here, is simply a covariant functor

    K → Set.


## 2. What a decorated telescope contains

### 2.1 The classifier policy

First choose a classifier policy

    bd : Ty → Option(Ty).

It says, once and for all, which coarse classes require classifiers and what
the class of such a classifier is. Define:

    C_bd(Ξ, τ) =
      {∗}         if bd(τ) = none
      Expr(Ξ, υ)  if bd(τ) = some(υ).

The singleton in the first case means that there is no classifier datum to
choose. The optionality is a policy for an entire coarse class, not a
slot-by-slot choice.

For the running example, take

    bd(ty) = none
    bd(tm) = some(ty).

Consequently, a type declaration carries no further classifier, while a term
declaration carries a raw type expression. The declaration A : Type has the
unique trivial classifier; the declaration x : A has the raw type expression
A as classifier.


### 2.2 Precedence

A classifier may mention earlier declarations but not later ones. To make
“earlier” meaningful for a general carrier, fix a coherent precedence
structure.

For every slot x : Δ ∋[τ] α, it supplies arities

    before(x)
    after(x)

and a factorization

    before(x) ⋈ after(x) = Δ.

The slot x is localized in the second factor, and reinserting that local slot
into the whole product recovers x. Thus after(x) includes x itself.

The choices are compatible with concatenation.

- A slot inherited from the left side of Γ ⋈ Δ has the same preceding part
  as before, while its following part is extended by Δ.

- A slot inherited from the right side has

      Γ ⋈ before(x)

  before it and the same following part as before.

For ordinary list-shaped telescopes this is the expected split: before(x) is
the strict list prefix preceding x, while after(x) is the list beginning at x.

In the combined raw shape 𝐀 ⋈ 𝐱 of the running example:

    before(A) = 1
    before(x) = 𝐀.

This is exactly why the classifier of x is allowed to mention A. Although
after(x) does not appear in the classifier formula, it certifies that the
chosen prefix really is a segment of the ambient arity and makes prefix
restriction and concatenation coherent.

This is genuine extra structure. A well-order on each slot fibre does not by
itself guarantee that every strict prefix is represented by a raw arity, much
less that those representatives are coherent with concatenation.


### 2.3 Recursion into binding arities

A top-level slot can itself bind an arity, and that binding arity can contain
slots with their own binding arities. Therefore it is not enough to attach a
classifier only to each immediate slot. For every immediate slot, we also
recursively decorate its entire binding arity.

Concretely, consider

    x : Δ ∋[τ] α.

When x is reached, the available base is Ω ⋈ before(x). A decoration must
therefore provide two pieces of data:

1. a decoration of α over Ω ⋈ before(x), describing the classifiers of all
   variables bound by x and recursively of anything they bind; and
2. a classifier for x itself over Ω ⋈ before(x) ⋈ α.

The recursion is legitimate because binding arities are well founded. Both
declarations in A : Type, x : A are nullary, so their binding arity is empty
and the recursive component is trivial. The recursive component becomes
essential in higher-rank syntax, where a declaration or operation binds a
nonempty local telescope.


### 2.4 The full definition of decoration

Let Ω be an external raw base and let Δ be a raw telescope shape. Define
Dec_bd(Ω, Δ) recursively by saying that, for every immediate slot

    x : Δ ∋[τ] α,

a decoration contains the pair

    nested_x : Dec_bd(Ω ⋈ before(x), α)
    classifier_x : C_bd(Ω ⋈ before(x) ⋈ α, τ).

In compact form:

    Dec_bd(Ω, Δ)
      =
    ∏ over x : Δ ∋[τ] α
      ( Dec_bd(Ω ⋈ before(x), α)
        × C_bd(Ω ⋈ before(x) ⋈ α, τ) ).

The classifier context is assembled in this order:

    Ω ⋈ before(x) ⋈ α

| component | meaning |
|---|---|
| Ω | the external base |
| before(x) | preceding slots of the ambient telescope |
| α | variables bound by the selected slot |

This is the dependency discipline of the first layer. A classifier can refer
to the external base, to its earlier siblings, and to the variables bound at
its own slot. It cannot refer to the slot being classified or to later
siblings. Applying the same clause recursively inside α imposes this discipline
at every nesting depth.

A decorated telescope over Ω is a raw shape together with such a decoration:

    D(Ω)
      = DTel_bd(Ω)
      = ∑ over Δ : Arity  Dec_bd(Ω, Δ).

For Γ ∈ D(Ω), write |Γ| for its raw shape.

The external base Ω is deliberately a raw arity, not an already decorated
context. A decorated telescope decorates its own new segment; it does not
redundantly decorate its external environment. At this layer we are recording
raw classifier data over arbitrary raw environments, not selecting well-formed
bases.

This is also what lets the construction remain generic in the raw syntax
rather than relative to a fixed signature. A decorated signature is the
special rooted case: a decorated raw arity over the empty base 1. In other
words, it is an element of D(1). It is one possible use of the generic
construction, not an input needed to define D.


### 2.5 Slot boundaries

The preceding definition can be repackaged locally around a slot. If

    Γ ∈ D(Ω)
    x : |Γ| ∋[τ] α,

then the decorated boundary of x is

    ∂Γ(x) = (Γ_before(x), Bₓ, clΓ(x)).

The three components are:

- Γ_before(x) ∈ D(Ω), the decorated restriction of Γ to before(x);

- Bₓ ∈ D(Ω ⋈ |Γ_before(x)|), the decorated binding arity of x, whose raw
  shape is α;

- the classifier

      clΓ(x)
        ∈ C_bd(Ω ⋈ |Γ_before(x)| ⋈ |Bₓ|, τ).

So the boundary says exactly what is already available when the slot is
reached, what variables it binds locally, and how it is classified there.
The decoration of Bₓ is the nested part of the original decoration. This
local view is particularly useful when one later states formation or typing
rules.


### 2.6 The running example as a decoration

Let 𝐀 be a raw one-slot arity containing a nullary ty-slot, and let 𝐱 be a raw
one-slot arity containing a nullary tm-slot. “Nullary” means that the binding
arity of each slot is the empty arity 1.

First form

    Γ_A = (A : Type) ∈ D(1).

Its only classifier is the unique element of the singleton associated to
bd(ty) = none.

Next, with A now in the raw external base, form

    Γ_x = (x : A) ∈ D(𝐀).

The shape of Γ_x is 𝐱, and the classifier attached to its term slot is the raw
expression selecting the external type variable A.

After the two pieces are joined, the boundaries in the complete telescope
look as follows.

| slot | preceding decorated telescope | binding telescope | classifier |
|---|---|---|---|
| A | empty | empty | the unique trivial value |
| x | A : Type | empty | the raw type expression A |

The same occurrence of A admits two complementary readings.

- In the separate tail Γ_x ∈ D(𝐀), it is an external-base variable.
- In the joined telescope A : Type, x : A, it is a preceding sibling.

Dependent concatenation is precisely the operation that turns the first
reading into the second.


## 3. Decorated telescopes form the syntax module D

Let σ : Ω → Ω′ be a raw Kleisli substitution. It acts on a decorated
telescope by substituting in every expression-valued classifier and leaving
the raw telescope shape unchanged:

    D(σ) : D(Ω) → D(Ω′)
    D(σ)(Δ, d) = (Δ, σ∗d).

For an immediate slot x : Δ ∋[τ] α, the action has two clauses.

1. On the nested decoration of α, use σ ↑ before(x). This substitutes in Ω
   while leaving the preceding slots fixed, and then continues recursively
   inside α.

2. On an expression-valued classifier

       classifier_x : Expr(Ω ⋈ before(x) ⋈ α, υ),

   use the lifted substitution σ ↑ (before(x) ⋈ α):

       Ω ⋈ before(x) ⋈ α → Ω′ ⋈ before(x) ⋈ α.

   It substitutes in the old external base Ω while fixing the preceding slots
   and bound variables. If the selected coarse class has no classifier, the
   unique singleton value remains unchanged.

Raw substitution has identity and composition laws, and lifting respects both
of them. Therefore:

    D(id_Ω) = id_D(Ω)
    D(θ ∘ σ) = D(θ) ∘ D(σ).

This proves that

    D : K → Set

is a module over the raw relative monad T.

The simplest nontrivial instance is the tail x : A. Suppose

    σ : 𝐀 → Ω′

sends the raw type variable A to a raw type expression B in Ω′. Suppressing
the canonical empty-arity unit factor, the action is

    D(σ)(x : A) = x : B.

The term-slot shape has not changed; only its classifier has been substituted.
This is the exact sense in which decorated telescopes form a syntax module.

There is a useful subtlety here. The complete rooted telescope

    A : Type, x : A  ∈ D(1)

has empty external base, so it has no interesting external variables to
substitute. To see the module action, one regards A as already present and
studies the tail x : A ∈ D(𝐀).

To see how a fresh A and its dependent x are assembled into a rooted context,
one instead uses the tensor and monoid multiplication below. These are two
different, complementary roles of the same example.


## 4. Remembering shape: the object (D, U)

Let

    Const(Arity) : K → Set

be the constant functor with value Arity. At every object it has the same
value—the whole set of raw arities—and every Kleisli arrow acts as the
identity function on that set.

Erasure gives maps

    U_Ω : D(Ω) → Arity
    U_Ω(Γ) = |Γ|.

Substitution changes classifiers but not telescope shape:

    U_Ω′(D(σ)(Γ)) = U_Ω(Γ).

Hence the maps U_Ω form a natural transformation

    U : D ⇒ Const(Arity).

Now define

    ArMod_C = [K, Set] / Const(Arity).

An object of ArMod_C is:

1. a syntax module M : K → Set, and
2. a substitution-invariant shape map

       U_M : M ⇒ Const(Arity).

A morphism

    f : (M, U_M) → (N, U_N)

is a natural transformation f : M ⇒ N that preserves shape:

    U_N(f(m)) = U_M(m).

Thus (D, U) is an object of ArMod_C.

Passing to the slice is not cosmetic. The shape |Γ| tells us by how much the
external base must be extended before a subsequent telescope segment can be
formed.

In the running example:

    U_1(Γ_A) = 𝐀
    U_𝐀(Γ_x) = 𝐱.

The module action x : A ↦ x : B leaves the second equation's right-hand side
equal to 𝐱. That shape invariance is what allows x : A to be used uniformly as
a one-declaration tail while its classifier changes.


## 5. The context-extension tensor on ArMod_C

### 5.1 Extending the base

For every raw arity Φ, there is a base-extension functor

    E_Φ : K → K
    E_Φ(Ω) = Ω ⋈ Φ.

On a substitution it acts by lifting:

    E_Φ(σ) = σ ↑ Φ.

The lifted substitution acts on the old base and fixes the newly appended
Φ-slots. There are coherent canonical comparisons

    E_1 ≅ Id_K
    E_Φ E_Ψ ≅ E_(Φ ⋈ Ψ).

These comparisons are the categorical form of “extending by nothing does
nothing” and “two successive extensions are one extension by the composite
arity.”

Nothing in the tensor construction itself requires T to be the raw syntax
monad. More generally, for any relative monad R on the same raw arities, a
coherent action by suffix extension gives the slice

    ArMod_R = [Kl(R), Set] / Const(Arity)

the same context-extension tensor. Raw syntax supplies the present instance
through ordinary lifted substitution. This genericity is important later:
an equation quotient can acquire its own suffix-extension action and hence
use the same monoidal category construction, rather than duplicating it.

For the running example, lifting a substitution under 𝐀 means: substitute in
whatever older base existed before A, but hold the freshly added A-slot fixed.
That is exactly the discipline needed when transporting the later segment
x : A.


### 5.2 Tensoring two arity-shaped modules

For (M, U_M) and (N, U_N) in ArMod_C, define

    (M ⊗tel N)(Ω)
      =
    ∑ m ∈ M(Ω)  N(Ω ⋈ U_M(m)).

An element is a pair (m, n) formed in two stages:

1. choose m over the original base Ω;
2. extend the base by the shape of m, then choose n.

Its total shape is

    U_(M ⊗tel N)(m, n) = U_M(m) ⋈ U_N(n).

This is not the pointwise cartesian product of functors. The base in which the
second component lives depends on the shape of the first. The tensor is
therefore a categorical encoding of dependent sequencing.

For a substitution σ : Ω → Ω′, its action is

    (M ⊗tel N)(σ)(m, n)
      =
    ( M(σ)(m),  N(σ ↑ U_M(m))(n) ).

The first segment is reindexed normally. The second is reindexed under the
first segment, whose slots must remain fixed. Since U_M is natural,
M(σ)(m) has the same shape as m, so the result has exactly the required
target base.

For shape-preserving natural transformations f : M ⇒ M′ and g : N ⇒ N′,
the tensor morphism acts by

    (f ⊗tel g)(m, n) = (f(m), g(n)),

with the canonical identification of the second base supplied by shape
preservation. This makes ⊗tel bifunctorial.


### 5.3 Unit, associator, and unitors

The tensor unit 𝕀 is the constant singleton module whose unique element has
empty shape:

    𝕀(Ω) = {∗}
    U_𝕀(∗) = 1.

The associator merely changes the placement of the cut between three
successive segments:

    ((m, n), p)  ↔  (m, (n, p)).

The underlying bases are identified using associativity of ⋈ and the
comparison

    E_Φ E_Ψ ≅ E_(Φ ⋈ Ψ).

The left and right unitors erase a unique empty segment. The pentagon and
triangle express the fact that repeated reassociation and insertion or
deletion of empty segments are coherent. Consequently

    (ArMod_C, ⊗tel, 𝕀)

is a monoidal category.

This tensor is ordered and is not expected to be symmetric: interchanging two
telescope segments can invalidate dependencies of the second on the first.

Moreover, the slice does not acquire this tensor merely by being a slice.
The construction depends essentially on coherent fixed-suffix extension in
the raw syntax Kleisli category.


### 5.4 The running example inside the tensor

Recall:

    Γ_A = (A : Type) ∈ D(1)
    Γ_x = (x : A)    ∈ D(1 ⋈ |Γ_A|).

Therefore:

    (Γ_A, Γ_x) ∈ (D ⊗tel D)(1).

This pair is the categorical form of the instruction:

> First add A : Type; in the resulting extended base, add x : A.

At this point the pair still remembers the cut between the two stages. Its
total raw shape is

    |Γ_A| ⋈ |Γ_x|.

The monoid multiplication will erase the cut while retaining exactly the
dependency information needed by the classifier of x.



## 6. Decorated telescopes form a monoid object

We now give the object (D, U) a unit and multiplication in ArMod_C.


### 6.1 Unit: the empty decorated telescope

For every base Ω, there is a unique decoration of the empty arity, because it
has no slots. This gives a shape-preserving natural transformation

    η : 𝕀 → D
    η_Ω(∗) = ∅_Ω.

Its shape is 1, as required.


### 6.2 Multiplication: dependent concatenation

Suppose

    Γ ∈ D(Ω)
    Δ ∈ D(Ω ⋈ |Γ|).

Their dependent concatenation

    Γ ; Δ ∈ D(Ω)

has raw shape

    |Γ ; Δ| = |Γ| ⋈ |Δ|.

Its decoration is obtained as follows.

- A slot coming from Γ keeps its preceding part and all of its classifier
  data. Only its following part grows by |Δ|.

- A slot y coming from Δ acquires the additional prefix |Γ|:

      before_(Γ ; Δ)(y)
        =
      |Γ| ⋈ before_Δ(y).

  Its old classifier context

      (Ω ⋈ |Γ|) ⋈ before_Δ(y) ⋈ α

  is canonically the required new context

      Ω ⋈ (|Γ| ⋈ before_Δ(y)) ⋈ α.

- The same construction is applied recursively inside every binding arity, so
  bound arities retain their own decorated internal structure.

Thus concatenation defines a shape-preserving map

    μ : D ⊗tel D → D
    μ(Γ, Δ) = Γ ; Δ.

It is a natural transformation because substitution commutes with dependent
concatenation:

    D(σ)(Γ ; Δ)
      =
    D(σ)(Γ) ; D(σ ↑ |Γ|)(Δ).

The lift on the second component is not an auxiliary nuisance; it is exactly
the action built into the tensor. Hence this equation is precisely the
naturality square for μ.


### 6.3 The monoid laws

The empty telescope is a left and right unit for concatenation, and
concatenation is associative up to the canonical associativity identification
of raw bases:

    ∅ ; Γ ≅ Γ
    Γ ; ∅ ≅ Γ
    (Γ ; Δ) ; Θ ≅ Γ ; (Δ ; Θ).

Categorically these are exactly the internal-monoid diagrams:

    μ ∘ (η ⊗tel id_D) = λ_D
    μ ∘ (id_D ⊗tel η) = ρ_D

and

    μ ∘ (μ ⊗tel id_D)
      =
    μ ∘ (id_D ⊗tel μ) ∘ a_(D,D,D),

where a, λ, and ρ are the associator and unitors of the context-extension
tensor.

We have therefore obtained a monoid object

    (D, U, η, μ) ∈ Mon(ArMod_C).



## 7. What the monoid theorem is really saying

Unpacked, the assertion that decorated telescopes form a monoid in ArMod_C
says considerably more than “telescopes can be concatenated.”

1. **Classifier substitution is functorial.** Every raw substitution acts on
   every classifier at every nesting depth, with identities and composites
   behaving correctly.

2. **Raw shape is stable under substitution.** Reindexing changes classifier
   expressions, not the layout of the telescope.

3. **Telescope segments can be sequenced dependently.** The second segment is
   formed over the base extended by the first segment's shape.

4. **Substitution respects sequencing.** Older variables are substituted in
   both segments, while the freshly introduced first segment is fixed when
   reindexing the second.

5. **The cut between segments is inessential.** Empty cuts and different
   parenthesizations lead canonically to the same decorated telescope.

6. **All of this is generic.** The construction uses the raw carrier, raw
   expression monad, precedence, and classifier policy, but no fixed signature
   and no particular typing rules.

The conceptual division of labour is:

| object | role |
|---|---|
| T | raw expression formation and simultaneous substitution |
| D | raw classifier data transported by that substitution |
| U | substitution-invariant telescope shape |
| ⊗tel | dependent sequencing of shaped modules |
| μ | flattening successive decorated telescope segments |

One should not conclude that D is itself a new syntax monad. At this layer,
D is a module over T and, after remembering shape, a monoid object for the
context-extension tensor.

A genuinely typed or dependently classified syntax requires an additional
layer selecting the well-formed decorated contexts, telescopes, and
expressions and proving that this selection is closed under the operations
above.

Nor does the internal-monoid result alone supply a contextual category,
comprehension category, C-system, fibred relative monad, or freeness theorem.
Those would be additional constructions or results.


## 8. Adding equations without losing the categorical structure

Suppose a fixed raw signature is equipped with equation schemas, and let T_E
be the relative monad obtained by quotienting raw expressions by the generated
structural, substitution-stable congruence. The source slots remain ordinary
sets. Only expression fibres are quotiented.

Equations compare decorations pointwise. An unclassified slot has no equation
data to check. For an expression-classified slot, its two classifiers are
compared by the generated expression congruence in that site's full context:
external base, preceding siblings, and bound variables. The same comparison is
made recursively inside every binding arity. Raw telescope shapes are never
identified.

Consequently the quotient telescope family has the form

    D_E(Γ)
      =
    Σ Δ : Arity,  Dec_bd(S ⋈ Γ, Δ) / equations.

A quotient substitution acts on D_E by substituting in classifier
representatives and then forgetting the representatives. Two-sided
substitution congruence makes the result independent of every choice. Thus

    D_E : Kl(T_E) → Set

is again a syntax module, and its literal raw-shape projection is again
natural.

The quotient Kleisli category inherits coherent extension by raw suffixes.
Therefore the same context-extension tensor applies to

    ArMod_(T_E) = [Kl(T_E), Set] / Const(Arity).

Empty telescope and dependent concatenation respect pointwise decoration
equality, so they descend to D_E. Their equations are inherited from the raw
operations. The quotient result is therefore another internal monoid:

    D_E ∈ Mon(ArMod_(T_E)).

For the running example, suppose the equation presentation proves

    A ≈ B.

The raw decorations x : A and x : B are different data, but their classifier
expressions represent the same quotient class. They therefore determine the
same element of D_E. Substitution can instantiate A ≈ B, and structural
congruence carries it into larger classifiers such as P(A) ≈ P(B). Throughout,
the telescope still has exactly one raw term slot: equations alter classifier
annotations, not shape.

This quotient theorem is still T1. It says that boundary annotations may be
compared and quotienting is compatible with substitution and telescope
concatenation. It does not say that A or B is a well-formed type, that x has
either type, or that a conversion judgment is admissible. Those assertions
require the later T2 judgment layer.



## 9. Extended example at the T1/T2 boundary: a type family

The simple telescope A : Type, x : A is the clearest example for the
categorical construction. The following stronger example is best kept as a
separate final section because it tests the limits of T1:

    A : Type
    P : (z : A) → Type
    x : A
    y : P(x).

The notation is deliberately suggestive. At T1 it does not assert a derived
dependent-function type or a typing judgment. It abbreviates raw slots and
their decorations.

### The raw pieces

Let 𝐀 be a one-slot raw arity containing a nullary ty-slot A. Let 𝐏 be a
one-slot raw arity containing a ty-slot P whose argument arity is 𝐳. The
arity 𝐳 has one nullary tm-slot, called z. Finally, let 𝐱 and 𝐲 be nullary
tm-slot arities for x and y.

The slot data for P is therefore:

    Pslot : 𝐏 ∋[ty] 𝐳
    zslot : 𝐳 ∋[tm] 1.

The important point is that z is not an additional outer declaration. It is
the unique argument position in P's binding arity. The notation

    P : (z : A) → Type

is a convenient way of saying that this argument position is term-like and
that its decoration will be the raw type expression A.

### The four decorated segments

The four pieces are formed over successively extended raw bases:

    Γ_A = (A : Type)              ∈ D(1)
    Γ_P = (P : (z : A) → Type)    ∈ D(𝐀)
    Γ_x = (x : A)                 ∈ D(𝐀 ⋈ 𝐏)
    Γ_y = (y : P(x))              ∈ D(𝐀 ⋈ 𝐏 ⋈ 𝐱).

For Γ_P, the outer P-slot has before(Pslot) = 1. Its decoration therefore
has two components.

First, it has a nested decoration

    nested_P : Dec_bd(𝐀 ⋈ 1, 𝐳).

The arity 𝐳 has only the slot zslot, with before(zslot) = 1 and binding arity
1. Thus the nontrivial part of nested_P is the classifier

    classifier_z
      : ClassifierAt_bd((𝐀 ⋈ 1) ⋈ 1 ⋈ 1, tm)
      = Expr((𝐀 ⋈ 1) ⋈ 1 ⋈ 1, ty).

It is the eta-expanded raw expression selecting A, up to the canonical unit
reassociations:

    classifier_z = A.

Second, P itself has the classifier

    classifier_P
      : ClassifierAt_bd(𝐀 ⋈ 1 ⋈ 𝐳, ty).

Since bd(ty) = none, this is the unique trivial value. P is a type-like slot,
so T1 does not attach a type expression to P itself. Its dependency on A is
recorded inside its argument arity, through classifier_z.

### Precisely what the decoration of y means

Now take the y-segment. Its external raw base is

    Ω_y = 𝐀 ⋈ 𝐏 ⋈ 𝐱.

Its raw shape 𝐲 has a unique slot

    yslot : 𝐲 ∋[tm] 1,

with before(yslot) = 1 and binding arity 1. Therefore the decoration of this
slot is the pair

    nested_y : Dec_bd(Ω_y ⋈ 1, 1)
    classifier_y : ClassifierAt_bd(Ω_y ⋈ 1 ⋈ 1, tm).

The first component is the unique empty decoration. The classifier policy
turns the second component into

    classifier_y : Expr(Ω_y ⋈ 1 ⋈ 1, ty).

This raw expression is what the notation P(x) abbreviates.

To construct P(x), take the P-slot from 𝐏 and include it into the larger raw
base Ω_y. Its head has result class ty and argument arity 𝐳. The unique
argument position is zslot. Fill that position with the eta-expanded x-slot
from Ω_y:

    argument(zslot) = η(xslot).

The raw application headed by P with this argument is the expression

    P(x) : Expr(Ω_y ⋈ 1, ty),

again with the harmless empty-arity factors reassociated to match the
classifier context Ω_y ⋈ 1 ⋈ 1. Thus, in complete detail, the decoration of
the y-slot is

    yslot ↦
      ( empty decoration,
        raw application headed by P and supplied with η(x) ).

Nothing in this pair is a proof that the argument x has the classifier A. The
decoration of P records that A is the intended classifier of its argument
position, and the decoration of x records that x has classifier A, but T1 has
no rule comparing the expected and actual classifiers of a raw application.

After concatenating all four segments into a rooted telescope, the y-slot has
preceding raw shape

    𝐀 ⋈ 𝐏 ⋈ 𝐱.

Its classifier is then viewed in the equivalent rooted context

    1 ⋈ 𝐀 ⋈ 𝐏 ⋈ 𝐱 ⋈ 1,

which is exactly the same classifier context as Ω_y ⋈ 1 ⋈ 1, by the unit and
associativity laws for raw arities.


### What T1 captures, and what it cannot capture

T1 records:

- that A is a raw ty-slot;
- that P is a raw ty-slot with one tm argument position;
- that the argument position z of P is classified by A;
- that x has raw classifier A;
- that y has raw classifier P(x);
- that all these classifier expressions transport functorially under raw
  substitution;
- that the four segments can be sequenced and flattened by the tensor and
  monoid structure.

T1 does not establish:

- that A is a well-formed type;
- that P is a well-formed type family;
- that every actual argument supplied to P has type A;
- that P(x) is a well-formed type;
- that x : A or y : P(x) is derivable.

The sharp counterexample is P(y). The raw expression grammar accepts it:
P asks for an argument of coarse class tm, and y also has coarse class tm. The
decorations separately record that P's argument should be classified by A and
that y is classified by P(x), but T1 contains no judgment comparing those two
classifiers. Consequently T1 could attach P(y) as the raw classifier of a
later slot w:

    w : P(y).

Unless an appropriate equality is available, the typing layer should reject
this declaration because y is not known to have type A. That rejection is
exactly the sort of rule that T2 must add: a well-formed-expression judgment
must inspect both the decorated argument boundary of P and the classifier of
the actual argument supplied to it.
