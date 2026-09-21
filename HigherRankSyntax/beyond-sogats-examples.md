# Beyond SOGATs: examples

Theories expressible in the framework that fail `beyond-sogats-syntactic.md`
Definition 1.1, so the rank-lowering theorem of `rank-and-sogats.md` §1 does not
apply to them. Companion to `beyond-sogats-semantics.md`, which supplies the
framing and the propositions.

Marks: `[proved]`, `[routine]`, `[open]`.

Notation: Part I writes a declaration as `Bind(Θ, β)`, Part II as `[Θ] β`
with slots `x : A` and `X : Sort`. Same thing.

`metatheory.md` extracts the pattern common to §1, §2 and §8: the rank-4
examples here are all instances of `Ξ ↦ Ξ⁺`, adding to a signature the ability
to reason about its own syntax.

---

## 0. The recipe

Two ways to fail Definition 1.1, and they behave differently.

```text
(i) fails    a sort or eq entry occurs INSIDE a binding
             usually the Russell reading of something type theory writes à la Tarski
(ii) fails   rank ≥ 4: a binding is nested two deep
             an operation that CONSUMES a binder rather than producing one
```

The second is the sharper phenomenon, because it is not a formalization choice:

> Producing a binder is rank-cheap; consuming one is rank-expensive. A constructor
> has its binding as an **outermost** argument list, so by `sogats.md` §3.5 the `Π`
> is only sectioned and `𝒫` never sees it. An eliminator has the same telescope
> **nested** inside a branch, so the `Π` must be evaluated, and reification needs
> it in `𝒫`.

Hence every infinitary datatype has a rank-3 constructor and a rank-4 eliminator.

---

## 1. λ-syntax with a case operator

The worked example. `beyond-sogats-semantics.md` Proposition 3.3 uses a minimal
but cooked-up `Ξ`; this one occurs for its own sake and has a named non-degenerate
model in the gap.

### 1.1 The signature

Pattern matching on λ-terms, with variables and terms as separate sorts and a
result sort `R`.

```text
Ξ = [ V : sort,  T : sort,  R : sort,
      var  : Bind([x : of V], of T),
      app  : Bind([s : of T, u : of T], of T),
      lam  : Bind([b : Bind([x : of V], of T)], of T),
      case : Bind(Θ, of R),
      β_var, β_app, β_lam ]

Θ = [ t : of T,
      v : Bind([x : of V], of R),
      a : Bind([s : of T, u : of T], of R),
      l : Bind([b : Bind([x : of V], of T)], of R) ]

β_lam : Bind(Θ',  eq (case (lam b) v a l) (l b))
        Θ' = [b : Bind([x : of V], of T)] ⋈ [v, a, l as above]
```

`R` is a **declared** sort, not bound. Making `case` polymorphic would put
`R : sort` inside a binding and fail clause (i) of
`beyond-sogats-syntactic.md` Definition 1.1; as written the theory fails **(ii)
alone**.

### 1.2 Rank, and where the difference lies

```text
[x : of V]                         rank 1
[b : Bind([x : of V], of T)]       rank 2
lam                                contributes 3        so var/app/lam alone: rank 3
l                                  contributes 3
Θ                                  rank 3
case, β_lam                        contribute 4         so rank Ξ = 4
```

So the syntax `[V, T, var, app, lam]` is rank 3 — a SOGAT, and Kaposi–Xie's own
running example. Adding the eliminator that inspects a binder pushes it to 4.

The telescope responsible is the *same* one in both places, and only its position
differs:

> In `lam`, `[b : Bind([x : of V], of T)]` is the slot's **own argument list** —
> an outermost `Π`, only *sectioned*, so `sogats.md` §3.5 makes it `𝒫`-free.
> In `case` the same telescope is the binding of the entry `l`, hence **nested**,
> so its `Π` must be *evaluated*, and reification needs it in `𝒫`.

### 1.3 The standard model refuses it

Take `𝒞 := 𝔽^op` with `𝔽` finite sets and all functions, so that
`PSh(𝒞) = [𝔽, Set]` and `よI = 𝔽(I,−)`. A presheaf is thus a covariant functor on
contexts and renamings.

```text
V := よ1                 V(n) = 𝔽(1,n) = n,  the variables available in context n
T := the initial algebra of  Σ X = V + X × X + δX,   δX(n) := X(n+1)

T(n) = α-equivalence classes of λ-terms with free variables in n
       T(n) ∋   x_i   (i ∈ n)  |   s u   (s, u ∈ T(n))  |   λ. b   (b ∈ T(n+1))
T(f) : T(n) ⟶ T(m)  for f : n ⟶ m   renames each free variable i to f i
```

The functor `δ` is the exponential by `V`. Products in `[𝔽, Set]` are pointwise,
and a pair of maps out of `n` and out of `1` is one map out of the coproduct, so

```text
(よn × よ1)(m)  =  𝔽(n,m) × 𝔽(1,m)  ≅  𝔽(n ⊔ 1, m)  =  よ(n+1)(m)
```

`よ` carrying the coproduct of contexts to a product of presheaves, with `n ⊔ 1`
the context `n` extended by one fresh variable. Hence

```text
(V ⇒ X) n   ≅  Hom(よn, V ⇒ X)     Yoneda
            ≅  Hom(よn × V, X)     exponential adjunction
            =  Hom(よn × よ1, X)    V = よ1
            ≅  Hom(よ(n+1), X)     the display above
            ≅  X(n+1)  =  δX n     Yoneda
```

so `δ ≅ (V ⇒ −)` and `(V ⇒ T)(n) = T(n+1)`: a function from variables to terms in
context `n` is a term in context `n+1`, the extra variable being the one abstracted
over. That is what a λ-body is.

**Lemma 1.3.1.** `V` is locally representable; `V ⇒ T` is not. `[proved]`

*Proof.* Local representability reads `𝔽(I ⊲ A, J) ≅ 𝔽(I,J) × A(J)`. For `A = V`,
`𝔽(I,J) × 𝔽(1,J) ≅ 𝔽(I+1,J)`, so `I ⊲ V := I+1`. For `A = V ⇒ T` take `I := 0`,
initial in `𝔽`, so `よ0 = 1`; the condition becomes `𝔽(k,J) ≅ T(J+1)` for
`k := 0 ⊲ A`, i.e. `J^k ≅ T(J+1)`. At `J = 1` the left side is a singleton and
`T(2)` is infinite. ∎

So `[b : Bind([x : of V], of T)] ∉ 𝒫` is **forced by the intended model**, not
chosen, and reification cannot be applied without discarding that model:

```text
Mod(Ξ, 𝒫-full)  ⊊  Mod(Ξ, 𝒫 without the l-binding)      the term model is in the gap
```

This is what §3's example lacks. There, and in every `𝒫`-variation tried before
it, the two classes were not known to differ at any base.

### 1.4 `case` is definable, not stipulated

In `Set^𝔽` the signature endofunctor is `Σ X = V + X × X + δX` with
`δX(n) = X(n+1)`, and `T` is its initial algebra. By Lambek the structure map

```text
[var, app, lam] : V + T × T + δT  ⟶  T
```

is an isomorphism, so `case` is copairing composed with its inverse, and
`β_var`, `β_app`, `β_lam` say exactly that. `Set^𝔽` is a presheaf topos, hence
cartesian closed, so `⟦Θ⟧ = T × R^V × R^{T×T} × R^{δT}` exists and
`⟦case⟧ ∈ Hom(⟦Θ⟧, R)` is a composite of morphisms. `[proved]` (Fiore–Plotkin–Turi,
*Abstract Syntax with Variable Binding*.)

**Remark 1.4.0 (what is cited, and what is not).** Fiore–Plotkin–Turi supply the
*model*: the setting `Set^𝔽`, the presheaf `V = よ1`, the functor `δ`, binding
signatures, and the theorem that the initial algebra exists and is λ-terms modulo
α, carrying a substitution monoid structure. They do **not** study the signature
of 1.1; `case` does not appear there, and is Lambek applied to their theorem.

The difference is the source of the rank.

```text
FPT     T is the initial Σ-algebra       a PROPERTY of one presheaf
1.1     case is a declared operation     STRUCTURE demanded of every model
        with three equations
```

A model of `Ξ` need not have `T` initial — the three equations make the structure
map only split monic. Initiality is a property, and properties cost no rank, being
statements about a particular model. Declaring the eliminator turns the property
into structure, and the structure is rank 4.

The three `β` equations make the structure map split monic. Adding exhaustiveness
— `case t var app lam = t`, which typechecks only at `R := T` — forces it
invertible.

**Remark 1.4.1 (why there is no object-level β, and what happens if there is).**
`β_var`, `β_app`, `β_lam` are the equations *for `case`*; `Ξ` states no equation
for the object language, so `T` is raw λ-terms modulo α and `(λx.x) y` and `y` are
distinct elements of `T(1)`. In the two-sorted presentation β is not even statable
without more: `b : V ⇒ T` consumes a *variable*, so `b u` is ill-typed for `u : of T`,
and one must first adjoin `subst : Bind([b : Bind([x : of V], of T), u : of T], of T)`.

Adjoining it, with `β_obj : app (lam b) u = subst b u`, collapses the theory. Take
`b := x ↦ var x` and `u := var y`, so `app (lam b) (var y) = var y`; then

```text
case (app (lam b) (var y)) v a l  =  a (lam b) (var y)      β_app
case (var y)               v a l  =  v y                     β_var
```

and the arguments agree, so `a (lam b) (var y) = v y` for every `a` and `v`,
forcing `R` subterminal.

This is the right way round. `case` is available above *because* `T` is an initial
algebra — Lambek's isomorphism says exactly that the constructors are jointly
surjective and disjoint — and β destroys that, `str` ceasing to be injective. The
incompatibility of pattern matching with β-conversion is classical, and it is why
metaprogramming operates on raw or normal forms. It makes the example more
natural, not less: the metatheory of a type theory manipulates raw syntax, which
is the setting Fiore–Plotkin–Turi axiomatise.

### 1.5 The binder is not finitary

**Lemma 1.5.1.** `V ⇒ T` is not finitely presentable in `Set^𝔽`. `[proved]`

*Proof.* `V ⇒ T` is the filtered union of the subpresheaves of bodies of bounded
size. Were it finitely presentable, `id` would factor through one of them, making
`V ⇒ T` a retract of a subobject of itself, hence equal to it. ∎

By `beyond-sogats-semantics.md` §3.2, `(−)^{V ⇒ T}` therefore does not preserve filtered colimits, so the
binder of `case` is not a finitary operation. This is the concrete witness the
finitarity route of `rank-and-sogats.md` §3 needed, and it applies here without
requiring `Mod(Ξ,𝒫)` to be a category.

### 1.6 What this establishes

```text
a natural rank-4 theory failing Definition 1.1 on clause (ii)          [proved]
its intended model forces the binding out of 𝒫                         [proved]
case is definable in that model, so the theory is not a stipulation    [proved]
the binder is not finitary                                             [proved]
no first-order presentation exists                                     [open]
```

The last is the gap. Failing Definition 1.1 says the theory is not second-order
by a criterion built to be *sufficient* for SOGATs, never proved to characterise
them. Lemma 1.5.1 is the input to `beyond-sogats-semantics.md` Proposition 3.3's argument; discharging it for
this `Ξ` is what would make the example a theorem rather than a witness.

**Remark 1.6.1 (the polymorphic variant, and why it is not used).** Binding the
result sort,

```text
case : Bind([R : sort, t : of T, v : Bind([x : of V], of R),
             a : Bind([s : of T, u : of T], of R),
             l : Bind([b : Bind([x : of V], of T)], of R)],  of R)
```

leaves the rank at 4 — `R` binds `𝟙`, so it contributes 1 and `l` still dominates
at 3 — while adding a failure of clause (i). That `rank` does not move is the
point: it is blind to boundaries.

It stays consistent, unlike the impredicative System F slot
`all : Bind([F : Bind([X : sort], sort)], sort)`, which has no models over any
base. The difference is where the large product lands. There it must *be* a sort,
hence `𝒰₀`-small, and it is not. Here the boundary is `El` of a **bound** `R`, so
the product over `𝒰` is never packaged as a sort; each `El S` is small and a
section picks one element per `S`. Lemma 1.3.1 is untouched, and the standard
model still works, `case_S` being copairing with the inverse of the structure map,
which never inspects `S`.

What is lost is the intended meaning. The eliminator of an initial algebra is
*parametric*; the slot asks only for an element of `El S` for each `S`, natural in
the base. `𝒰` is not a category in `PSh(𝒞)`, so there is no naturality in `S` to
demand, and `𝒫` cannot impose it. The polymorphic slot therefore admits models
whose `case` behaves incomparably at different result types.

`R` is kept declared for an argumentative reason rather than a mathematical one.
With `R` declared the theory fails (ii) and nothing else, so **nesting** is
isolated as the sole cause — 5.2's observation that the same telescope is `𝒫`-free
in `lam` and not in `case`. The polymorphic variant fails (i) as well, and a
reader could then attribute the separation to the `sort` entry rather than to the
nesting.

---

---

## 2. Brouwer ordinals

The same phenomenon without the β-tension of §1.4.1: `O` is a datatype, not
syntax, so its constructors are disjoint by construction.

```text
O  : sort
oz : of O
os : Bind([a : of O], of O)
ol : Bind([f : Bind([n : of Nat], of O)], of O)                      rank 3

rec : Bind([ z : of R,
             s : Bind([a : of O, r : of R], of R),
             l : Bind([f : Bind([n : of Nat], of O),
                       g : Bind([n : of Nat], of R)], of R),
             a : of O ],  of R)                                      rank 4
+ the three recursion equations
```

`l` binds a rank-2 telescope, contributing 3, so `Θ_rec` has rank 3 and `rec` has
rank 4. Every entry is `of`-boundaried, so it fails **(ii) alone**.

**What must be reified, and why it cannot be.** Not `[n : of Nat]` — that is
representable in any reasonable base. The telescope reification must consume is
`l`'s binding,

```text
Θ_l = [ f : Bind([n : of Nat], of O),  g : Bind([n : of Nat], of R) ]
⟦Θ_l⟧ = (Nat ⇒ O) × (Nat ⇒ R)
```

and representability of that means the base admits a context extension by a
**function**, which a first-order context category does not have. Over `𝔽^op`-style
bases the cardinality count of §1.3 applies verbatim. `[open]`

**Why it is convincing.** The intended reading is the non-SOGAT one — `ol` really
does take an `ℕ`-indexed sequence and `rec` really does consume one; nothing is a
formalization choice. It is consistent, existing in any topos with `W`-types. And
it explains a line the subject already draws: infinitely-branching `W`-types are
exactly where inductive types stop being first-order, finitely-branching ones
staying at rank 3.

The family is large — infinitely-branching trees, `W`-types over an infinite
branching family, coinductive streams with an infinitary destructor, and the
eliminator of an inductive-recursive universe, whose `π` branch binds
`[x : of (T a)]` twice over and is likewise rank 4.

---

## 3. Large elimination

The universe example, and it fails **(i)** rather than (ii).

```text
Nat : sort,  zero : of Nat,  succ : Bind([n : of Nat], of Nat)

elim : Bind([ Z : sort,
              S : Bind([n : of Nat, X : sort], sort),
              n : of Nat ],  sort)                                   rank 3

eq (elim Z S zero)     Z
eq (elim Z S (succ n)) (S n (elim Z S n))
```

`Z : sort` is an entry of `elim`'s binding and `X : sort` an entry of `S`'s, so
(i) fails twice. The equations are legal: `eq` relates *expressions*, and a
`sort`-boundaried expression is one.

This is **recursion on `Nat` into the universe** — what gives `Vec n A`, and the
classical dividing line between predicative systems and those with large
elimination. It is consistent: at `Nat = ℕ` the interpretation iterates `S` from
`Z`. `[routine]`

**Why it is not merely Russell against Tarski.** Its Tarski shadow — recursion
into a *declared* sort `ty` — is `of`-only, hence a SOGAT, and is strictly weaker:
a declared universe need not contain all sorts, so recursion into `ty` builds only
types inside that universe, whereas recursion into `sort` builds arbitrary sorts.
The two readings are not notational variants of one theory.

---

## 4. Conditional operations and quasi-identities

A third flavour, and the only one that is about logic rather than binding. It
fails **(i)** through an `eq` entry, and it needs no higher-order structure at all.

Since `⟦eq l r⟧ = Eq(⟦l⟧,⟦r⟧)` is a subterminal, a binding carrying an `eq` entry
interprets as a **subobject**: the operation is defined on an equalizer.

```text
cancel : Bind([a : of M, b : of M, c : of M,
               p : eq (mul a b) (mul a c)],   eq b c)              rank 2

comp   : Bind([f : of A, g : of A, p : eq (cod f) (dom g)], of A)  rank 2
```

Every entry binds `𝟙`, so `Θ` has rank 1 and each slot has rank 2 — the lowest at
which anything can sit inside a binding at all.

**Why `ToS⁺` cannot.** `Π`'s domain must be a sort code `Tm U`, and `Eq l r : Ty`
is not one. So a hypothesis that is an *equation* has nowhere to go, and neither
quasi-identities nor equationally-domained partial operations are `ToS⁺`
signatures.

**The examples are classical.** Cancellative monoids and semigroups, torsion-free
groups, and Freyd's one-sorted categories, where composition is defined only when
`cod f = dom g`. The general shape is the Horn fragment: implications whose
premises are equations. Conditions needing `≠`, `∨` or `∃` — fields, integral
domains, local rings — are *not* expressible, since `Bd` has no such formers.

**The caveat, which is sharper here than elsewhere.** `[open]` Each of these
theories has a familiar alternative presentation that *is* a SOGAT: categories via
a dependent `Hom : Bind([a : of Ob, b : of Ob], sort)`, with `comp` total. If the
two presentations have equivalent categories of models — which for categories they
plainly do — then this flavour exhibits **presentation differences, not
separations**, and shows something worth knowing:

> Definition 1.1 is a property of a *presentation*, not of a theory. One theory may
> have both a SOGAT presentation and a non-SOGAT one.

That is consistent with, and reinforces, §6: failing Definition 1.1 is not the
same as having no first-order presentation. Whether *every* quasi-identity can be
re-presented this way is the open question. The encoding must force a dependent
sort to be *exactly* the equalizer, and a GAT axiom is an equation in a context of
variables, which gives one implication and not its converse — so it is not obvious
that it always can.

---

## 5. What is *not* an example

Worth recording, since the nearest neighbours of §§2–3 are all SOGATs.

```text
U : Bind([n : of Nat], sort)         a universe HIERARCHY                  SOGAT
Fin : Bind([n : of Nat], sort)       an indexed family of sorts            SOGAT
lift : Bind([n : of Nat,
             A : of (U n)], of (U (succ n)))                              SOGAT
ol, os, oz                           the ordinal CONSTRUCTORS              SOGAT
```

Each has `of`-boundaried bindings and rank ≤ 3. `Fin` and `U` are exactly MLTT's
`Tm : Ty → U⁺` pattern, `Fin : Π Nat (λ_. U⁺)` in `ToS⁺`. Note also that
"`Fin n` has exactly `n` elements" is **not expressible** — the framework has no
cardinality — so what pushes `Fin` past the line is its *eliminator*, whose motive
is `sort`-valued, not `Fin` itself.

§10 revisits the hierarchy: the bare family `U` is a SOGAT, but the *Russell*
equation `El (U n) = Ty n` is a sort equation, and it forces `Ty ∈ 𝒫`.

`𝒫` does not separate any of these. Demanding `[n : of Nat] ∈ 𝒫` forces
`Nat ≅ よR` by the terminal-base lemma, so at `𝒞 = 1` it collapses `Nat` to a
singleton and destroys the intended model `Nat = ℕ`, while over a syntactic base
it holds automatically. That is `sogats.md` §3.1, not a separation.

---

## 6. Status

```text
§1  λ-syntax with case    rank 4, fails (ii)     model verified, V ⇒ T not loc. rep.  [proved]
§2  Brouwer ordinals      rank 4, fails (ii)     rank arithmetic [proved];
                                                 Θ_l non-representability            [open]
§3  large elimination     rank 3, fails (i)      consistency                         [routine]
§4  quasi-identities      rank 2, fails (i)      rank arithmetic [proved];
                                                 whether it separates at all         [open]
```

The three flavours, side by side:

```text
§1, §2   consuming a binder        fails (ii)   not a formalization choice
§3       Russell quantification    fails (i)    strictly stronger than its Tarski shadow
§4       Horn premises             fails (i)    about logic, not binding; rank 2
```

In every case, failing Definition 1.1 says the theory is not second-order by a
criterion built to be *sufficient* for SOGATs, never proved to characterise them.
Turning any of these into a theorem needs `beyond-sogats-semantics.md`
Proposition 3.3, for which §1.5's non-finitary binder is the input.

---
---

# Part II. Internalized schemas

A different brief from Part I. Not "this fails Definition 1.1", but:

> a **single finite signature** for something that is elsewhere a declaration
> schema of an implementation, or a coding layer that changes the subject.

The comparison class here is proof assistants and specification frameworks
generally, not SOGATs. Where a rank or a `𝒫` is worth recording it is recorded,
but nothing below is organised around Definition 1.1.

**Notation.** `[Θ] β` for `Bind(Θ, β)`, slots written `x : A` for an `of`
boundary and `X : Sort` for a `sort` one, so a declaration reads

```text
pow : [n : Power, A : Ty] Ty
```

Part I still uses `Bind(−,−)`; the two are the same thing.

**Rank, recalled.** `rank 𝟙 = 0`, `rank Θ = max_z (rank (Θ.binding z) + 1)`, and
an entry with binding `Θ` contributes `rank Θ + 1`. So

```text
flat binding                          contributes 2
a slot that binds                     contributes 3
a slot whose binding has a binder     contributes 4
```

---

## 7. The reification fork

A declared sort and the ambient `Sort` differ in exactly one way, and it decides
every design below.

```text
                        storable in a declared sort?   bindable over?   quantifiable?
A : Ty     (declared)             yes                       yes             yes
A : Sort   (ambient)              NO                        yes             yes
```

`Ty` is `𝒰₀`-small, so a list of `Ty`s is a sort. The ambient `Sort` is not:
`⟦.sort⟧_Γ = !^* 𝒰` (semantics.md 1.3), and `𝒰` classifies the small dependent
presheaves, so it is not itself small.

Both sides of the fork are **writable**, and that is the point — the framework
can state the bad one and refute it.

**7.1 Proposition.** The signature

```text
Ty     : Sort
Schema : Sort
nil    : Schema
El     : [S : Schema] Sort
cons   : [A : Sort, S : Schema] Schema
_      : [A : Sort] eq (El (cons A nil)) A
```

is well formed and has **no models over any base `𝒞`**. `[proved]`

*Well-formedness.* The last entry has an `eq` boundary, which `Wf_bd.eq`
(`Typing/Rules.lean:83`) admits once `boundaryOf l ≈ boundaryOf r`. Here both
sides are sort-expressions, so both boundaries are `.sort`. Equations **between
sorts** are therefore legal; this is used again in §10 and §11.

*Proof.* Let `Γ` be an ambient and write `X = J Γ`. Interpreting the entries:
`⟦cons⟧` is a section over `X` of `Π_{A : 𝒰} ⟦Schema⟧`, and the equation says
`⟦El⟧ ∘ ⟦cons⟧(−, nil) = id` on `𝒰(X)`. So

```text
𝒰(X)  ↣  (El ⟦Schema⟧)(X)
```

is a split mono, exhibiting `𝒰` as a retract of a **small** dependent presheaf.
At `𝒞 = 1`, `Γ = 𝟙` this reads: an injection of the `𝒰₀`-small sets into a
`𝒰₀`-small set. ∎

**7.2 Remark.** So *the necessity of codes is a theorem here, not a convention.*
The `Desc`/`El` layer that `Ty` represents is forced, and the framework says by
how much: `Ty` may be stored, `Sort` may only be bound over and quantified.
GATs and SOGATs cannot state 7.1 at all — `A : Sort` is not a legal argument
position for them, so the question does not arise.

**7.3 Remark.** What survives on the ambient side is still substantial. A slot
`A : Sort` in a binding is a genuine universal quantification over sorts, so
`absurd : [A : Sort, x : ⊥] A` — ex falso into an arbitrary sort — is one entry
at rank 2. Reappears in §10.

---

## 8. Inductive-type schemas, internalized

The target: one signature in which `data` is an **operation**, its argument a
term denoting a schema. In Agda, Coq and Lean `data` is a declaration schema of
the implementation — infinitely many rules, external to any theory, with no
notion of model.

### 8.1 The signature

`S` is successor throughout; `s` ranges over `Sig`.

```text
-- (a) extrinsic naturals, with their index sorts
Power  : Sort                                                               1
Z      : Power                                                              1
S      : [n : Power] Power                                                  2
Fin    : [n : Power] Sort                                                   2
fz     : [n : Power] Fin (S n)                                              2
fs     : [n : Power, i : Fin n] Fin (S n)                                   2

-- (b) a universe of codes
Ty     : Sort                                                               1
El     : [A : Ty] Sort                                                      2

-- (c) powers
pow    : [n : Power, A : Ty] Ty                                             2
proj   : [n : Power, A : Ty, t : El (pow n A), i : Fin n] El A              2
tab    : [n : Power, A : Ty, f : [i : Fin n] El A] El (pow n A)             3
         proj (tab f) i = f i          tab ([i] proj t i) = t

-- (d) signatures, internally:  Sig = List Power   (Ivan's "List Nat")
Sig    : Sort                                                               1
nil    : Sig                                                                1
cons   : [n : Power, s : Sig] Sig                                           2
Op     : [s : Sig] Sort                                                     2
here   : [n : Power, s : Sig] Op (cons n s)                                 2
there  : [n : Power, s : Sig, o : Op s] Op (cons n s)                       2
ar     : [s : Sig, o : Op s] Power                                          2
         ar (cons n s) here = n        ar (cons n s) (there o) = ar s o

-- (e) the `data` keyword
data   : [s : Sig] Ty                                                       2
constr : [s : Sig, o : Op s, t : El (pow (ar s o) (data s))] El (data s)    2
ind    : [ s : Sig,
           P : [x : El (data s)] Sort,
           e : [ o : Op s,
                 t : El (pow (ar s o) (data s)),
                 h : [i : Fin (ar s o)] P (proj t i) ] P (constr s o t),
           x : El (data s) ] P x                                            4
         ind s P e (constr s o t) = e o t ([i] ind s P e (proj t i))        4
```

**8.1.1 Remark (why `tab`).** With list-style `⟨⟩`/`∷` constructors only —
rank 2 — nothing forces `pow n A` to have any elements at a non-standard `n`.
`tab`/`proj` as a bijection makes `pow n A` the exponential `(El A)^{Fin n}` at
every `n`. The naturals stay extrinsic, but coherently so: what the model does
at non-standard `n` is determined, it is just not determined to be finite.

### 8.2 Internalizing the arity costs exactly one rank

Compare a **fixed** finitary datatype:

```text
ℕ-ind : [ P : [n : Nat] Sort, z : P Z,
          s : [n : Nat, p : P n] P (S n), n : Nat ] P n                     3
```

`s`'s binding `[n, p]` is flat, so `s` contributes 2 and `rank Θ = 2`.

In `ind` of 8.1(e) the induction hypothesis `h` **must** be a binder: with
`ar s o` a variable, the components of `t` are only reachable through `Fin`. So
`h` contributes 2, `e`'s binding has rank 2, `e` contributes 3, `rank Θ_ind = 3`,
and `ind` is rank 4. `[proved]`

> **Every fixed finitary inductive type has a rank-3 eliminator. One `data`
> operation covering all of them at once has a rank-4 one. Internalizing the
> arity costs exactly one rank.**

This is the *same* mechanism as §2, reached by a different road. There, `lim`'s
argument is already infinitary, so `g : [n : Nat] P (f n)` is forced to be a
binder. Here every individual constructor is finitary and the binder appears
only because the arity is a variable. One reason for both:

> the induction hypothesis inherits the shape of the constructor argument.

`ind` also carries a `sort`-boundaried slot `P` inside a binding, so it fails
Part I's (i) as well as (ii). `constr` and `data` themselves stay at rank 2.

### 8.3 The natural `𝒫`

`𝒫` only ever *constrains* — its members must be locally representable
(semantics.md Def 1.1) — so a larger `𝒫` means a stronger theory with fewer
models. Take the smallest one that makes the binders mean what is intended. The
criterion is uniform:

> Put a sort family in `𝒫` **iff** "a term with a free variable of that sort"
> should be a judgement of the object theory.

That is exactly the object-level / schema-level divide:

```text
𝒫 = { El, Fin }                object-level: types, and their index sorts
∉ 𝒫 : Power, Ty, Sig, Op       schema-level: metalanguage data
```

`Sig ∈ 𝒫` would mean models have contexts extended by a **variable signature** —
an object-theory term with a free signature variable. Not intended, and not
needed: nothing in the signature binds over `Sig`.

**Where it bites.** By `sogats.md` §3.5, `𝒫` is invisible where a `Π` is merely
sectioned and visible where it is evaluated — i.e. at a binding **nested** inside
another. Two places here:

```text
tab   rank 3   f's domain Fin n is evaluated when Θ_tab is formed
ind   rank 4   h's domain Fin (ar s o) is evaluated inside e's binding
               P's domain El (data s) is evaluated when Θ_ind is formed
```

With `Fin ∈ 𝒫`, `[i : Fin n] El A` is `(El A)(I ⊲ Fin n)` and `h` really is
"`P` holds at each component". Without it, it is the presheaf exponential, `pow`
is not the `n`-th power, and `h` is an unrelated internal function.

**8.3.1 Remark (`⊲` respects `Σ`, not `+`).** Extension by `Fin n` is extension
by **one** variable ranging over an `n`-element sort, not by `n` variables:

```text
𝒞(J, I ⊲ Σ_A B) ≅ Σ (f : 𝒞(J,I)). Σ (a : A J f). B J (f,a) ≅ 𝒞(J, I ⊲ A ⊲ B)   ✓
𝒞(J, I ⊲ (A + B)) ≅ Σ f. (A J + B J)                     ≠ 𝒞(J, I ⊲ A ⊲ B)      ✗
```

So `I ⊲ Fin (S^k Z)` is *not* the `k`-fold extension. §9 needs `n` genuine
variables and therefore cannot reuse `Fin`; it declares its own family with
`Ctx (S n) ≅ Ctx n × V`, and the left-hand identity above is what makes that
work. `[proved]`

### 8.4 What this buys, and what it does not

**Buys.** `s` is a term: one may quantify over it, state a lemma for all
schemas at once, and — the part no proof assistant offers — the signature has a
class of models, so "a category with a `data` former closed under all schemas"
is a definition rather than a description of an implementation.

**Does not buy.** Every individual term above is writable in Agda; the
`Desc`/`El` presentation is a standard exercise. The difference is whether the
schema is a *theorem of the implementation* or an *axiom of a theory one can
then model*, and §7.1 says the coding layer is not optional either way.

**8.4.1 Remark (higher inductive types).** `eq` in this framework is strict, so
a path constructor `loop : eq base base` is just an equation and the HIT
collapses. Genuine HITs need `Id : [A : Ty, x : El A, y : El A] Ty` declared and
path constructors valued in `El (Id …)`; `Sig` then grows a second `cons` for
path arities, and `ind` a second branch. Sketch only. `[open]`

**8.4.2 Remark (the initial model).** Expected: `Power = ℕ`, `Sig = List ℕ`, and
`El (data s)` the initial algebra of `X ↦ Σ_{o : Op s} X^{Fin (ar s o)}`.
`Fin ∈ 𝒫` is what makes that functor preserve the colimits the construction
needs, since a locally representable `A` makes `A ⇒ −` a right adjoint computed
pointwise, hence cocontinuous. Not verified. `[open]`

---

## 9. Binding signatures, internalized

Fiore–Plotkin–Turi take a binding signature as **external** data: a set of
operations with externally given arities `(n_1, …, n_k)`, and one initial algebra
in `Set^𝔽` per signature. Internalizing it is the same move as §8, one level up:
the arity now says how many variables each argument **binds**.

### 9.1 The obstacle, and the fix

An `n`-fold binding `[x_1 : V, …, x_n : V]` cannot be written for a variable `n` —
bindings are static telescopes. So declare the contexts as a sort family and make
them representable:

```text
⊤      : Sort,  tt : ⊤,  η                                                  1
V      : Sort                                                               1
Ctx    : [n : Power] Sort                                                   2
_      : eq (Ctx Z) ⊤                                                       1
ext    : [n : Power, v : Ctx n, x : V] Ctx (S n)                            2
p      : [n : Power, v : Ctx (S n)] Ctx n                                   2
q      : [n : Power, v : Ctx (S n)] V                                       2
+ β/η, making  Ctx (S n) ≅ Ctx n × V
```

With `𝒫 = { V, Ctx }`, 8.3.1 gives `I ⊲ Ctx (S n) ≅ I ⊲ Ctx n ⊲ V`, so at a
standard `n` the sort `Ctx n` is extension by `n` genuine variables and
`[v : Ctx n] Tm` is "a term with `n` extra free variables" — the FPT shift `δ^n`,
with `n` a term. `[routine]`

### 9.2 The signature

```text
Ar     : Sort,  nilₐ : Ar,  consₐ : [n : Power, a : Ar] Ar                  2
Sig    : Sort,  nilₛ : Sig, consₛ : [a : Ar, s : Sig] Sig                   2
Op     : [s : Sig] Sort,  here, there                                       2
arity  : [s : Sig, o : Op s] Ar                                             2

Tm     : Sort                                                               1
var    : [x : V] Tm                                                         2
Args   : [a : Ar] Sort                                                      2
nilᵃ   : Args nilₐ                                                          1
consᵃ  : [n : Power, a : Ar,
          t : [v : Ctx n] Tm, as : Args a] Args (consₐ n a)                 3
op     : [s : Sig, o : Op s, as : Args (arity s o)] Tm                      2
```

Rank 3, and `consᵃ` is the only entry that reaches it. One signature whose
initial model is the free abstract syntax with binding over a **variable**
binding signature. `[open]` — that the initial model is FPT's is expected, not
checked.

### 9.3 The recursor, again at rank 4

```text
Idx    : [a : Ar] Sort                         positions of an arity
at     : [a : Ar, i : Idx a] Power             how many variables position i binds
sel    : [a : Ar, as : Args a, i : Idx a, v : Ctx (at a i)] Tm

Tm-rec : [ P : [t : Tm] Sort,
           w : [x : V] P (var x),
           u : [ s : Sig, o : Op s, as : Args (arity s o),
                 h : [i : Idx (arity s o), v : Ctx (at (arity s o) i)]
                       P (sel as i v) ] P (op s o as),
           t : Tm ] P t                                                     4
```

`h`'s binding `[i, v]` is flat, so `h` contributes 2, `u`'s binding has rank 2,
`u` contributes 3, `Tm-rec` is rank 4. Same accounting as 8.2, and the induction
hypothesis is now indexed by *both* the argument position and the variables that
position binds — which is exactly what an initial-algebra recursion in `Set^𝔽`
needs. `[proved]` for the rank; the equations are a sketch.

---

## 10. A universe hierarchy à la Russell

```text
Power, Z, S                                                       as in §8
Ty   : [n : Power] Sort                                                     2
El   : [n : Power, A : Ty n] Sort                                           2
U    : [n : Power] Ty (S n)                                                 2
_    : [n : Power] eq (El (S n) (U n)) (Ty n)                               2
lift : [n : Power, A : Ty n] Ty (S n)                                       2
_    : [n : Power, A : Ty n] eq (El (S n) (lift n A)) (El n A)              2
Pi   : [n : Power, A : Ty n, B : [a : El n A] Ty n] Ty n                    3
```

Two of these are equations **between sorts**, legal by 7.1's well-formedness
note, and both are things a Tarski-style presentation gets only up to a
coercion:

```text
El (S n) (U n)      = Ty n        the universe IS the sort of types, on the nose
El (S n) (lift n A) = El n A      cumulativity, on the nose
```

**10.1 Remark (Russell forces `Ty ∈ 𝒫`).** `El ∈ 𝒫` means every instance
`El n A` is locally representable. The first equation makes `Ty n` such an
instance, so `Ty ∈ 𝒫` follows. Semantically that is precisely the difference
between Russell and Tarski: models must have contexts extended by a **type
variable**. Consistent in the syntactic model of MLTT with Russell universes, by
construction. `[routine]`

**10.2 Remark (extrinsic levels are not well-founded).** Nothing in the above
forbids a model with `S n = n` for some `n`. There `U n : Ty (S n) = Ty n` and
`El n (U n) = Ty n`: a universe containing a code for itself, and the hierarchy
collapses. Two repairs, and the framework prices both:

```text
assert   nz : [n : Power, p : Id (S n) n] ⊥                                 2
derive   Power-induction with a `sort` motive                               3
         + absurd : [A : Sort, x : ⊥] A                    (§7.3)           2
```

So: **internalizing the levels makes their well-foundedness an explicit
obligation**, discharged at rank 2 as an axiom or rank 3 as a theorem. Exactly
parallel to 8.4.2, where internalizing the arity made the *finiteness* of `Fin n`
an obligation rather than a given.

---

## 11. Telescopes, and induction–recursion

The framework internalizing its own `dTel`, one level down. `Θ : Tel` below is a
**term** of a declared sort, not a meta-level telescope; the ambiguity is the
point.

```text
Sg   : [X : Sort, Y : [x : X] Sort] Sort                                    3
       pair, fst, snd, β, η
Ty   : Sort,  El : [A : Ty] Sort                                            2

Tel  : Sort                                                                 1
Env  : [Θ : Tel] Sort                                                       2
nilₜ : Tel                                                                  1
ext  : [Θ : Tel, A : [γ : Env Θ] Ty] Tel                                    3
_    : eq (Env nilₜ) ⊤                                                      1
_    : [Θ : Tel, A : [γ : Env Θ] Ty]
         eq (Env (ext Θ A)) (Sg (Env Θ) ([γ] El (A γ)))                     3

Pi   : [Θ : Tel, A : [γ : Env Θ] Ty] Ty                                     3
lam  : [Θ : Tel, A : [γ : Env Θ] Ty, f : [γ : Env Θ] El (A γ)] El (Pi Θ A)  3
app  : [Θ : Tel, A : [γ : Env Θ] Ty, g : El (Pi Θ A), γ : Env Θ] El (A γ)   2
+ β/η
```

Rank 3 throughout. `Pi Θ A` is the product over a telescope **given by a term**;
in Agda, Coq and Lean telescopes exist only in the metalanguage.

**11.1 Remark (this is an induction–recursion).** `Tel` is generated by `nilₜ`
and `ext`, and `Env` is *computed* by recursion on that generation — the two
sort equations are the recursive clauses, and `ext`'s own argument `A` mentions
`Env Θ`. So `Tel`/`Env` is a genuine inductive–recursive definition, stated with
two entries and two equations, no `Desc`, no coding, and no dedicated IR support
in the framework. What the framework does *not* do is construct it: it posits
`Tel` and `Env` and asks for a model. `[open]`

**11.2 Remark (`𝒫`, and why it is coherent).** `𝒫 = { El, Env }`, `Tel ∉ 𝒫`.
The second sort equation then demands that local representability be closed
under `Sg` and contain `⊤`, which is 8.3.1's left-hand identity — so
`I ⊲ Env (ext Θ A) ≅ I ⊲ Env Θ ⊲ El (A −)`, and extension by an internal
telescope is iterated extension by its components. `[proved]`

**11.3 Remark (`Sg` is a §7.3 entry).** `Sg : [X : Sort, Y : [x : X] Sort] Sort`
has two `sort`-boundaried slots inside a binding: `Σ`-types **à la Russell**,
over arbitrary sorts, with no `Ty`/`El` layer. Together with §10 this is MLTT
written with the ambient `Sort` playing the role that `Ty` plays in a SOGAT
presentation — available exactly to the extent §7.1 permits, i.e. as long as
nothing tries to store a sort.

---

## 12. Status, Part II

```text
§7   the reification fork      no models, any base                          [proved]
     well-formedness of sort equations (Rules.lean:83)                      [proved]
§8   data as an operation      rank arithmetic, 2 → 4                       [proved]
     𝒫 = {El, Fin}, where it bites                                          [proved]
     ⊲ respects Σ not +                                                     [proved]
     initial model = free Σ-algebra                                         [open]
     HIT extension                                                          [open]
§9   binding signatures        rank 3 syntax, rank 4 recursor               [proved]
     Ctx (S n) ≅ Ctx n × V gives the FPT shift                              [routine]
     initial model = FPT free syntax                                        [open]
§10  Russell hierarchy         El ∈ 𝒫 forces Ty ∈ 𝒫                         [routine]
     collapse at S n = n, and its price                                     [proved]
§11  internalized telescopes   rank 3; 𝒫-coherence via Σ-closure            [proved]
     Tel/Env is an induction-recursion                                      [open]
```

One theme across all four:

> Internalizing a schema turns a property the metalanguage supplied for free
> into an explicit obligation of the theory — finiteness in §8, the shift in §9,
> well-foundedness in §10, the recursion in §11 — and the framework prices each
> one in ranks and in `𝒫`.
