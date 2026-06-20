# The Mathematical Content of `diamondAt`

## The Point

The theorem `diamondAt` is an interchange law for hereditary substitution. It
says that the following two operations commute:

1. replace variables from one context $D$ by expressions over $D'$;
2. replace variables from another context $S$ by expressions over $S'$.

There is one important subtlety. The fillers used to replace the $S$-variables
may themselves contain variables from $D$. Therefore, if we first substitute
$D$-variables, then the $S$-fillers must also be transformed by that same
substitution. The theorem says that this is the only correction needed.

## Notation

We write $𝓔(Γ)$ for expressions in context $Γ$. If
$α$ is an arity, then

$$
Γ ◁ α
$$

means the context $Γ$ extended by one binder of arity $α$. This is
written $Γ :: α$ in Lean.

The operation $⋈$ appends telescopes. We use the following names for the
contexts appearing in the theorem:

$$
P = pre,
D = dom,
D' = cod,
T = τ,
S = src,
S' = dst.
$$

The list $υ$ of already-opened binders gives a telescope

$$
U = Tele(υ).
$$

In Lean, $U$ is $Tele.ofList υ$.

The expression to which the theorem applies lives in the context

$$
((((P ⋈ D) ⋈ T) ⋈ S) ⋈ U).
$$

Thus it may mention variables from five regions:

$$
P, D, T, S, U.
$$

An argument family can be viewed as a singleton substitution. If `A` is an
argument family for a head of arity `β`, write

$$
A♯ : ⟨β⟩ ⇝ Ω
$$

for the substitution defined by

$$
A♯(here(j)) = Aⱼ.
$$

This is Lean's `Subst.fromArgs ... A`. The β-like step is then not a new
primitive operation: it is ordinary substitution action by `A♯`. Thus

$$
(A♯)_Ξ(b)
$$

means: act on the filler `b` by the singleton substitution generated from the
argument family `A`, at passive depth `Ξ`.

## The Two Substitutions

The first substitution is

$$
σ : D ⇝ P ⋈ D'.
$$

This means that for every variable $z : D ∋ β$, we have a filler

$$
σ(z) ∈ 𝓔((P ⋈ D') ◁ β).
$$

It replaces $D$-variables while preserving the prefix $P$.

The second substitution is

$$
κ : S ⇝ ((P ⋈ D) ⋈ T) ⋈ S'.
$$

Thus for every $x : S ∋ β$,

$$
κ(x)
∈
𝓔(((((P ⋈ D) ⋈ T) ⋈ S') ◁ β)).
$$

This replaces $S$-variables by expressions that still live over $D$. So
$κ$ is a substitution before the change of target context induced by
$σ$.

## Action At A Passive Depth

If $A$ is a passive telescope, then $σ$ acts at depth $A$ as a map

$$
σ_A :
𝓔((P ⋈ D) ⋈ A)
→
𝓔((P ⋈ D') ⋈ A).
$$

The word "passive" means that variables from $A$ are not substituted. They are
merely carried along. Only variables from $D$ are active for $σ$.

Similarly, $κ$ acts at passive depth $U$ as a map

$$
κ_U :
𝓔(((((P ⋈ D) ⋈ T) ⋈ S) ⋈ U))
→
𝓔(((((P ⋈ D) ⋈ T) ⋈ S') ⋈ U)).
$$

Only variables from $S$ are active for $κ$; everything else is passive.

## Postcomposition Of A Substitution

Since the fillers of $κ$ may contain $D$-variables, applying $σ$ to an
expression also transforms the substitution $κ$. We write this
postcomposition as

$$
σ ▷ κ :
S ⇝ ((P ⋈ D') ⋈ T) ⋈ S'.
$$

It is defined pointwise by

$$
(σ ▷ κ)(x)
=
σ_{T ⋈ S' ◁ β}(κ(x)),
where x : S ∋ β.
$$

The passive depth is $T ⋈ S' ◁ β$, because the
filler $κ(x)$ is an expression over

$$
((P ⋈ D) ⋈ (T ⋈ S' ◁ β)).
$$

After $σ$ acts, this becomes an expression over

$$
((P ⋈ D') ⋈ (T ⋈ S' ◁ β)),
$$

which is exactly the required type of a filler for $x$ in the transformed
substitution.

## The Theorem As An Equation

Let

$$
e ∈ 𝓔(((((P ⋈ D) ⋈ T) ⋈ S) ⋈ U)).
$$

Then `diamondAt` says:

$$
(σ ▷ κ)_U
(
  σ_{(T ⋈ S) ⋈ U}(e)
)
=
σ_{(T ⋈ S') ⋈ U}
(
  κ_U(e)
).
$$

This is the clean mathematical statement. The left-hand side first applies
$σ$ to $e$, then substitutes the remaining $S$-variables using the
postcomposition $σ ▷ κ$. The right-hand side
first substitutes the $S$-variables using $κ$, then applies $σ$.

## The Same Equation As A Square

The theorem says that the following square commutes:

```text
𝓔(((((P ⋈ D)  ⋈ T) ⋈ S)  ⋈ U))
  -- σ_(T ⋈ S) ⋈ U -->
𝓔(((((P ⋈ D') ⋈ T) ⋈ S)  ⋈ U))

        | κ_U                         | (σ ▷ κ)_U
        v                             v

𝓔(((((P ⋈ D)  ⋈ T) ⋈ S') ⋈ U))
  -- σ_(T ⋈ S') ⋈ U -->
𝓔(((((P ⋈ D') ⋈ T) ⋈ S') ⋈ U))
```

The top arrow changes $D$ into $D'$. The left arrow changes $S$ into $S'$. The
bottom arrow changes $D$ into $D'$ after $S$ has already been changed into
$S'$. The right arrow changes $S$ into $S'$ after the fillers for $S$ have
themselves been pushed forward along $σ$.

## Why The Theorem Is Not Trivial

If the fillers of $κ$ did not contain variables from $D$, the theorem
would be close to ordinary commutation of independent substitutions. But here
the fillers of $κ$ are expressions over

$$
((P ⋈ D) ⋈ T) ⋈ S',
$$

so they may contain $D$-variables. Therefore substituting $D$-variables before
substituting $S$-variables changes the $S$-fillers themselves.

The postcomposition $σ ▷ κ$ is precisely the
bookkeeping that accounts for this dependency. The theorem says: the dependency
of $κ$ on $D$ is handled pointwise by $σ$.

## The Five Head Cases

The context of $e$ decomposes into five regions:

$$
((((P ⋈ D) ⋈ T) ⋈ S) ⋈ U).
$$

Consequently, the head variable of an application in $e$ belongs to exactly one
of:

$$
U, S, T, D, P.
$$

The proof of the theorem is a structural recursion on $e$, with a case split on
these five possibilities.

### Head In $U$

This is a local binder introduced by recursive descent. Neither substitution
acts on it. Both sides rebuild the same head and use the induction hypothesis
on all arguments.

More explicitly, suppose the expression has the form

$$
e = ap(x_υ,a),
$$

where $x_υ : U ∋ β$ is the head variable and, for each binder
argument $j ∈ B(β)$, the expression $a(j)$ is the corresponding
subterm under the extra binder of arity $ar(j)$.

After unfolding the two routes in the diamond, both sides still have the same
head $x_υ$. What changes is only the family of arguments. For each
argument $j$, define

$$
Lⱼ =
(σ ▷ κ)_{U ◁ ar(j)}
(
  σ_{(T ⋈ S) ⋈ (U ◁ ar(j))}(a(j))
)
$$

and

$$
Rⱼ =
σ_{(T ⋈ S') ⋈ (U ◁ ar(j))}
(
  κ_{U ◁ ar(j)}(a(j))
).
$$

The induction hypothesis applied to the subterm $a(j)$ says precisely that

$$
Lⱼ = Rⱼ
$$

for every binder argument $j$. More precisely, for each $j$ we call the same
theorem with the same $P,D,D',T,S,S',σ,κ$, but with the
under-telescope enlarged from $U$ to

$$
U_j = U ◁ ar(j),
$$

and with expression $a(j)$. In Lean, using ASCII names for readability, this is
the recursive call:

```lean
diamondAt (upsilon := j.arity :: upsilon)
  sigma hTauSrc hTauDst srcTarget dstTarget kappa (args j)
```

Therefore the under case concludes by congruence of the application constructor
and function extensionality:

$$
ap(x_υ, j ↦ Lⱼ)
=
ap(x_υ, j ↦ Rⱼ).
$$

So the informal phrase "the under case is `ap(x_υ, j ↦ IHⱼ)`" means:
after both routes have been normalized to applications with the same head, the
desired equality is induced pointwise from the recursive equalities on the
argument family. In the Lean file, this argument is packaged by the lemma
`DiamondSite.underBranch`.

### Head In $S$

This is an active variable for $κ$. On the right side, $κ$ fires
immediately. On the left side, $σ$ first acts on the ambient expression,
and then the postcomposition $σ ▷ κ$ fires.
The two results are equal because $σ ▷ κ$ was
defined by applying $σ$ to the fillers of $κ$. This branch recursively
invokes the same theorem on the selected filler $κ(x)$.

More explicitly, suppose

$$
e = ap(xₛ,a),
where xₛ : S ∋ β.
$$

For this application, the branch goal is exactly

$$
(σ ▷ κ)_U
(
  σ_{(T⋈ S)⋈ U}
    (ap(xₛ,a))
)
=
σ_{(T⋈ S')⋈ U}
(
  κ_U(ap(xₛ,a))
).
$$

We now unfold both sides. First consider the left-hand side. The head $xₛ$ is
passive for $σ$, because $σ$ only replaces variables from $D$.
Therefore $σ$ preserves the head and acts on the arguments:

$$
σ_{(T ⋈ S)⋈ U}(ap(xₛ,a))
=
ap
(
  xₛ,
  j ↦
    σ_{(T⋈ S)⋈(U◁ar(j))}(a(j))
).
$$

Write

$$
Āⱼ =
σ_{(T⋈ S)⋈(U◁ar(j))}(a(j)).
$$

Then the previous equation says

$$
σ_{(T ⋈ S)⋈ U}(ap(xₛ,a))
=
ap(xₛ, j ↦ Āⱼ).
$$

Now apply $(σ ▷ κ)_U$. This substitution does act on $xₛ$, so it fires.
Firing means: take the filler selected by $xₛ$ and instantiate its binder
arguments by the transformed argument family. In the notation introduced above,
we get

$$
(σ ▷ κ)_U
(
  ap(xₛ, j ↦ Āⱼ)
)
=
(L♯)_∅((σ ▷ κ)(xₛ)),
$$

where

$$
Lⱼ =
(σ ▷ κ)_{U◁ar(j)}
(
  Āⱼ
).
$$

The notation `L♯` means the singleton substitution generated by this family
`j ↦ Lⱼ`.

By definition of postcomposition, the fired filler is

$$
(σ ▷ κ)(xₛ)
=
σ_{T⋈ S'◁β}(κ(xₛ)).
$$

Substituting that definition of the filler into the previous equation, the
left route has unfolded to

$$
(L♯)_∅(σ_{T⋈ S'◁β}(κ(xₛ))).
$$

Now unfold the right-hand side. Here $κ$ fires immediately at the head $xₛ$:

$$
κ_U(ap(xₛ,a))
=
(κᵦ)_∅(κ(xₛ)).
$$

Therefore the right route becomes

$$
σ_{(T⋈ S')⋈ U}
(
  (κᵦ)_∅(κ(xₛ))
).
$$

To compare these two normal forms, package the argument family as a singleton
substitution

$$
κᵦ : ⟨β⟩
⇝ ((P⋈ D)⋈ T⋈ S')⋈ U
$$

defined by

$$
κᵦ(here(j))
=
κ_{U◁ar(j)}(a(j)).
$$

At this point the left route is

$$
(L♯)_∅(σ_{T⋈ S'◁β}(κ(xₛ))),
$$

and the right route is

$$
σ_{(T⋈ S')⋈ U}
(
  (κᵦ)_∅(κ(xₛ))
).
$$

The recursive call that compares these is `diamondAt` applied to the selected
filler $κ(xₛ)$. Its parameters are

$$
Tnew  = T ⋈ S',
Snew  = ⟨β⟩,
S'new = U,
Unew  = ∅.
$$

The expression is $κ(xₛ)$. In Lean, this is the call:

```lean
diamondAt (tau := tau bowtie dst) (src := singleton beta)
  (dst := Tele.ofList upsilon) sigma
  (upsilon := []) ... kappaBeta (e := kappa xsrc)
```

where `kappaBeta` is the singleton substitution `κᵦ` above.

The recursive theorem says exactly that

$$
(R♯)_∅(σ_{T⋈ S'◁β}(κ(xₛ)))
=
σ_{(T⋈ S')⋈ U}
(
  (κᵦ)_∅(κ(xₛ))
).
$$

where

$$
Rⱼ =
σ_{(T⋈ S')⋈ U◁ar(j)}
(κ_{U◁ar(j)}(a(j))).
$$

Similarly, `R♯` is the singleton substitution generated by `j ↦ Rⱼ`.

The only remaining mismatch is that our unfolded left route contains $Lⱼ$, not
$Rⱼ$. But the recursive hypotheses already computed for the original arguments
$a(j)$ say precisely that

$$
Lⱼ = Rⱼ
$$

for every $j$. In the Lean proof, this pointwise replacement of singleton
filler families is the equality named `hSubst`; its only nonempty case is the
singleton slot $here(j)$, where it is exactly the argument recursive
hypothesis `hargs j`.

This recursive call is terminating because it decreases the source side of the
diamond: instead of proving the theorem for all of $S$, it proves it for the
single selected $S$-slot $xₛ$.

### Head In $T$

This head is passive for both substitutions. Both sides preserve it and recurse
on the arguments.

Concretely, suppose

$$
e = ap(x_T,a),
$$

where $x_T : T ∋ β$. This head lies in the ambient passive telescope
between the $D$-part and the $S$-part. It is not a variable that $σ$ may
replace, because $σ$ only acts on $D$. It is also not a variable that
$κ$ may replace, because $κ$ only acts on $S$. Thus both routes
through the diamond rebuild the same $T$-head.

For each binder argument $j ∈ B(β)$, set

$$
Lⱼ =
(σ ▷ κ)_{U ◁ ar(j)}
(
  σ_{(T ⋈ S) ⋈ (U ◁ ar(j))}(a(j))
)
$$

and

$$
Rⱼ =
σ_{(T ⋈ S') ⋈ (U ◁ ar(j))}
(
  κ_{U ◁ ar(j)}(a(j))
).
$$

The recursive hypothesis again gives $Lⱼ = Rⱼ$ for every $j$. The recursive
call is exactly the same one as in the $U$-case: for each argument $j$, we apply
the theorem to the subterm $a(j)$, leaving $σ,κ,T,S,S'$ and all
coherence data unchanged, and replacing the under-telescope $U$ by

$$
U_j = U ◁ ar(j).
$$

In Lean, again with ASCII names for readability, this is:

```lean
diamondAt (upsilon := j.arity :: upsilon)
  sigma hTauSrc hTauDst srcTarget dstTarget kappa (args j)
```

Therefore the $T$-case reduces to

$$
ap(x_T, j ↦ Lⱼ)
=
ap(x_T, j ↦ Rⱼ).
$$

The Lean proof is longer than this sentence because it must show that the
formal embeddings of the same $T$-head through
$(P ⋈ D) ⋈ (T ⋈ S)$ and
$(P ⋈ D) ⋈ (T ⋈ S')$ are the intended ones. Once this
reassociation bookkeeping is done, the branch is just congruence plus the
recursive equalities.

### Head In $D$

This is an active variable for $σ$. Firing $σ$ creates a one-binder
instantiation from the arguments of the application. This is the only branch
where the companion theorem for one-binder instantiation is needed.

### Head In $P$

This is part of the untouched prefix. Both substitutions preserve it and
recurse on the arguments.

Here an application has the form

$$
e = ap(x_P,a),
$$

with $x_P : P ∋ β$. The prefix $P$ is shared background context:
$σ$ preserves it while replacing only $D$-variables, and $κ$
preserves it while replacing only $S$-variables. Consequently the head $x_P$
survives unchanged along both sides of the square.

As before, for each binder argument $j$ we compare the two transformed subterms

$$
Lⱼ =
(σ ▷ κ)_{U ◁ ar(j)}
(
  σ_{(T ⋈ S) ⋈ (U ◁ ar(j))}(a(j))
),
,
Rⱼ =
σ_{(T ⋈ S') ⋈ (U ◁ ar(j))}
(
  κ_{U ◁ ar(j)}(a(j))
).
$$

The induction hypothesis gives $Lⱼ = Rⱼ$. Concretely, for each $j$ the
recursive call is the theorem applied to $a(j)$ at the enlarged passive
under-telescope

$$
U_j = U ◁ ar(j),
$$

with the same substitutions $σ$ and $κ$, the same ambient telescope
$T$, the same source and destination $S,S'$, and the same coherence witnesses.
In Lean, using ASCII names for readability, it is the same call:

```lean
diamondAt (upsilon := j.arity :: upsilon)
  sigma hTauSrc hTauDst srcTarget dstTarget kappa (args j)
```

Hence

$$
ap(x_P, j ↦ Lⱼ)
=
ap(x_P, j ↦ Rⱼ).
$$

The only formal work in this case is showing that the prefix injection for
$x_P$ is the same after passing through the source and destination
parenthesizations. Mathematically, nothing happens to the head.

## Why The Formal Statement Has Coherence Data

The mathematical equation above suppresses associativity bookkeeping for
$⋈$. Lean cannot suppress it completely. The formal theorem therefore
carries witnesses saying that the decompositions

$$
T ⋈ S
and
T ⋈ S'
$$

are proper and that injections into larger contexts compute with the intended
parenthesization. These witnesses do not change the mathematical content of the
theorem. They only ensure that the formal proof can recognize, for example,
that a head from $S$ remains a head from $S$ after it is embedded through

$$
(P ⋈ D) ⋈ (T ⋈ S).
$$

## Role In Substitution Composition

The public composition theorem says that acting by a composite substitution is
the same as acting by one substitution and then the other. The difficult case is
when the first substitution fires on an application head. Firing creates a fresh
one-binder instantiation, and the remaining substitution must commute past that
instantiation.

The theorem described here is the general interchange principle that makes that
step possible. In short: hereditary substitution respects substitution
composition.
