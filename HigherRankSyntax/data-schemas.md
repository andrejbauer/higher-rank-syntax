# The `data` schema as a higher-rank theory

A single finite signature `Ξ_data` that internalises the `data` / `inductive`
keyword for finitary single-sorted inductive types, completed from Andrej's
whiteboard sketch, together with its rank, its positivity, the extent to which it
is beyond SOGATs, and its place in the literature.

Companion to `beyond-sogats-examples.md` Part II §8, an earlier version of the same
example; §8 below lists where the two differ. The framework is
`positive-theories-and-initiality.md`, cited as *PT*.

Marks: `[paper]` argued here or in the cited note; `[routine]`; `[conjecture]`;
`[open]`; `[Lean]` formalized.

**Notation.** A slot is `y : [Θ] β`. `x : A` is an `of A` entry, `X : Sort` a `sort`
one, `eq l r` an equation boundary, and `(x) e` fills a binding. Implicit arguments
are suppressed when determined. The number after a slot is its rank contribution:
`rank [] = 0`, and an entry with binding `Θ` contributes `rank Θ + 1`.

---

## 0. Verdict

```text
rank Ξ_data = 4                                                         [paper]
not second-order (beyond-sogats-syntactic Def 1.1): (ii) and (iii) fail,
  and (i) as well with the optional ηind                                [paper]
positive (PT Def 3.3), so PT Thm 7.5 gives an initial model             [paper]
rank 3 after adding one sort G ≅ [i : Fin n] Tm (B i);
  the canonical map of models is surjective, not injective              [paper]
  the model categories are equivalent                                   [conjecture]
```

The natural presentation is rank 4, and every known rank-3 presentation names the
induction-hypothesis type, as a new sort or as a code in `Ty` or `Tys`. So
"beyond SOGATs" is established for the presentation. For the theory it is open
(§5.4).

---

## 1. The board

```text
…ℓ : [b : [x:Var] Tm] R] R       left edge: the l-branch of `case` (beyond-sogats-examples §1),
                                  one '[' cut off by the photo
…, P)                            left edge, cut off by the photo

Aⁿ                               [A, B, …, C]
Power : Sort                     Schema : Sort
z : Power                        Ty     : Sort
s : [n:Power] Power              nil    : Schema
                                 cons   : [A:Ty][S:Schema] Schema
Ty  : Sort                       prod   : Schema → Ty
pow : [n:Power][A:Ty] Ty         tuple
()  : [A:Ty] pow(z,A)            proj
cons: …        pow(sn,A)           ⋮
proj
──────────────────────────────────────────────────────────
Schema = "List Nat"
data   : Schema → Ty
Constr : [S:Schema] …
ind    :

data T =                         data tree =
  | T × T × … × T → T              | 1 → T
  |                                | T × T → T
  |
```

What this note changes or fills in:

- **Russell to Tarski.** `() : [A:Ty] pow(z,A)` uses elements of a type directly.
  Here the decoding `Tm : [A : Ty] Sort` is explicit. It is not called `El`,
  which is the HrS former of PT §1.1.
- **The two `Schema`s.**
  - The right column's `Schema` is a list of types; here it is called `Tys`.
  - The bottom one, "List Nat", is called `Sig`, because "schema" already names
    the generators of `Adm` (PT §3.1, `Theory.Schema`). `D` ranges over `Sig`.
- **`Constr`** is completed as `constr D o t`: a constructor name `o` of `D` and
  a tuple `t` of `ar D o` recursive arguments, which is `T × … × T → T`.
- **`proj`.**
  - For `Aⁿ` it becomes `hd` and `tl`, the two projections of
    `pow (s n) A ≅ A × pow n A`, together with the indexed `proj` that the
    induction hypothesis needs.
  - For `[A, …, C]`, `tuple` becomes `unit` and `pair`, and `proj` becomes `fst`
    and `snd`.
- **`ind`** is the part the board leaves open (§2.4).

---

## 2. The signature `Ξ_data`

`n ∷ R` abbreviates `consₛ n R`.

### 2.1 Powers (the board's `Aⁿ`)

```text
Power : Sort                                                                   1
z     : Power                                                                  1
s     : [n : Power] Power                                                      2
Ty    : Sort                                                                   1
Tm    : [A : Ty] Sort                                                          2
pow   : [n : Power, A : Ty] Ty                                                 2
()    : [A : Ty] Tm (pow z A)                                                  2
cons  : [n : Power, A : Ty, a : Tm A, v : Tm (pow n A)] Tm (pow (s n) A)       2
hd    : [n : Power, A : Ty, v : Tm (pow (s n) A)] Tm A                         2
tl    : [n : Power, A : Ty, v : Tm (pow (s n) A)] Tm (pow n A)                 2
_     : [n, A, a, v]                 eq (hd (cons a v)) a                      2
_     : [n, A, a, v]                 eq (tl (cons a v)) v                      2
_     : [A, v : Tm (pow z A)]        eq v ()                                   2
_     : [n, A, v : Tm (pow (s n) A)] eq v (cons (hd v) (tl v))                 2
```

### 2.2 Positions

```text
Fin   : [n : Power] Sort                                                       2
fz    : [n : Power] Fin (s n)                                                  2
fs    : [n : Power, i : Fin n] Fin (s n)                                       2
proj  : [n : Power, A : Ty, v : Tm (pow n A), i : Fin n] Tm A                  2
_     : [n, A, v : Tm (pow (s n) A)]            eq (proj v (fz n)) (hd v)      2
_     : [n, A, v : Tm (pow (s n) A), i : Fin n] eq (proj v (fs n i)) (proj (tl v) i)   2
```

### 2.3 Heterogeneous products (the board's `[A, B, …, C]`)

```text
Tys   : Sort                                                                   1
nilₗ  : Tys                                                                    1
consₗ : [A : Ty, L : Tys] Tys                                                  2
prod  : [L : Tys] Ty                                                           2
unit  : Tm (prod nilₗ)                                                         1
pair  : [A : Ty, L : Tys, a : Tm A, u : Tm (prod L)] Tm (prod (consₗ A L))     2
fst   : [A, L, u : Tm (prod (consₗ A L))] Tm A                                 2
snd   : [A, L, u : Tm (prod (consₗ A L))] Tm (prod L)                          2
_     : fst (pair a u) = a,   snd (pair a u) = u                               2
_     : u = unit  at prod nilₗ,   u = pair (fst u) (snd u)  at prod (consₗ A L)    2
```

`ind` does not use this layer. Its role is §5.2.

### 2.4 Signatures and `data` (the board's bottom block)

```text
Sig    : Sort                                       "List Nat"                 1
nilₛ   : Sig                                                                   1
consₛ  : [n : Power, R : Sig] Sig                                              2
Op     : [D : Sig] Sort                             constructor names          2
here   : [n : Power, R : Sig] Op (n ∷ R)                                       2
there  : [n : Power, R : Sig, o : Op R] Op (n ∷ R)                             2
ar     : [D : Sig, o : Op D] Power                                             2
_      : [n, R]           eq (ar (n ∷ R) (here n R)) n                         2
_      : [n, R, o : Op R] eq (ar (n ∷ R) (there n R o)) (ar R o)               2
data   : [D : Sig] Ty                                                          2
constr : [D : Sig, o : Op D, t : Tm (pow (ar D o) (data D))] Tm (data D)       2

ind    : [ D : Sig,
           P : [x : Tm (data D)] Ty,
           m : [ o : Op D,
                 t : Tm (pow (ar D o) (data D)),
                 h : [i : Fin (ar D o)] Tm (P (proj t i)) ]
               Tm (P (constr D o t)),
           x : Tm (data D) ]
         Tm (P x)                                                              4
βind   : [D, P, m, o : Op D, t : Tm (pow (ar D o) (data D))]
         eq (ind D P m (constr D o t)) (m o t ((i) ind D P m (proj t i)))      4
```

Optional uniqueness, which makes `ind D P m` the only solution of `βind`:

```text
ηind   : [ D, P, m, f : [x : Tm (data D)] Tm (P x),
           e : [o : Op D, t : Tm (pow (ar D o) (data D))]
                 eq (f (constr D o t)) (m o t ((i) f (proj t i))),
           x : Tm (data D) ]
         eq (f x) (ind D P m x)                                                4
```

The motive is `Ty`-valued, matching the board's `data : Schema → Ty`. A
`Sort`-valued motive is not positive (§3). `ind` therefore eliminates into the
universe `Ty`, not into every sort as Lean's recursors do.

### 2.5 Case analysis on positions and constructor names

`ind` takes one method `m` with a free constructor name `o`, and the hypothesis `h`
has a free position `i`. To program constructor by constructor and position by
position, add the following.

```text
fcase : [n : Power, Q : [i : Fin (s n)] Ty, q₀ : Tm (Q (fz n)),
         q₁ : [i : Fin n] Tm (Q (fs n i)), i : Fin (s n)] Tm (Q i)              3
fnone : [Q : [i : Fin z] Ty, i : Fin z] Tm (Q i)                               3
_     : fcase … (fz n) = q₀,   fcase … (fs n i) = q₁ i                         3
_     : [n, Q, f : [i : Fin (s n)] Tm (Q i), i]
          eq (f i) (fcase n Q (f (fz n)) ((j) f (fs n j)) i)                   3
_     : [Q, f : [i : Fin z] Tm (Q i), i]  eq (f i) (fnone Q i)                 3

ocase : [ n : Power, R : Sig, A : Ty,
          B  : [o : Op (n ∷ R), t : Tm (pow (ar (n ∷ R) o) A), i : Fin (ar (n ∷ R) o)] Ty,
          Q  : [o : Op (n ∷ R), t : Tm (pow (ar (n ∷ R) o) A)] Ty,
          m₀ : [t : Tm (pow n A), h : [i : Fin n] Tm (B (here n R) t i)]
                 Tm (Q (here n R) t),
          m₁ : [o : Op R, t : Tm (pow (ar R o) A), h : [i : Fin (ar R o)] Tm (B (there n R o) t i)]
                 Tm (Q (there n R o) t),
          o  : Op (n ∷ R),  t : Tm (pow (ar (n ∷ R) o) A),
          h  : [i : Fin (ar (n ∷ R) o)] Tm (B o t i) ]
        Tm (Q o t)                                                             4
_     : ocase … m₀ m₁ (here n R) t h = m₀ t h                                  4
_     : ocase … m₀ m₁ (there n R o) t h = m₁ o t h                             4
_     : [n, R, A, B, Q, f : [o, t, h] Tm (Q o t), o, t, h]
          eq (f o t h) (ocase … ((t h) f (here n R) t h) ((o t h) f (there n R o) t h) o t h)   4
onone : [A, B, Q, o : Op nilₛ, t, h] Tm (Q o t)       B, Q, t, h as above at nilₛ    3
_     : [A, B, Q, f : [o, t, h] Tm (Q o t), o, t, h]  eq (f o t h) (onone A B Q o t h)       4
```

`ocase` is rank 4, while `fcase` is rank 3, for the following reason. In `m`, the
types of `t` and `h` depend on `o`, and `Ty` has no Π. So the motive cannot
absorb `t` and `h`; the branches must bind them, `h` included.

### 2.6 Trees

```text
S_tree   := z ∷ (s (s z)) ∷ nilₛ             data tree = | 1 → T | T × T → T
tree     := data S_tree
leaf     := constr S_tree (here _ _) ()                          uses ar-here
node l r := constr S_tree (there _ _ (here _ _)) (cons l (cons r ()))
                                                                 uses ar-there, then ar-here

tree-ind : [ P : [x : Tm tree] Ty,  ml : Tm (P leaf),
             mn : [l r : Tm tree, p : Tm (P l), q : Tm (P r)] Tm (P (node l r)),
             x : Tm tree ]  Tm (P x)                                           3
```

`tree-ind` is the recursor Lean generates for `data tree`, up to the `Ty`-valued
motive. It is derivable `[routine]`:

```text
tree-ind P ml mn := ind S_tree P ((o t h) ocase z R tree B Q m_leaf m_rest o t h)
  m_rest := (o' t h) ocase (s (s z)) nilₛ tree B' Q' m_node
                       ((o'' t h) onone tree B'' Q'' o'' t h) o' t h
  R := (s (s z)) ∷ nilₛ,   B := (o t i) P (proj t i),   Q := (o t) P (constr S_tree o t)
  B', Q' := B, Q precomposed with there z R;   B'', Q'' likewise with there z R ∘ there _ nilₛ
  m_leaf := (t h) ml                                     t = ()  by pow-η at z
  m_node := (t h) mn (hd t) (hd (tl t)) (h (fz _)) (h (fs _ (fz _)))
                                          t = cons (hd t) (cons (hd (tl t)) ())  by pow-η
```

The two β-rules of `tree-ind` follow from `βind`, the `ocase` equations,
ar-here/ar-there, proj-fz/proj-fs and hd-cons/tl-cons.

Conversely, `ind S_tree` is recovered from `tree-ind` `[routine]`:

```text
ml        := m (here _ _) () ((i) fnone _ i)
mn l r p q := m (there _ _ (here _ _)) (cons l (cons r ())) ((i) fcase … p ((j) fcase … q ((k) fnone _ k) j) i)
```

`βind` at a variable `o` then follows from the η-slots of `ocase`, `onone`,
`fcase`, `fnone` and `pow`. The same argument works for any closed `D`, by
induction on `D` `[routine]`. So at a closed signature, `ind` with §2.5 is the
external schema's recursor.

---

## 3. The theory `T_data`: admissible types, positivity

`T_data := Theory.ofSchemas Ξ_data` (PT §3.1), generated by four schemas:

```text
[x : Tm A]                     over [A : Ty]
[i : Fin n]                    over [n : Power]
[o : Op D]                     over [D : Sig]
[h : [i : Fin n] Tm (B i)]     over [n : Power, B : [i : Fin n] Ty]
```

**Proposition 3.1.** `T_data` is positive `[paper]`.

*Proof.* By PT Def 3.2, every binder domain nested inside an entry must lie in
`Adm ∩ Pos`; the outermost entries need only `Pos` (B2).

- *Nested domains.*
  - `P`'s `x : Tm (data D)` and `m`'s `t` are instances of the first schema.
  - `m`'s `o` is an instance of the third.
  - `h`'s type `H := [i : Fin (ar D o)] Tm (P (proj t i))` is the fourth at
    `n ↦ ar D o`, `B ↦ (i) P (proj t i)`. It is in `Pos` because
    `[i : Fin (ar D o)]` is admissible.
  - The binder domains of `fcase`'s `Q` and `q₁`, of `fnone`'s `Q`, and of the
    `f` of their η-slots are instances of the second.
  - The binder domains of `ocase`'s `B`, `Q`, `m₀` and `m₁`, and of the `f` of
    the η-slots of `ocase` and `onone`, are instances of the first three schemas.
    The h-types inside `m₀`, `m₁` and `f` are instances of the fourth. This uses
    ar-here and ar-there, which are judgmental (PT §1.2).
  - `ηind`'s `e` is an `IdElement` under admissible domains (P2, P3).
- *`Adm ⊆ Pos`.* The first three schemas are in `Pos` by P1. The fourth is in
  `Pos` by P3, because its domain is an instance of the second. ∎

**Remark 3.2 (what is forced).**

- **Forced.** P3 forces every nested binder domain into `Adm`:
  - the second and third schemas, generically: via `(Q, q₀) ↦ ((i) prod nilₗ, unit)`
    at `fcase`'s `q₁`, and via the section `P ↦ (x) data D` at `m`'s `o`;
  - `H` over `[D, P, o, t]`, and the h-types of `ocase`;
  - `[x : Tm (data D)]` and `[x : Tm (pow k A)]`.
- **Chosen.** The generic first and fourth schemas; only their instances are
  forced. The generic fourth is the choice that makes §5.1 exact.
- **Not admissible.** `[n : Power]`, `[A : Ty]`, `[D : Sig]` and `[L : Tys]` are
  not generated by the four schemas, and positivity does not force them, since
  they are never nested binder domains. So no context of the tautological model
  has a variable of these sorts.

**Remark 3.3.** A `Sort`-valued motive `P : [x : Tm (data D)] Sort` (as in
`beyond-sogats-examples.md` §8.1) is never positive, since its atom is `U` `[paper]`.
This follows at once from PT Lemma 3.4 (a) and (c), that is,
`PositiveEntry.bind_inv` and `PositiveEntry.not_U` `[Lean]`.

**Corollary 3.4.** By PT Thm 7.5, the tautological model `𝒮_{T_data}` is initial
in `Mod(T_data)` `[paper]`. Its contexts can contain hypothesis variables
`h : [i : Fin n] Tm (B i)`, which are rank-2 entries. That closed terms of
`Tm (data D)` are the trees of `D` needs normalization `[open]`.

**Example 3.5 (the standard model)** `[routine]`.

```text
base          small sets
Ty(Γ)         Γ → Set
Tm A (Γ)      ∏_γ A γ
Power(Γ)      Γ → ℕ
Sig(Γ)        Γ → List ℕ
Fin, Op, pow, prod, data
              pointwise; data D γ is the term algebra of the signature D γ
Γ ⊲ A         Σ_γ A γ
```

All four schemas have extensions. The fourth is `Σ_γ ∏_{j < n γ} B γ j`. `ind`,
`fcase` and `ocase` are defined pointwise.

---

## 4. Rank

```text
rank 1   Power z Ty Tys nilₗ unit Sig nilₛ
rank 2   every other slot of §§2.1–2.4 up to constr, with its equations
rank 3   fcase fnone (with equations), onone
rank 4   ind βind ηind; ocase, its two equations and η; onone-η
derived  tree-ind, rank 3 (§2.6)
```

`rank Ξ_data = 4` `[paper]`. The number for each slot was recomputed mechanically
from its binding tree and checked independently. The accounting for `ind`:

```text
[i : Fin (ar D o)]                                  rank 1
h : [i : Fin (ar D o)] Tm (P (proj t i))            contributes 2
[o, t, h]                                           rank 2
m : [o, t, h] Tm (P (constr D o t))                 contributes 3
[D, P, m, x]                                        rank 3
ind                                                 contributes 4
```

**Proposition 4.1 (Def 1.1 of `beyond-sogats-syntactic.md`)** `[paper]`.

- **(i) holds without `ηind`.** Every nested entry is `of`-boundaried. With
  `ηind`, (i) fails at its `e`, an `eq` entry.
- **(ii) fails.** `rank Ξ_data = 4`.
- **(iii) fails in both directions.**
  - `Adm` contains the `Bind` type of the fourth schema.
  - `Adm` omits `[n : Power]`, `[A : Ty]`, `[D : Sig]` and `[L : Tys]`.

So Construction 2.1 of that note is undefined at `m`.

```text
⟨m⟩ = π⁺ ⟨o⟩ (π⁺ ⟨t⟩ (π⁺ ⟨h⟩ …))        ⟨h⟩ = π⁺ (Fin _) (el⁺ (Tm _))
```

The last domain, `⟨h⟩`, lies in `U`, not `U⁺`.

**Where the rank comes from.**

> "the induction hypothesis inherits the shape of the constructor argument"
> (`beyond-sogats-examples.md` §8.2)

Here the argument is a tuple of length `ar D o`, which is a term. So the hypothesis
cannot be a fixed list of entries. It becomes a binder over positions, and `m`
consumes it.

```text
                                    rank   top of the rank
pow, prod, data, constr               2    —
fixed recursor (tree-ind)             3    the motive binds; methods are flat
fcase                                 3    the motive binds
ind, ocase                            4    a method binds a hypothesis that binds
Ξ_λ⁺'s ind (metatheory §2.1)          4    lam binds, so its hypothesis binds
Brouwer rec (examples §2)             4    ol takes a sequence, so its hypothesis is one
W-elimination, NPS 1990 ch. 15        4    sup takes a family
W-elimination, Martin-Löf 1984        3    hypothesis reified as an element of a Π-type
```

`T_data` reaches rank 4 with first-order constructors only. The binder comes from
the arity being a term, not from any constructor argument being a function.

**Proposition 4.2 (fixed signatures).**

- For closed `D`, the per-constructor recursor is rank 3 `[paper]`.
- `ind D` stays rank 4, because `o` is still a variable.
- With §2.5, the two are interderivable (§2.6) `[routine]`.

---

## 5. Is rank 4 essential?

There are three known ways down to rank 3.

- §5.1 adds a sort isomorphic to `[i : Fin n] Tm (B i)`.
- §5.3 adds a type former isomorphic to it.
- §5.2 adds a `Tys`-valued code that agrees with it only at numerals.

### 5.1 By a sort `G`

```text
G     : [n : Power, B : [i : Fin n] Ty] Sort                                   3
absG  : [n, B, g : [i : Fin n] Tm (B i)] G n B                                 3
appG  : [n, B, u : G n B, i : Fin n] Tm (B i)                                  3
_     : [n, B, g, i]  eq (appG (absG g) i) (g i)                               3
_     : [n, B, u]     eq (absG ((i) appG u i)) u                               3
```

The construction:

- Replace by `u : G n B` every entry of type `[i : Fin n] Tm (B i)` that lies
  inside another entry's binding. These are:
  - the `h` of `m` in `ind`, `βind` and `ηind`;
  - the `h` of `m₀` and `m₁`;
  - the `h` of `f` in the η-slots of `ocase` and `onone`.
- Replace `ocase`'s and `onone`'s own outermost `h` as well, so that their
  equations pass `u` through.
- Insert `absG` in `βind` and `ηind`:
  `βind : … eq (ind D P m (constr D o t)) (m o t (absG ((i) ind D P m (proj t i))))`.
- Replace the fourth schema by `[u : G n B]`.

Call the result `T_data^G`. It is rank 3 `[paper]` and positive `[routine]`, and
without `ηind` every nested entry is `of`. Without `ηind`, or with its `e` reified
through an extensional `Eq` sort, it is a Kaposi–Xie `ToS⁺` signature that puts
`Power`, `Ty`, `Tys` and `Sig` in `U`, and `Tm`, `Fin`, `Op` and `G` in `U⁺`
`[routine]`.

**Models.**

- The round trip `T_data → T_data^G → T_data` is the identity. The round trip
  `T_data^G → T_data → T_data^G` replaces `(G, absG, appG)` by
  `([i : Fin n] Tm (B i), id, id)`.
- So the forgetful map `Mod(T_data^G) → Mod(T_data)` is surjective, and its
  fibres are the choices of an isomorphic `G` `[paper]`.
- An equivalence of categories is expected `[conjecture]`. The canonical map is
  not a bijection `[paper]`. So the argument of `beyond-sogats-semantics.md`
  Prop 4.3 does not yield the bijection of its Def 2.1 (3). Whether some other
  bijection exists is not decided here.

This is Construction 4.1 of that note with `F` parametrised by the free variables
of the reified binder. As written, 4.1's closed `F : sort` cannot reify `h`,
whose type mentions `D, P, o, t`.

**Remark 5.1.** Positivity is what makes this available. P3 puts every nested
binder domain into `Adm`, and the representability of the reified type is exactly
what `U⁺` requires. The expectation is that the construction extends to positive
theories whose `Adm` is generated by generic schemas, one for each reified sort
family `[conjecture]`. That needs an iteration argument, which is not given here
(compare §8, item 6). `IdElement` entries would reify through an extensional `Eq`
sort.

A `ToS⁺` sort lies in `U⁺` as a whole declaration. So a positive theory that makes
only some instances of a sort admissible has no direct counterpart. If the
expectation holds, rank alone does not separate positive theories from SOGATs;
this is `beyond-sogats-semantics.md` Remark 4.4 in the positive setting.

### 5.2 Through `Tys`: Benke–Dybjer–Jansson's `F^IH`, Lean's `.below`

```text
ihs  : [n, A, P : [x : Tm A] Ty, t : Tm (pow n A)] Tys                         3
_    : [A, P, t : Tm (pow z A)]          eq (ihs z A P t) nilₗ                 3
_    : [n, A, P, t : Tm (pow (s n) A)]   eq (ihs (s n) A P t) (consₗ (P (hd t)) (ihs n A P (tl t)))   3
dmap : [n, A, P, f : [x : Tm A] Tm (P x), t : Tm (pow n A)] Tm (prod (ihs n A P t))  3
_    : dmap z … = unit,   dmap (s n) A P f t = pair (f (hd t)) (dmap n A P f (tl t))   3

h    : Tm (prod (ihs (ar D o) (data D) P t))                       in ind's m
βind : eq (ind D P m (constr D o t)) (m o t (dmap (ar D o) (data D) P ((x) ind D P m x) t))   3
```

- **Rank and admissibility.** The new `ind` and `βind` are rank 3, and they need
  only `[x : Tm A]` and `[o : Op D]` admissible `[paper]`. `ocase` is not covered,
  because its `B` is not of the form `P ∘ proj`. `ocase`, its η and `onone`-η
  stay rank 4, and `fcase` and `ocase` still need `Fin` and the fourth schema.
- **Covering `ocase` as well.** Index by positions instead of tuples:

  ```text
  ihs'  : [n : Power, B : [i : Fin n] Ty] Tys                                   3
  _     : ihs' z B = nilₗ,   ihs' (s n) B = consₗ (B (fz n)) (ihs' n ((i) B (fs n i)))   3
  dmap' : [n, B, f : [i : Fin n] Tm (B i)] Tm (prod (ihs' n B))                 3
  _     : dmap' z B f = unit,
          dmap' (s n) B f = pair (f (fz n)) (dmap' n ((i) B (fs n i)) ((i) f (fs n i)))   3
  ```

  With every nested `[i : Fin n] Tm (B i)` replaced by `Tm (prod (ihs' n B))`, the
  whole theory is rank 3. At each numeral `n`,
  `ihs n A P t = ihs' n ((i) P (proj t i))` `[routine]`.
- **What it is.**
  - BDJ's Fig. 2 states `F^IH` and `F^map` as constants with equations at `Zero`
    and `Succ m`. That is exactly `ihs` and `dmap`.
  - Lean computes the same type by large elimination:
    `List.below = List.rec PUnit (fun a t ih => motive t ×' ih)`.
- **A different theory** `[paper]`. Take the families model with
  `Power = ℕ ⊔ {∞}`, `s ∞ = ∞`, `Fin ∞ = ℕ`, `pow ∞ A = A^ℕ`, and `Tys` the finite
  lists.
  - `T_data`'s `ind` exists, by well-founded recursion. `fcase` and `fnone`, with
    their η, hold, since `ℕ = 1 + ℕ`.
  - `ihs ∞ … t` at a constant stream `t` (so `tl t = t`) would satisfy
    `L = consₗ B L` in finite lists, which has no solution. `ihs'` fails in the
    same way.
  - The same model therefore separates BDJ's Fig. 2 presentation from `T_data`.

### 5.3 By a type former in `Ty` (Martin-Löf 1984)

```text
dpow  : [n, B : [i : Fin n] Ty] Ty                                             3
dproj : [n, B, u : Tm (dpow n B), i : Fin n] Tm (B i)                          3
dtab  : [n, B, f : [i : Fin n] Tm (B i)] Tm (dpow n B)                         3
+ β, η;     h : Tm (dpow (ar D o) ((i) P (proj t i)))
```

- **Rank.** Rank 3, and this one also covers `ocase` `[paper]`.
- **A different theory** `[paper]`. Take the families model restricted to
  countable sets:

  ```text
  Power      ℕ ⊔ {∞}, with s ∞ = ∞
  Fin ∞      ℕ
  Ty(Γ)      Γ → (countable sets)
  Tys        finite lists of countable sets
  pow ∞ A    the eventually constant streams
  ```

  - `pow`, `prod` and `data` preserve countability. In particular `data D` is the
    initial algebra of a finitary functor, reached at ω. So every `Tm` of a code
    is countable.
  - `T_data`'s `ind`, `fcase` and `ocase` exist.
  - `Tm (dpow ∞ (const bool))` would be `2^ℕ`, which no code has.
- **The MLTT situation.** This is why W-types are rank 3 inside MLTT: Π reifies
  the hypothesis (`beyond-sogats-examples.md` §2.1).

### 5.4 What can be claimed

```text
[paper]       T_data is rank 4 and not second-order (Def 1.1 (ii), (iii))
[paper]       Kaposi–Xie's translation is undefined on it as presented
[paper]       the reifications of §5.2 and §5.3 change the models
[conjecture]  Mod(T_data) ≃ Mod(T_data^G), a rank-3 ToS⁺-style signature
[open]        a rank-3 presentation over T_data's own sorts, adding no sort or code
```

So the example is beyond SOGATs as a presentation. Every known rank-3 version
gives the induction-hypothesis type a name, as a sort (§5.1) or as a code
(§§5.2–5.3). A semantic separation would need a reading in which that type is not
representable (§6).

---

## 6. Two readings of the binders over `Op` and `Fin`

This is the same fork as `beyond-sogats-examples.md` §5 (`nat ∈ 𝒫` / `nat ∉ 𝒫`).

```text
                   Op, Fin ∈ Adm   (T_data, §3)            Op, Fin ∉ Adm
m                  one method, o a free variable          Π over Op D
h                  one hypothesis, i a free variable      Π over Fin (ar D o)
positive           yes; PT Thm 7.5 gives 𝒮_T              no (P3 fails at m); models as in
                                                          semantics.md Def 3.1; initiality [open]
per constructor    through ocase (rank 4)                 where Op D and Fin k are constant
                                                          presheaves on k-element sets: one method
                                                          per constructor, one hypothesis per argument
```

- **Products over constant presheaves** `[paper]`. `Bind` over the constant
  presheaf on `K` is, at `(I, ξ)`, the dependent product `∏_{j ∈ K} C(I, (ξ, j))`,
  because `b(f, j) = b(id, j)·f`.
- **The model classes differ** `[paper]`. The constant presheaf on `K` is locally
  representable iff `|K| = 1`. For `|K| ≥ 2`, `v·⟨f, x⟩ = v` forces `x = v`. For
  `K = ∅`, there is no generic element `v`. So the constant models are excluded
  from the first reading.
- **The standard model is in both** `[routine]`. In Example 3.5, `⟦m⟧` is
  pointwise the tuple of per-constructor methods in both readings, since PT
  Lemma 2.3 needs an extension to exist, not to be admissible. The readings differ
  in their classes of models and their initial models, not in the value of `⟦m⟧`.
- **`ocase` is needed** `[conjecture]`. Consider `isLeaf : [x : Tm tree] Tm bool`,
  with `bool := data (z ∷ z ∷ nilₛ)`, `isLeaf leaf = tt` and
  `isLeaf (node l r) = ff`. It is not definable in `T_data` with `ocase`, its
  equations and the η-slots of `ocase` and `onone` removed. Countermodel sketch,
  over reflexive graphs:
  - `Op S_tree` relates `here` to `there here`; their arities differ, and `Power`
    has all edges.
  - `Fin`, over an edge `n — n'`, relates equal positions below both.
  - `Op` of `bool` is discrete.
  - `Sig` relates lists of equal length.
  - Every remaining slot preserves the relations, including `fcase`, `fnone`,
    their η, and `ηind`. `isLeaf` would relate `tt` to `ff`.
- **Against the ω-rule** (examples §5).
  - *Same mechanism:* a premise at an extension, against a Π over the semantic
    elements.
  - *Difference:* at closed `D`, `Op D` and `Fin k` are finite, and `ocase` closes
    the gap inside a positive theory. So §5's argument against a first-order
    presentation does not transfer.
- **A third reading.** `beyond-sogats-examples.md` §8.3 takes a mixed reading,
  `Fin ∈ 𝒫` and `Op ∉ 𝒫`, which is also not positive.

---

## 7. Literature

### 7.1 Closest prior art

Benke, Dybjer and Jansson (2003), §2.1 and Fig. 2, "Axioms for the theory of
homogeneous term algebras", stated in Martin-Löf's logical framework.

```text
Arity : Type (Zero, Succ),  Sig : Type ([], ::)        §2.1 text: Sig = [Arity] = [Nat]
T : Sig → Set,  Intro,  F⁰ (sums of powers),  F^IH,  F^map
rec : (Σ : Sig)(C : T_Σ → Set)((y : F⁰ T_Σ) → F^IH T_Σ C y → C (Intro y)) → (x : T_Σ) → C x
rec C d (Intro y) = d y (F^map T_Σ C (rec C d) y)
```

> "A one-sorted signature is nothing but a finite list of natural numbers,
> representing the arities of the operations of the signature."

The board's theory is theirs. Fig. 2 states `F^IH` and `F^map` as constants with
equations at `Zero` and `Succ m`, which is exactly the rank-3 presentation of §5.2;
the caption adds that "large elimination rules can be added". Their Alfa code
(`Homogenous.alfa`) defines `FIHa` by case on the arity, that is, by large
elimination.

`T_data` takes the other route: the hypothesis is a binder, and nothing names its
type. By §5.2, the ∞-model separates the two presentations.

Their variant `HomoFin.alfa` takes the constructor arguments as
`Fa n X = Fin n → X`, an MLTT function type in place of `X^n`. It defines only the
iterators `It` and `MIt`. With a dependent eliminator, its hypothesis would take
the §5.3 form `(i : Fin n) → C (x i)`.

### 7.2 The schema as an external family of rules

- **Generating the eliminator from the constructors.** Backhouse, Chisholm,
  Malcolm, Saaman (1989) read the elimination rule off the introduction rules.
  Coquand and Paulin (1990), Dybjer (1991, 1994) and Paulin-Mohring (1993) give the
  schemas of CIC and MLTT. Each `data` declaration is new constants, checked by a
  meta-level criterion.
- **Lean 4** (de Moura–Ullrich 2021).
  - Carneiro (2019) §2.6.3: for a recursive argument `u_i : ∀x::ξ_i. …` the
    hypothesis is `δ_i = ∀x::ξ_i. C … (u_i x)`, a Π over the argument's own
    binders. The hypothesis inherits the argument's shape.
  - Kernel: `src/kernel/inductive.cpp`.
  - `.below` and `.brecOn` are derived from `.rec` in
    `src/Lean/Meta/Constructions/BRecOn.lean`.
- **Agda and Rocq.** Positivity is an external check (reference manuals).

### 7.3 Internalised schemas: codes and generic rules

- **Codes replacing a schema.** Dybjer and Setzer (1999; 2003; 2006) give finite
  axiomatisations: codes plus one generic formation, introduction and elimination
  rule. This is the precedent for replacing a schema by finitely many rules.
- **Universes of datatypes.** Altenkirch–McBride (2003); Morris, Altenkirch and
  Ghani (2009); Morris (2007).
- **Levitation.** Chapman, Dagand, McBride and Morris (2010). `ind` takes one method
  over `⟦D⟧(μD)` with hypothesis `All D … P d`, computed by large elimination; this
  is the first reading of §6 reified as in §5.2. `π`/`switch` over the enumerations
  `En` (elements `#E`) is `ocase`.
- **Elaboration.** Dagand and McBride (2012) elaborate `data` declarations into
  codes, which is the step from the board's `data tree` to `S_tree`. See also
  Dagand's thesis (2013).
- **Curried eliminators.** Diehl and Sheard (2014) derive per-constructor
  eliminators from descriptions, as in §2.6.
- **Native datatypes and codes.** Escot and Cockx (2022); Ko, Chen and Lin (2022).
- **W-types.** Hugunin (2021): an inductive universe of inductive types, built
  from W.

### 7.4 The hypothesis as a predicate lifting

- Hermida and Jacobs (1998), and Ghani, Johann and Fumex (2012): induction through
  the lifting of `P` along the functor. `[i : Fin n] Tm (B i)` is that lifting for
  `X ↦ X^{Fin n}`.
- `Below`: McBride, Goguen and McKinna (2006). Motives: McBride (2002).

### 7.5 Semantics

- **W-types.** Martin-Löf (1984); Moerdijk and Palmgren (2000); Gambino and Hyland
  (2004). Dybjer (1997) represents inductive sets by W-types.
- **Containers and polynomial functors.** A signature `D` is the container
  `Op D ◁ Fin ∘ ar D` (Abbott, Altenkirch and Ghani 2005), and `data D` is its
  W-type. See also indexed containers (Altenkirch et al. 2015) and Gambino and Kock
  (2013).
- **Universal algebra.** `List Nat` is a ranked alphabet, and in the standard model
  `data D` is its initial term algebra (Goguen, Thatcher, Wagner and Wright 1977).
  So `constr` is an isomorphism there, by Lambek's lemma (1968). Internally, `ηind`
  gives only uniqueness of recursion into `Ty`-valued motives, because `Ty` has no
  Σ over `Op D` with which to state the structure functor.

### 7.6 Frameworks and their bound on order

The literature counts order one lower than our rank: `ind` is third order.

- **The rank-4 phenomenon, named in 1990.** Nordström, Petersson and Smith (1990),
  ch. 4:

  > "We limit ourselves here to assumptions whose variables are of arity 0; they
  > are sufficient for everything in type theory except for the elimination rule
  > involving the primitive constant funsplit (chapter 7) and the natural
  > formulation of the elimination rule for well-orderings."

  Their ch. 15 gives the rank-4 W-elimination. Martin-Löf (1984) gives the rank-3
  one.
- **Finitary type theories.** Haselwarter and Bauer (2023) §2.1:

  > "The metavariable arity associated to a metavariable M is a pair (c, n), where
  > … n is the number of term arguments it accepts."

  Premises bind object variables only, so `ind` is not an FTT rule and `T_data^G`
  is. Bauer, Haselwarter and Lumsdaine (2020), Def 3.22, likewise.
- **SOGATs.** Kaposi and Xie (2024); Uemura (2023). Uemura's thesis (2021),
  Remark 4.1.1: "we are not allowed to write a higher-order operator like
  ((A → B) → C) ⇒ D in a SOGAT".
- **Contexts with higher-order variables.**
  - Contextual modal type theory (Nanevski, Pfenning and Pientka 2008) has
    meta-variables `u::A[Ψ]` with `Ψ` ordinary, which is second order. See also
    Pientka (2008).
  - Multi-level contextual type theory (Boespflug and Pientka 2011) has
    meta^n-variables. It is the context-side counterpart of `𝒮_{T_data}`, whose
    contexts contain `h : [i : Fin n] Tm (B i)`.
  - Schroeder-Heister (1984): rules of arbitrary level.
- **Higher-order algebraic theories.** Arkor and McDermott (2020); Arkor (2022)
  ch. 4: `ord(X ⇒ Y) = max(ord X + 1, ord Y)`. Also Fiore and Mahmoud (2010), and
  Fiore and Hur (2010).
- **Theories of signatures.** Kaposi, Kovács and Altenkirch (2019); Kaposi and
  Kovács (2020); Kovács (2022).
  - There the eliminator of each signature is computed externally. It is never one
    entry quantified over signatures, which is what costs the rank here.
  - Kovács and Kaposi (2020) handle infinitary constructors by Π over external
    sets, which is the second reading of §6.

---

## 8. Corrections to existing notes

1. **`beyond-sogats-examples.md` §8.1 (e): `ind` is not positive.**
   - `P : [x : El (data s)] Sort` has atom `U`, which is not in `Pos`.
   - `e` binds `o : Op s`, which §8.3 keeps out of 𝒫.
   - `h`'s type is not in 𝒫.

   Each violates P3, so PT Thm 7.5 does not apply to that signature.
2. **§8.3, "𝒫 = { El, Fin } … ∉ 𝒫 : Power, Ty, Sig, Op".** Positivity forces `Op`
   and the hypothesis type into 𝒫. As stated, this is the mixed reading of §6.
3. **§8.2, "`h` must be a binder" `[proved]`, and the boxed "exactly one rank".**
   These are true for that signature. §5 here gives rank-3 variants that add a sort
   or a code.
4. **Part II's rank recall: "a slot whose binding has a binder contributes 4".**
   This last line is off by one. Such a slot contributes 3, as `tab` does (§8.1),
   which is what the line before it says. Rank 4 needs an entry whose own binding
   has a binder.
5. **`beyond-sogats-semantics.md` Construction 4.1: the closed `F : sort`.** It
   cannot reify a binder that mentions earlier entries. It needs the
   parametrisation of §5.1.
6. **Lemma 4.2: `rank R(Ξ) = rank Ξ − 1`.** This fails when several entries reach
   the maximum. `ind`, `βind`, `ηind` and `ocase` all carry `h`, so the reification
   must be applied simultaneously and iterated.
7. **Prop 4.3's proof: "the two theories have the same models".** This holds only
   up to `F ≅ Ψ`: the canonical map of models is surjective, not injective. So the
   proof does not establish the bijection of Def 2.1 (3). Either the definition
   should ask for an equivalence, or a different bijection is needed.
8. **`beyond-sogats-syntactic.md` Def 1.1 (iii), "exactly … the sort-boundaried
   slots".** Together with Construction 2.1 sending every sort to `U⁺`, this
   excludes `semantics.md`'s own `𝒫_MLTT`, which has no `[X : of ty]`. It should
   range over the sorts declared representable, Kaposi–Xie's `U⁺`.
9. **`beyond-sogats-examples.md`, opening: §8 grouped with §1 and §2.** The note
   groups §8 with §1 and §2 under `metatheory.md`'s `Ξ ↦ Ξ⁺`, whose mechanism is a
   binding constructor. §8 has none.

---

## 9. Status

```text
§2    signature well formed; equations typed via ar-here/ar-there      [routine]
§2.6  tree-ind ⇄ ind S_tree with §2.5, any closed D                    [routine]
§3    T_data positive                                                  [paper]
      Sort-valued motive not positive (from Lean lemmas)               [paper]
      initial model 𝒮_T (PT Thm 7.5, itself on paper)                  [paper]
      closed Tm (data D) = trees of D                                  [open]
§4    rank 4; Def 1.1 (ii), (iii) fail, (i) too with ηind              [paper]
§5.1  T_data^G rank 3                                                  [paper]
      T_data^G positive                                                [routine]
      Mod(T_data^G) → Mod(T_data) surjective, not injective            [paper]
      equivalence of model categories                                  [conjecture]
§5.2  rank 3 with ihs'; model classes differ                           [paper]
§5.3  rank 3; model classes differ                                     [paper]
§5.4  rank-3 presentation without a new sort or code                   [open]
§6    Bind over a constant presheaf = dependent product                [paper]
      constant presheaf representable iff singleton                    [paper]
      isLeaf undefinable in T_data minus the ocase slots               [conjecture]
      initiality for Op, Fin ∉ Adm                                     [open]
```

What would make the example precise, in order of payoff:

- **The equivalence `Mod(T_data) ≃ Mod(T_data^G)`.** It settles that the
  separation is one of presentation. If it fails, a separation candidate follows.
- **A Lean literal `Ξ_data`, at least through §2.4.**
  - Prove `Ambient.Wf` for it, as for `untypedLambdaSyntax` in
    `Theory/Examples.lean`.
  - Prove positivity. This is still open (`sorry`s in
    `untypedLambdaSyntax_positive`) even for that example.
  - Define `rank` on `dTel` and check `rank = 4` by `decide`.
- **The `isLeaf` countermodel.** It shows that §2.5 is needed and that `ocase` is
  not derivable.

---

## References

Verified against publisher or repository pages.

- Abbott, Altenkirch, Ghani. Containers: constructing strictly positive types. TCS 342(1), 2005. doi:10.1016/j.tcs.2005.06.002
- Altenkirch, Ghani, Hancock, McBride, Morris. Indexed containers. JFP 25, e5, 2015. doi:10.1017/S095679681500009X
- Altenkirch, McBride. Generic programming within dependently typed programming. IFIP WCGP 2002, Kluwer 2003. doi:10.1007/978-0-387-35672-3_1
- Arkor, McDermott. Higher-order algebraic theories. Preprint, 2020; Arkor, PhD thesis, Cambridge 2022, ch. 4. doi:10.17863/CAM.86347
- Backhouse, Chisholm, Malcolm, Saaman. Do-it-yourself type theory. Formal Aspects of Computing 1(1), 1989. doi:10.1007/BF01887198
- Bauer, Haselwarter, Lumsdaine. A general definition of dependent type theories. arXiv:2009.05539, 2020.
- Benke, Dybjer, Jansson. Universes for generic programs and proofs in dependent type theory. Nordic J. Computing 10(4), 2003. https://www.cse.chalmers.se/~peterd/papers/Generic.pdf (code: https://www.cse.chalmers.se/~patrikj/poly/gendt/)
- Boespflug, Pientka. Multi-level contextual type theory. LFMTP 2011, EPTCS 71. doi:10.4204/EPTCS.71.3
- Carneiro. The Type Theory of Lean. MSc thesis, CMU, 2019. https://github.com/digama0/lean-type-theory/releases/tag/v1.0
- Chapman, Dagand, McBride, Morris. The gentle art of levitation. ICFP 2010. doi:10.1145/1863543.1863547
- Coquand, Paulin. Inductively defined types. COLOG-88, LNCS 417, 1990. doi:10.1007/3-540-52335-9_47
- Dagand. A Cosmology of Datatypes: Reusability and Dependent Types. PhD thesis, Strathclyde, 2013.
- Dagand, McBride. Elaborating inductive definitions. arXiv:1210.6390, 2012; JFLA 2013.
- de Moura, Ullrich. The Lean 4 theorem prover and programming language. CADE-28, LNCS 12699, 2021. doi:10.1007/978-3-030-79876-5_37
- Diehl, Sheard. Generic constructors and eliminators from descriptions. WGP 2014. doi:10.1145/2633628.2633630
- Dybjer. Inductive sets and families in Martin-Löf's type theory and their set-theoretic semantics. In Logical Frameworks, CUP 1991. doi:10.1017/CBO9780511569807.012
- Dybjer. Inductive families. Formal Aspects of Computing 6(4), 1994. doi:10.1007/BF01211308
- Dybjer. Representing inductively defined sets by wellorderings in Martin-Löf's type theory. TCS 176, 1997. doi:10.1016/S0304-3975(96)00145-4
- Dybjer, Setzer. A finite axiomatization of inductive-recursive definitions. TLCA 1999, LNCS 1581. doi:10.1007/3-540-48959-2_11
- Dybjer, Setzer. Induction-recursion and initial algebras. APAL 124, 2003. doi:10.1016/S0168-0072(02)00096-9
- Dybjer, Setzer. Indexed induction-recursion. JLAP 66(1), 2006. doi:10.1016/j.jlap.2005.07.001
- Escot, Cockx. Practical generic programming over a universe of native datatypes. ICFP 2022. doi:10.1145/3547644
- Fiore, Hur. Second-order equational logic. CSL 2010, LNCS 6247. doi:10.1007/978-3-642-15205-4_26
- Fiore, Mahmoud. Second-order algebraic theories. MFCS 2010, LNCS 6281. doi:10.1007/978-3-642-15155-2_33
- Gambino, Hyland. Wellfounded trees and dependent polynomial functors. TYPES 2003, LNCS 3085, 2004. doi:10.1007/978-3-540-24849-1_14
- Gambino, Kock. Polynomial functors and polynomial monads. Math. Proc. Camb. Phil. Soc. 154(1), 2013. doi:10.1017/S0305004112000394
- Ghani, Johann, Fumex. Generic fibrational induction. LMCS 8(2:12), 2012. doi:10.2168/LMCS-8(2:12)2012
- Goguen, Thatcher, Wagner, Wright. Initial algebra semantics and continuous algebras. JACM 24(1), 1977. doi:10.1145/321992.321997
- Haselwarter, Bauer. Finitary type theories with and without contexts. J. Automated Reasoning, 2023. doi:10.1007/s10817-023-09678-y
- Hermida, Jacobs. Structural induction and coinduction in a fibrational setting. Inf. Comput. 145(2), 1998. doi:10.1006/inco.1998.2725
- Hugunin. Why not W? TYPES 2020, LIPIcs 188, 2021. doi:10.4230/LIPIcs.TYPES.2020.8
- Kaposi, Kovács. Signatures and induction principles for higher inductive-inductive types. LMCS 16(1), 2020. doi:10.23638/LMCS-16(1:10)2020
- Kaposi, Kovács, Altenkirch. Constructing quotient inductive-inductive types. POPL 2019. doi:10.1145/3290315
- Kaposi, Xie. Second-order generalised algebraic theories: signatures and first-order semantics. FSCD 2024. doi:10.4230/LIPIcs.FSCD.2024.10
- Ko, Chen, Lin. Datatype-generic programming meets elaborator reflection. ICFP 2022. doi:10.1145/3547629
- Kovács. Type-theoretic signatures for algebraic theories and inductive types. PhD thesis, ELTE, 2022. doi:10.15476/ELTE.2022.070
- Kovács, Kaposi. Large and infinitary quotient inductive-inductive types. LICS 2020. doi:10.1145/3373718.3394770
- Lambek. A fixpoint theorem for complete categories. Math. Z. 103, 1968. doi:10.1007/BF01110627
- Martin-Löf. Intuitionistic Type Theory. Bibliopolis, 1984.
- McBride. Elimination with a motive. TYPES 2000, LNCS 2277, 2002. doi:10.1007/3-540-45842-5_13
- McBride, Goguen, McKinna. A few constructions on constructors. TYPES 2004, LNCS 3839, 2006. doi:10.1007/11617990_12
- Moerdijk, Palmgren. Wellfounded trees in categories. APAL 104, 2000. doi:10.1016/S0168-0072(00)00012-9
- Morris. Constructing Universes for Generic Programming. PhD thesis, Nottingham, 2007.
- Morris, Altenkirch, Ghani. A universe of strictly positive families. IJFCS 20(1), 2009. doi:10.1142/S0129054109006462
- Nanevski, Pfenning, Pientka. Contextual modal type theory. ACM TOCL 9(3), 2008. doi:10.1145/1352582.1352591
- Nordström, Petersson, Smith. Programming in Martin-Löf's Type Theory. OUP, 1990. https://www.cse.chalmers.se/research/group/logic/book/book.pdf
- Paulin-Mohring. Inductive definitions in the system Coq: rules and properties. TLCA 1993, LNCS 664. doi:10.1007/BFb0037116
- Pientka. A type-theoretic foundation for programming with higher-order abstract syntax and first-class substitutions. POPL 2008. doi:10.1145/1328438.1328483
- Schroeder-Heister. A natural extension of natural deduction. JSL 49(4), 1984.
- Uemura. A general framework for the semantics of type theory. MSCS 33(3), 2023. doi:10.1017/S0960129523000208
- Uemura. Abstract and Concrete Type Theories. PhD thesis, Amsterdam, 2021.
