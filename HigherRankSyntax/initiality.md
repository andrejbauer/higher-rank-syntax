```text
HrS                                            SORTS   Ob < Sub, Ty < Tm
  Ob  : Type                      Ty : (Γ : Ob) → Type
  Sub : (Γ Δ : Ob) → Type         Tm : (Γ : Ob) (a : Ty Γ) → Type

CwF
  ⋄ : Ob    id : Sub Γ Γ    ∘ : Sub Δ Γ → Sub Ξ Δ → Sub Ξ Γ    ! : Sub Γ ⋄
  associativity, both units,   σ = !  for every σ : Sub Γ ⋄
  a[σ] : Ty Δ        t[σ] : Tm Δ (a[σ])
  a[id] = a,   a[σ ∘ θ] = a[σ][θ],   likewise for t
  ▷ : (Γ : Ob) → Ty Γ → Ob         p : (a : Ty Γ) → Sub (Γ ▷ a) Γ
  ν : (a : Ty Γ) → Tm (Γ ▷ a) (a[p a])
  ⟨_,_⟩ : (σ : Sub Δ Γ) → Tm Δ (a[σ]) → Sub Δ (Γ ▷ a)
  p a ∘ ⟨σ,t⟩ = σ      (ν a)[⟨σ,t⟩] = t      ⟨p a, ν a⟩ = id
  σ⁺a := ⟨σ ∘ p (a[σ]), ν (a[σ])⟩                                 derived

UNIVERSE — Tarski, closed under nothing
  U  : Ty Γ                        U[σ] = U
  El : Tm Γ U → Ty Γ               (El S)[σ] = El (S[σ])

Π — domain and codomain both unrestricted
  Bind  : (a : Ty Γ) → Ty (Γ ▷ a) → Ty Γ
  lam   : Tm (Γ ▷ a) c → Tm Γ (Bind a c)
  unlam : Tm Γ (Bind a c) → Tm (Γ ▷ a) c
  lam (unlam t) = t                unlam (lam e) = e
  (Bind a c)[σ] = Bind (a[σ]) (c[σ⁺a])        (lam e)[σ] = lam (e[σ⁺a])

EQUALITY — ETT's Id, declared only at the atoms  a ∈ { U , El S }
  Id   : (a : Ty Γ) → Tm Γ a → Tm Γ a → Ty Γ
  refl : (l : Tm Γ a) → Tm Γ (Id a l l)
  (Id a l r)[σ] = Id (a[σ]) (l[σ]) (r[σ])
  t t' : Tm Γ (Id a l r)  ⊢  t = t'                     irrelevance
  t    : Tm Γ (Id a l r)  ⊢  l = r : Tm Γ a             reflection

NO Σ, NO unit.   A theory is an object Ξ = ⋄ ▷ a₁ ▷ … ▷ aₙ.
A model of (Ξ, 𝒫) over 𝒞 is a global element of J_𝒞(Ξ) at which every Θ ∈ 𝒫
interprets as a locally representable dependent presheaf.
```

Marks: `[proved]` in the Lean tree; `[routine]`; `[sorry]`; `[open]`.

---

## Why `Ctx` carries it

```text
Ob       Σ Δ, {Ξ : dTel 1 Δ // Ambient.Wf Ξ}   Telescope.lean:625, Rules.lean:197  mod Eq_t
Sub Γ Δ  {σ : Subst |Δ| |Γ| // Wf_sub}         SubstitutionLemma.lean:836          mod Eq_sub
Ty Γ     Σ α, {Θ, β // Wf_t Γ (cons Θ β .nil)} Telescope.lean:15, Rules.lean:89    mod Eq_t
Tm Γ a   {τ // Wf_s Γ a τ}                     Rules.lean:51                       mod Eq_s
```

A type is **one entry**: a shape `α`, a binding `Θ : dTel |Γ| α` — the entries
the slot binds — and a declaration `β : Bd (|Γ| ⋈ α)`, written over `Γ` extended
by them, so it may mention what is bound; `β` equational included. `Wf_t` at
`cons Θ β .nil` unfolds by `Wf_t.cons` to `Wf_t Γ Θ` and `Wf_bd Γ Θ β`. A term
is a filling of the entry.

**CwF.** `⋄` is the empty ambient `𝟙`, terminal because it has no slots to fill.
`id` is the η-expansion of every slot, `Subst.id`; `∘` is **hereditary**
substitution, `Subst.comp`. So the category laws are the relative-monad laws
`act_η`, `act_id`, `act_comp` of `SyntaxMonad`. `[proved]` raw, `[routine]` for
`Wf_sub.id`, `Wf_sub.comp`

Reindexing of types and of terms is the one action `σ ⋆ −`, and its two laws are
`substitutionAt`'s package of six fields. `[proved]`

`Γ ▷ a` is `Ξ ⋈ a`; `p` is the projection renaming `C.inl` read as a filling;
`ν` is `Expr.η` of the fresh slot, `Subst.ofRenaming C.inr`; `⟨σ,t⟩` is
copairing of substitutions. The three axioms are Theorem 13.2 of
`equational-telescopes-core.md`. `[routine]`

**Universe.** `U := cons .nil .sort .nil` and `El S := cons .nil (.of S) .nil` —
the entries that bind nothing and declare `sort`, resp. `of S`. Then `Tm Γ U` is
the object theory's sort-expressions and `Tm Γ (El S)` its elements of `S`. The
two substitution laws are `Bd.act_sort` and `Bd.act_of`, both `rfl`. `[proved]`

**Π.** Write the two entries out. `a` is one entry over `Γ`, and `c` is one
entry over `Γ ▷ a`, whose arity is `|Γ| ⋈ C.single α`:

```text
cons {Ω α Δ} : (Θ : dTel Ω α) (β : Bd (Ω ⋈ α)) (rest : dTel (Ω ⋈ C.single α) Δ)
             → dTel Ω (C.single α ⋈ Δ)                        Telescope.lean:15

a = cons Θ_a β_a .nil     Θ_a : dTel |Γ| α                β_a : Bd (|Γ| ⋈ α)
c = cons Θ_c β_c .nil     Θ_c : dTel (|Γ| ⋈ C.single α) Δ
                          β_c : Bd ((|Γ| ⋈ C.single α) ⋈ Δ)

Bind a c := cons (cons Θ_a β_a Θ_c) β_c .nil
```

The inner `cons` is `dTel.cons` with **`rest := Θ_c`**: the new entry binds `a`,
then whatever `c` binds, so its binding has arity `C.single α ⋈ Δ`. The outer
`cons` instantiates its own `α` at that whole binding, and keeps `c`'s
declaration — which typechecks only because `β_c`, of type
`Bd ((|Γ| ⋈ C.single α) ⋈ Δ)`, is already of type `Bd (|Γ| ⋈ (C.single α ⋈ Δ))`.
`⋈` is composition in `Function.End`, so associativity and `_ ⋈ 1 = _` are both
`rfl`.

So the slot of `Bind a c` takes `a`'s arguments and then `c`'s, and declares
what `c` declares. Its fillings and `c`'s are then the *same raw data*:

```text
Tm Γ (Bind a c)    an expression over |Γ| ⋈ (C.single α ⋈ Δ),  boundary β_c
Tm (Γ ▷ a) c       an expression over (|Γ| ⋈ C.single α) ⋈ Δ,  boundary β_c
```

`lam` and `unlam` are therefore the identity, both round trips are `rfl`, and
`β`, `η` hold definitionally — which is why `Eq_e` carries neither rule.
`[proved]`

**Equality.** `Id a l r := cons .nil (.eq l r) .nil`. It is well formed because
`Wf_bd.eq` asks the two sides to have equal boundaries, and they do — both
`.sort`, or both `.of S`. `refl` exists because `Wf_s` requires of an equational
slot only that the equation hold, and `l ≈ l` is `Eq_e.refl`; no filler datum is
demanded, which is irrelevance, `Eq_s` not comparing equational slots (9.2,
6.3); and reflection is `Eq_e.hyp`, `Rules.lean:30`. `[proved]`

**Why `Id` is declared at the atoms only.** At an equational entry the fillings
carry unconstrained representatives that `Eq_s` does not compare, so `Id` there
would not respect the quotient. At a `Bind`-entry `Ctx` would satisfy
`Id (Bind a c) t t' = Bind a (Id c (unlam t) (unlam t'))` on the nose, which is
not an axiom of `ETT` — `Id (Π A B) f g` and `Π A (Id B (f x) (g x))` are there
isomorphic, never equal. Either would cost initiality.

---

## Why `Ctx` is initial

**No junk.** Each raw constructor is one clause of the spec.

```text
cons Θ β .nil,  Θ = .nil, β = .sort      U
                Θ = .nil, β = .of S      El S
                Θ = .nil, β = .eq l r    Id U l r   /   Id (El S) l r
                Θ = .cons …              Bind a c,  splitting Θ at its head entry
ap x args                                unlam at a variable head
```

Surjectivity onto `Ty Γ` is induction on the binding list: `cons (cons Θ_a β_a
Θ_c) β_c .nil` is `Bind a c` for the head entry `a` and the entry `c` over
`Γ ▷ a`. Surjectivity of `unlam` onto expressions is `Wf_e.ap`: every expression
is a slot applied to a **total** argument list and is already η-long, so it is
the iterated `unlam` of the slot's own variable, instantiated. `[routine]`

**No confusion.** `Eq_e` has five constructors (`Rules.lean:25`) and none is `β`
or `η`: `refl`, `symm`, `trans` are the congruence closure that any
GAT-equality has, `hyp` is reflection, `subst` is substitution congruence, which
in a GAT is free because substitution is an operation. `β` is absent because
`Subst.act` performs it, `η` because `Expr.η` makes every term η-long. So `≈` is
generated by the spec's own axioms and nothing else. `[proved]`, by inspection

**The recursor.** For an `HrS`-model `M`, by mutual recursion on `Bd`, `dTel`,
`Expr`:

```text
⟦.sort⟧ := U        ⟦.of S⟧ := El ⟦S⟧        ⟦.eq l r⟧ := Id _ ⟦l⟧ ⟦r⟧
⟦cons Θ β .nil⟧ := Bind ⟦a⟧ ⟦c⟧             for Θ ≠ .nil
⟦ap x args⟧ := (unlamⁿ (var x)) [ ⟨… ⟨id, ⟦args₁⟧⟩ …, ⟦argsₙ⟧⟩ ]
```

where `var x` is `ν` of `x`'s entry weakened by the `p`s of the slots after `x`,
and `n` is the length of `x`'s binding. Objects go by iterated `▷`, morphisms
slotwise. The recursion is on `Expr.Subterm` (well founded, `Expr.lean`) and
structural on `dTel`. Soundness of `Wf_e`, `Wf_bd`, `Wf_t`, `Wf_s` uses
`substitutionAt`; soundness of `Eq_e` uses reflection at `hyp` and naturality of
`lam` at `subst`. `[open]`

**Descent and uniqueness.** `⟦−⟧` is defined on representatives, so it must
respect `Eq_t`, `Eq_bd`, `Eq_e`, `Eq_s` and `Eq_sub`; invariance under an
`≈`-equal ambient is `Invariance.lean`, whose two open `sorry`s at `:24` and
`:31` are the only blocking gap. A strict morphism `F : Ctx ⟶ M` agrees with
`⟦−⟧` by induction on the same three inductives, the `ap` case using that `F`
preserves `unlam` and `ν`. `[sorry]`, `[open]`

**Why 1-categorical initiality is available at all.** Nothing in the spec is
imposed up to isomorphism, and the two equations that would force a pseudo
presentation — `Γ ▷ ⊤ = Γ` and `Γ ▷ Σ a c = (Γ ▷ a) ▷ c` — are not statable,
there being no `⊤` and no `Σ`. The raw layer is canonical: slot heads, total
argument lists, η-long terms, hereditary substitution.

**Theories as closed types.** In Kaposi–Xie a signature is a closed type of
`ToS⁺`, packed by `Σ`; here a theory is an object of `Ctx`. In the telescope
model `q : Tm ⟶ Ty` of `NaturalModel.lean:135` a theory is three things at once:

```text
Ξ : Ctx                      an object                        Ctx.lean:17
Ξ : empty.Tele               a telescope over ⋄, Ctx.toTele   Ctx.lean:35
Ξ : Ty.obj (op empty.toOb)   a closed type                    Ctx/Telescope.lean:204
```

At `X := empty.toOb` both `X.arity = 1` and `Ob.Tele.Wf X Θ = Wf_t .nil Θ` hold
by `rfl`, `Quotient.liftOn` and `Quotient.hrecOn` computing on `Quotient.mk`. So
`Ctx ≃ Ob.Tele X` is field-for-field, and `Ctx.Rel` (`Ctx.lean:62`) and
`Ob.Tele.Rel` (`Ctx/Telescope.lean:61`) differ only by a `Wf_t` conjunct that the
subtype supplies. `Quotient.congr` then gives

```lean
Ob ≃ Ty.obj (Opposite.op empty.toOb)
```

`[routine]`. It is the `⋄` instance of: `extend X : Ty.obj (op X) → Ob`
(`Ctx/Telescope.lean:229`) is injective, i.e. `Eq_t` cancels a common prefix
under `concatenate`; at `X = ⋄` it is also surjective. `[open]`

The packing `Σ` does for Kaposi–Xie is done here by telescope concatenation,
associative on the nose (`concatenate_assoc`) where `Σ` in a CwF is associative
up to isomorphism: the telescope presheaf `Ty` is the strict `Σ`-closure of the
single-entry `Ty` of the table above. As a specification, `HrS_tel` is `HrS` with
a telescope former and the strict laws

```text
Γ ▷ (Θ ⋈ Ψ) = (Γ ▷ Θ) ▷ Ψ          Γ ▷ nil = Γ
```

`Ctx` with telescopes as types is a strict model of `HrS_tel`, and every
`HrS`-model becomes one by taking lists of types as telescopes. Presheaf
categories are not strict `HrS_tel`-models, so initiality is claimed for `HrS`;
`HrS_tel` is the packaging layer above it in which "a theory is a closed type"
holds verbatim.

---

## Why this fragment specifies higher-rank theories

> The fragment is exactly the judgement forms of a generalised algebraic theory,
> closed under hypothetical judgement with no restriction on what may be
> hypothesised.

Cartmell's GAT has four judgement forms and two equalities. Every one of them is
an item of the spec, and the spec has nothing else:

```text
Γ ctx                  an object                Ob
Γ ⊢ A sort             a term of U              U : Ty Γ
Γ ⊢ a : A              a term of El A           El : Tm Γ U → Ty Γ
Γ ⊢ A = B sort         Id_U                     equations between SORTS
Γ ⊢ a = b : A          Id_El                    equations between ELEMENTS
───────────────────────────────────────────────────────────────────────────
"given …, you get …"   Bind                     the hypothetico-general
                                                judgement
```

So `Id` at the atoms is not an awkward proviso: **`Id_U` and `Id_El` are
Cartmell's two equality judgements**, and a theory has nothing else to equate —
an equation between proofs is vacuous by irrelevance, and an equation between
operations would be a claim about the framework rather than about the theory.

`Bind` is likewise not a chosen type former. Harper, §2 of `arXiv:2106.01484`:
"LF uses dependent function classes to define the **hypothetico-general
judgment** form that is central to the definition of many logical systems",
citing "the deductive apparatus of a logic — its basic, hypothetical, and
general judgments, and the evidence for them (Martin-Löf, 1987)".

**Where the rank comes from.** A GAT is rank 2 because its premises are
*elements*. Make a premise itself a hypothetical judgement and the rank rises;
let that nest and every rank appears:

```text
premise is an element                       Bind (ι…) …             GAT
premise is "given x : A, an element of B"   Bind (Bind …) …         SOGAT
premise is "given such a premise, …"        Bind (Bind (Bind …)) …
```

**unrestricted `Bind`-domain ⟺ arbitrary rank.** Uemura and Kaposi–Xie restrict
the domain, which is what bounds the rank at 3 and forces reification above it.
Nothing else in the spec touches rank.

**Each omission is a refusal, not a gap.**

```text
no Σ, no ⊤             a theory is a LIST of declarations, not one packed
                       thing — Cartmell's convention, and LF's "a signature
                       is a context"
U closed under nothing the framework supplies BINDING, the theory supplies its
                       SORTS.  Closure would donate function-sorts to every
                       theory that never declared them
Id only at the atoms   equations are between the things the theory talks about
no restriction on      the one place we refuse a RESTRICTION rather than a
Bind's domain          convenience
```

Every omission is the framework declining to give theories something for free.
That is what makes it a specification language rather than a type theory in its
own right.

**Two stumbling blocks**, both old.

*The framework is weaker than what it specifies.* MLTT — with `Σ`, `⊤`,
universes closed under everything — is specified in a language that has none of
those. That is the LF bet: the framework organises binding and dependency, all
strength comes from the declared constants, and adequacy theorems are the
tradition's certificate that the bet pays.

*`Π` plays two unrelated roles.* `Bind` is rule arity; the object theory's `Π`
is a declared constant whose *type* is written with `Bind`. In MLTT-as-a-
signature both appear on the same line.

**What is classical, and what is not.**

```text
judgements as types, hypothetico-general Π   Martin-Löf 1987; Harper–Honsell–
                                             Plotkin 1993
binding as meta-level function space         HOAS, Pfenning–Elliott 1988, with
                                             canonical forms as the standard fix
GAT judgement forms                          Cartmell 1986
U closed under nothing ⟹ strict positivity   Kaposi–Kovács–Altenkirch: ToS's U
                                             has no closure for this reason
rank as nesting depth                        Fiore–Mahmoud (second order),
                                             Arkor (nth order), Kaposi–Xie
                                             (SOGAT = order 2)
extensional equality in a framework          Harper, arXiv:2106.01484
```

The statement that ties them — *this* fragment of `ETT + U`, characterised by
what it omits, as the language of arbitrary-rank theories, with `Id` at the
atoms being exactly Cartmell's two equalities — was not found in the
literature. `[open]`, and three web searches are not a survey.
