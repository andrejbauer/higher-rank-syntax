# HrS and the literature

A reading guide.  It places the framework `HrS` against the research it draws
on, says for each of its design clauses whether the literature states it,
whether it is our own reading, or whether it is open, and lists what to read
to go deeper.  It was assembled from the primary texts (URLs in §9), quoting
verbatim; where a source could not be obtained, §10 says so.

The specification of `HrS` is `initiality.md`; the Lean record is
`HigherRankSyntax/HrS/Structure.lean`, and morphisms of models are
`HigherRankSyntax/HrS/Morphism.lean`.

---

## 0. The fragment

```text
HrS  =  a category with families           Ob, Sub, Ty, Tm, ⋄, ▷, p, ν, ⟨_,_⟩
      + a Tarski universe closed under nothing   U : Ty Γ,   El : Tm Γ U → Ty Γ
      + Bind, a dependent product with domain AND codomain unrestricted
      + extensional Id, declared ONLY at the atoms U and El S
          (reflection and irrelevance; no Id at Bind-types)
      − no Σ, no ⊤
```

A theory is a context of `HrS`, equivalently a closed type.  The claim of
`initiality.md` is that this fragment is the language of theories of arbitrary
rank, where rank is the nesting depth of hypothetical judgements, that `Id` at
`U` and at `El S` are Cartmell's two equality judgements, and that each omission
is the framework declining to give theories something for free.

The one-sentence version of the whole argument.  A rule says "given these
premises, you get this conclusion"; Martin-Löf shows "given" has two forms,
hypothetical and general, and the logical-framework tradition shows one
dependent function type captures both, which is `Bind`.  What a premise may
*be* is then the whole question: an element (algebraic theories), an element of
a dependent sort (GATs), or itself a hypothetical judgement (SOGATs), each step
being one more `Bind` nested in the domain of a `Bind`.  Bounding the domain
bounds the rank; leaving it unrestricted admits every rank.  The universe is
closed under nothing because the framework's job is binding and the theory's
job is its sorts.  And Cartmell's GATs have exactly two equality judgement
forms, which is what `Id` at `U` and at `El S` are.

---

## 1. The five clauses and their status

| clause | status |
|---|---|
| `Bind` is the hypothetico-general judgement; a rule is an element of a `Bind`-type | **stated** (Martin-Löf, HHP, Harper) |
| the theory's sorts are the terms of a universe with `El` and no closure | **stated** (KKA, Kaposi–Xie); the *motive* differs, see §4 |
| unrestricted `Bind`-domain is what admits arbitrary rank | **our reading**; the nearest statement is Gratzer–Sterling, §3 |
| `Id` at `U` and at `El S` are Cartmell's T= and ε= judgements | **our reading**; no source pairs them, and no source restricts `Id` to atoms |
| each omission is a refusal to donate structure | **our reading**; the literature supplies the ingredients, not the reading |

Two facts frame everything below.  First, in HHP's LF the basic judgement
forms are themselves declared constants (`tp`, `el`, `true`), so LF is broader
than `HrS`: `HrS` hardwires Cartmell's two forms as `U` and `El` and is a
framework for GAT-shaped theories specifically.  Second, the literature's word
is "order" (Fiore, Arkor, Uemura, Kaposi–Xie) or "level" (Martin-Löf,
Schroeder-Heister, Gratzer–Sterling), never "rank", and its count is one lower
than ours: a GAT is first-order, a SOGAT second-order.  `initiality.md` calls
them rank 2 and rank 3.  Keep the offset in mind when reading.

---

## 2. Judgements as types; `Bind` as the hypothetico-general judgement

**Stated in the literature.**  Martin-Löf's analysis is that there are two ways
of making a new judgement from old: assume one (hypothetical) or leave a
variable free (general), and that the hypothesis may be any judgement whatever.
The two fuse into one hypothetico-general form whose evidence is a function
from evidence to evidence.  HHP make this the judgements-as-types principle:

> "rules are viewed as proofs of higher-order judgements"
> — Harper, Honsell, Plotkin 1993

> "J1 ⊢ J2 = J1 → J2   and   ⋀x∈C J(x) = Πx:C.J(x)"
> — HHP 1993

and Harper explains the consolidation of both forms into one:

> "the entailment J1, . . . , Jn ⊢ J becomes ξ1 ∈ J1, . . . , ξn ∈ Jn ⊢ ε ∈ J"
> — Harper, Notes on Logical Frameworks, 2012

That single former is `Bind`.  `lam`/`unlam` say that evidence for a
hypothetical judgement is a function of evidence for its hypotheses, and a
theory is a list of rules whose types are judgements.

**Worth internalising.**  `Bind` is nobody's Π.  Martin-Löf places the
hypothetico-general judgement *prior* to the universal quantifier, and in any
object theory written in `HrS` the object-level Π is a declared constant whose
rules are written with `Bind`.  `initiality.md` §"Two stumbling blocks" notes
this; the literature makes it a first principle.

**Read.**  HHP 1993 §§1–2 for the principle and §4 for adequacy, which is what
licenses a framework weaker than what it specifies.  Martin-Löf 1983/1996,
third lecture, for the two forms of judgement and why the hypothesis may be
anything.  Harper 2012 for the six-page summary.  Pfenning–Elliott 1988 for
binding as meta-level function space.

---

## 3. Order, and the domain of `Bind`

**Stated in the literature: what order is.**  Arkor and McDermott define it as
nesting depth:

> "A second-order operator may therefore be presented by an inference rule
> whose premisses are themselves (first-order) inference rules"
> — Arkor, McDermott, Higher-order algebraic theories

with `ord(X ⇒ Y) = max(ord(X) + 1, ord(Y))`, the ⇒-formation rule carrying the
side condition `ord(X) < n`, and `n = ω` lifting the bound.  Our rank is the
left-nesting depth of `Bind` in a declaration's type with the base counted as
1, hence their theory-order plus one.  Arkor's Example 3.12 shows order is
relative to presentation.

**Stated in the literature: where frameworks bound it.**  In every framework
examined the bound is a side condition on the *domain* of the framework's
function type, and nowhere else.  But two different axes are being restricted,
and `initiality.md` runs them together:

(a) *Which basic forms may be hypothesised.*  Uemura's Π rule demands a
representable domain `Γ ⊢ A : ∗`, because

> "judgments in DTT cannot have hypotheses of the form (X : Type)"
> — Uemura, HoTTEST slides, 2020

(b) *How deep Π nests.*

> "we are not allowed to write a higher-order operator like ((A → B) → C) ⇒ D
> in a SOGAT"
> — Uemura, thesis, 2021

A hypothesis `X : U` or `p : Id` adds nothing to depth yet already leaves GAT
expressivity, so depth alone does not measure what the restriction buys.  `HrS`
lifts both restrictions at once.  Among the sources only Gratzer–Sterling's
"unrestricted hypothetical judgment" does the same.

**What actually decides the level.**  What may sit in a domain is fixed
*jointly* by the domain rule and by what the universe contains.  Kaposi–Xie
keep the `Ty`-level Π at `El`-domains and close `U` instead: ToS⁺ adds a
subuniverse `U⁺` with

> "a Π type with U+-domain and U-codomain"
> — Kaposi, Xie 2024

whose π⁺ lands in `Tm U`, so a `Ty`-level Π never sits in a domain.  Harper
restricts the Π-domain to a sort but

> "The class Sort is required to be closed under dependent function sorts"
> — Harper 2021

so nesting is unbounded there by the opposite trade.  KKA's restriction is the
strict-positivity one:

> "we cannot write Π (Π a B) C because the first argument of Π needs to be small"
> — Kaposi, Kovács, Altenkirch 2019

and Uemura says of the two restrictions that they "should be related, but we
leave it as future work".  Only because `HrS`'s `U` is closed under nothing
does the `Bind`-domain rule *alone* decide the level.

**Our reading, and the nearest statement.**  The one-clause picture in
`initiality.md`, GAT / SOGAT / `HrS` differing only in the domain of `Bind`, is
a reconstruction: neither Uemura nor Kaposi–Xie obtain second order by relaxing
that domain.  Gratzer–Sterling come nearest: representable-only dependent
products correspond to

> "hypothetical judgments of one level only"

whereas Martin-Löf's framework

> "supports hypothetical judgments of arbitrary level"
> — Gratzer, Sterling 2021

The signature languages also admit external parameters and infinitary
constructors; `HrS` has neither, so any "precisely" is for closed finitary
theories.

**Read.**  Fiore–Mahmoud 2010 §§1–2, 4 for second order as "terms under bound
variables", i.e. parameterised metavariables.  Arkor–McDermott §§2–3 for the
n-th order definition and the ⇒-rule with its side condition.  Uemura 2023
§4 (Defs 4.1–4.5) and thesis Remark 3.2.12 for the representable-domain rule
and its motive.  Kaposi–Xie 2024 §§3–4 for ToS and ToS⁺.  Gratzer–Sterling
2021 §1 for the level language.  Bocquet 2022 §3 for a third convention on
what counts as zeroth-, first-, second-order.

---

## 4. The universe as the sort-space

**Stated in the literature.**

> "an empty universe ... This allows us to add sorts to a signature"
> — Kaposi, Kovács, Altenkirch 2019

> "The base type U is for declaring sorts"
> — Kaposi, Xie 2024

Harper likewise uses `Sort` for the theory's syntactic categories, though his
`Sort` is closed under Π-sorts.  Altenkirch–Kaposi remark that an unclosed
`(U, El)` "is not a universe, but a base type", and Palmgren's abstract
definition of a universe includes closure under type constructions; so "a
universe closed under nothing" is our phrase for what the literature calls a
base type of codes with a decoding.

Uemura's category `G`, freely generated by an exponentiable arrow
`∂0 : E0 → U0`, is `(finite GATs)ᵒᵖ`, and a model of it "is precisely a natural
model (category with families)" (Uemura 2023, Thm 4.12, Cor 4.13).  But `G` has
pushforward along `∂0` (the `El`-hypotheses) and finite limits (the equations),
so it classifies `(U, El, Bind with El-domain, equations)`, not the bare pair;
`HrS` lacks finite limits, has unrestricted `Bind`, and takes its equations
from `Id` with reflection.  Reading `HrS` as "the language whose theories are
GATs" is a transfer of his theorem, not the theorem.

**Where the motive differs.**  The literature's stated reason for leaving `U`
unclosed is strict positivity, which is what delivers initial algebras:

> "As U is not closed under this function space, these function types cannot
> (recursively) appear in inductive arguments, which ensures strict positivity"
> — Kaposi, Kovács 2020

`initiality.md`'s reason is that closure would donate function-sorts to every
theory.  The two coincide in effect.  But the literature attaches a *theorem* to
its restriction (signatures are algebraic theories with initial algebras), and
`HrS` removes the domain restriction that carried that guarantee.  Kaposi–Xie
say of exactly the shape `lam : (Tm → Tm) → Tm` that it is "not first-order
(not strictly positive), hence this is not an algebraic theory anymore".  See §7.

**Read.**  KKA 2019 §§1, 3 and Kaposi–Kovács 2020 §2 for `U`/`El` as sort
declaration and the positivity argument.  Awodey 2018 for a type former as a
pullback square of natural transformations, so that omitting one is omitting
structure.  Sterling 2019 for "every former is further structure on the
initial CwF".  Coquand 2018 for a Tarski universe presented on a CwF.  Palmgren
1998 for Tarski versus Russell.

---

## 5. `Id` at the atoms and Cartmell's two equalities

**Stated in the literature.**  Cartmell's four conclusion forms are `Δ is a
type`, `t ∈ Δ`, `Δ = Δ'`, `t = t' ∈ Δ`, and

> "Each axiom is either a T=rule or an ε=rule"
> — Cartmell, thesis 1978, ch. 1

So a GAT has exactly two equality judgement forms, between sorts and between
elements.  Harper's reason for building equality into a framework at all:

> then "any interpretation must obey the specified laws"
> — Harper 2021

**Our reading.**  The pairing of `IdSort` with T= and `IdElement` with ε= is
`initiality.md`'s; no source makes it.  It passes through reflection, since
Cartmell's equalities are judgements, not types.  Three refinements the
literature forces on the picture:

- Cartmell's premises are lists `xᵢ ∈ Δᵢ`; to hypothesise an equation (a Horn
  clause) he adds a *sort* `Eq(x₁, x₂)` with `r(x) ∈ Eq(x, x)` and axioms
  `y₁ = y₂`, `x₁ = x₂`, which is exactly what `HrS` calls irrelevance and
  reflection at `El`.  `IdElement` is a large, non-iterable version of that
  `Eq`-sort:

  > "The identity type itself is large", which "prevents us from writing
  > iterated equality types"
  > — Kaposi, Kovács, Altenkirch 2019

- Cartmell has no sort for equality *of sorts*; `IdSort` internalises T= as a
  hypothesisable type, which he never does.

- **No framework surveyed places `Id` at exactly `U` and `El`.**  KKA have it at
  `El` only; Harper at every sort including Π-sorts (and draws the consequence
  "equality at function type is extensional"); Uemura and Kaposi–Xie at every
  type; Uemura's and Bocquet's SOGATs drop sort equations altogether.  The atom
  restriction is therefore not a variant found anywhere but a departure from
  every framework read, and `initiality.md`'s argument that `Id` at a
  `Bind`-type "would cost initiality" is `HrS`-specific.

**Read.**  Cartmell thesis ch. 1 §1.6 (Definitions 1–3) and §1.3 ("Predicates
as types", the `Eq`-sort construction).  Harper 2021 §§1–2 and Figs 4–6 for
reflection and unicity as framework rules.  KKA 2019 §3 for `Id` at `El` and
the largeness remark.

---

## 6. Omissions as refusals

**Stated in the literature: the ingredients.**  HHP built LF "as weak as
possible" and call its extra structure "a conservative extension of the
underlying logic"; Harper wants framework judgements "analytic" so as to "avoid
the infinite regress" (Harper 2012).  Algebraically, every former is "further
structure" on the initial CwF (Sterling 2019), and Σ is packaging "instead of a
newline-separated list" (Kaposi–Xie 2024).

**Also stated, and cutting the other way.**  HHP record the mirror image: what
the framework supplies is *imposed everywhere*.  Π forces weakening and
contraction, so "relevance and linear logics" fall outside LF; every CwF
likewise donates the structural rules.  A framework cannot decline to donate
what it is made of.

**Our reading.**  No source calls omissions refusals.  HHP's motive is
unification, KKA's positivity, and Kaposi–Kovács treat the lack of Σ as costing
no expressiveness.  The "each omission is a refusal" framing in `initiality.md`
is ours.

---

## 7. The cost: semantics of an unrestricted domain

This is the section that bears on the formalization.

> "a logical framework often lacks a good notion of a model of a signature.
> Models of a signature may not even form a category (Capriotti 2016)"
> — Uemura 2023, §1

Representable Π is safe because it "is defined by a pullback", which underwrites
compact generation of the (2,1)-category of models (Uemura thesis, Remark
3.2.12); Bocquet gives the same reason for local finite presentability and the
existence of initial models.  Capriotti's counterexample is Π nested on the
left, `Φ :≡ (U → U) → U`, and his morphisms are logical-relation, not strict;
whether strictness avoids his counterexample is not addressed in any source
read.  Kaposi–Xie:

> "there is no meaningful notion of homomorphism of second-order models"

so "we turn it into a GAT".  Uemura offers sufficiency alongside the semantic
reason, not necessity: "variable binding in a type theory only occurs at the
'first-order' level".

**The open point.**  None of the sources gives arbitrary level a 1-categorical
initiality theorem with strict morphisms; their classifying objects are locally
cartesian closed categories.  `HrS`'s `Morphism` is strict, and `initiality.md`
argues the raw layer is canonical (slot heads, total argument lists, η-long
terms, hereditary substitution).  Whether that is what rescues 1-categorical
initiality for an unrestricted `Bind` is exactly the question the literature
leaves open and the question the initiality proof will answer.  It is an
obligation the fragment takes on, not one it inherits.

**Read.**  Uemura 2023 §1 and thesis §3.2 for the model-category argument.
Capriotti 2016 §§2.5–2.7 for the counterexample.  Kaposi–Xie 2024 §§6–8 for the
first-order semantics that recovers a category of models.  Gratzer–Sterling
2021 §5 for the LCCC classifier.

---

## 8. Ledger

**In the literature, used as stated.**

- A rule is an element of a dependent function type; hypothetical and general
  judgement are one former.  (Martin-Löf; HHP; Harper.)
- Order is the left-nesting depth of the function type; frameworks bound it by
  a side condition on the domain.  (Fiore–Mahmoud; Arkor–McDermott; Uemura;
  Kaposi–Xie.)
- A theory's sorts are terms of a base type of codes with a decoding, and its
  operations are terms of `El`-types.  (KKA; Kaposi–Xie; Harper.)
- A GAT has exactly two equality judgement forms.  (Cartmell.)
- A framework should be weaker than what it specifies; adequacy is the
  certificate.  (HHP.)
- Restricting the Π-domain is what buys a well-behaved category of models.
  (Uemura; Bocquet; Kaposi–Xie; Capriotti.)

**Ours, not found stated anywhere.**

- The one-clause picture: GAT, SOGAT and arbitrary rank differ only in the
  domain of `Bind`.
- The identification of `IdSort`/`IdElement` with Cartmell's T=/ε= forms.
- `Id` at exactly the atoms `U` and `El S`, and the argument that `Id` at a
  `Bind`-type would cost initiality.
- Omissions read as refusals.
- Rank counted from 2 rather than order counted from 1.

**Open, and decided by the formalization.**

- Whether strict morphisms and a canonical raw layer give 1-categorical
  initiality for unrestricted `Bind`, against the literature's grounds for
  restricting the domain.  (`initiality.md` §"Why 1-categorical initiality is
  available at all"; to be settled by the proof that `Ctx` is initial.)
- The relation between Uemura's representability restriction and KKA's
  strict-positivity restriction, which Uemura leaves as future work and which
  `HrS` collapses by closing `U` under nothing.

---

## 9. Reading list

Ordered within each group.  "Read for" says what the source contributes to the
argument above.  Access status is recorded where the text was only partially
obtained.

**Judgements as types.**

- Harper, Honsell, Plotkin, *A Framework for Defining Logics*, JACM 40(1),
  1993.  https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf
  Read for: §§1–2 the principle; §4 adequacy; the remark that Π imposes
  weakening and contraction.
- Martin-Löf, *On the Meanings of the Logical Constants and the Justifications
  of the Logical Laws*, Siena 1983 / NJPL 1996.
  https://archive-pml.github.io/martin-lof/pdfs/Meanings-of-the-Logical-Constants-1983.pdf
  Read for: the third lecture, hypothetical and general judgement, and why the
  hypothesis may be any judgement.
- Harper, *Notes on Logical Frameworks*, IAS 2012.
  https://www.cs.cmu.edu/~rwh/papers/lfias/lf.pdf
  Read for: the six-page consolidation; "analytic" judgements.
- Pfenning, Elliott, *Higher-Order Abstract Syntax*, PLDI 1988.
  https://www.cs.cmu.edu/~fp/papers/pldi88.pdf
  Read for: binding as meta-level function space.

**Equational frameworks.**

- Harper, *An Equational Logical Framework for Type Theories*,
  arXiv:2106.01484, 2021.  https://arxiv.org/pdf/2106.01484
  Read for: reflection and unicity as framework rules; `Sort` closed under
  Π-sorts as the opposite trade to `HrS`; "any interpretation must obey the
  specified laws".
- Gratzer, Sterling, *Syntactic categories for dependent type theory:
  sketching and adequacy*, arXiv:2012.10783, 2021.
  https://arxiv.org/pdf/2012.10783
  Read for: "hypothetical judgments of one level only" versus "arbitrary
  level"; the LCCC classifier.
- Sterling, *Algebraic Type Theory and Universe Hierarchies*,
  arXiv:1902.08848, 2019.  https://arxiv.org/pdf/1902.08848
  Read for: every former as further structure on the initial CwF.

**Generalised algebraic theories.**

- Cartmell, *Generalised Algebraic Theories and Contextual Categories*, DPhil
  thesis, Oxford 1978.  LaTeX transcription (Lumsdaine et al.):
  https://github.com/peterlefanulumsdaine/cartmell-thesis (ch. 1 is
  `1-gats.tex`; raw OCR in `ocr/ocr.tex`).  Scan:
  https://ncatlab.org/nlab/files/Cartmell-Thesis.pdf
  Read for: §1.6 Definitions 1–3 (pretheory, derivability, theory); §1.3 the
  `Eq`-sort; §1.7 the substitution lemma and stratification; §1.9 models
  ("We neglect the formal definition").
- Cartmell, *Generalised algebraic theories and contextual categories*, APAL
  32, 1986.  https://www.sciencedirect.com/science/article/pii/0168007286900539
  Not obtained (paywalled); the thesis has the same Definitions 1–3.
- Bezem, Coquand, Dybjer, Escardó, *On generalized algebraic theories and
  categories with families*, MSCS 31, 2021.
  https://www.cambridge.org/core/services/aop-cambridge-core/content/view/02459F7C89C72EEA9A1BC296F17B920C/S0960129521000268a.pdf/on_generalized_algebraic_theories_and_categories_with_families.pdf
  Read for: the modern restatement of GATs and their CwF semantics.  Partial.
- nLab, *generalized algebraic theory*.
  https://ncatlab.org/nlab/show/generalized+algebraic+theory

**Theories of signatures.**

- Kaposi, Kovács, Altenkirch, *Constructing Quotient Inductive-Inductive
  Types*, POPL 2019.  https://akaposi.github.io/finitaryqiit.pdf
  Read for: `U` as sort declaration; `Id` at `El` and its largeness; "the first
  argument of Π needs to be small".
- Kaposi, Kovács, *Signatures and Induction Principles for Higher
  Inductive-Inductive Types*, LMCS 16(1), 2020.  https://arxiv.org/abs/1902.00297
  Read for: the strict-positivity sentence; Σ costing no expressiveness.
- Kaposi, Xie, *Second-Order Generalised Algebraic Theories: Signatures and
  First-Order Semantics*, FSCD 2024.
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol299-fscd2024/LIPIcs.FSCD.2024.10/LIPIcs.FSCD.2024.10.pdf
  Read for: ToS⁺ and the subuniverse `U⁺`; "no meaningful notion of
  homomorphism of second-order models"; Σ as packaging.
- Kovács, *Type-Theoretic Signatures for Algebraic Theories and Inductive
  Types*, PhD thesis, ELTE 2022.  https://arxiv.org/pdf/2302.08837
  Read for: the systematic account.  Partial.
- Altenkirch, Kaposi, *Type Theory in Type Theory using Quotient Inductive
  Types*, POPL 2016.  http://www.cs.nott.ac.uk/~psztxa/publ/tt-in-tt.pdf
  Read for: "not a universe, but a base type".

**Second- and higher-order algebraic theories.**

- Fiore, Mahmoud, *Second-Order Algebraic Theories*, MFCS 2010.
  https://arxiv.org/abs/1308.5409
  Read for: second order as terms under bound variables.
- Fiore, Hur, *Second-Order Equational Logic*, CSL 2010.
  https://www.cl.cam.ac.uk/~mpf23/papers/Types/soeqlog.pdf
  Read for: parameterised metavariables.  Partial.
- Arkor, McDermott, *Higher-order algebraic theories*.
  https://www.cl.cam.ac.uk/~na412/Higher-order%20algebraic%20theories.pdf
  Read for: the n-th order definition, `ord(X ⇒ Y)`, the side condition
  `ord(X) < n`, Example 3.12.
- Arkor, *Monadic and Higher-Order Structure*, PhD thesis, Cambridge 2022.
  https://arkor.co/files/Monadic%20and%20Higher-Order%20Structure.pdf
  Read for: ch. 4 in full.
- Arkor, Fiore, *Algebraic models of simple type theories*, LICS 2020.
  https://arxiv.org/pdf/2006.16949
  Read for: k-th order arities.  Partial.

**Representable maps and the semantics of the domain restriction.**

- Uemura, *A General Framework for the Semantics of Type Theory*,
  arXiv:1904.04097, MSCS 2023.  https://arxiv.org/pdf/1904.04097
  Read for: §1 "models may not even form a category"; §4 the representable
  Π-rule; Thm 4.12 and Cor 4.13 on `G` and natural models.
- Uemura, *Abstract and Concrete Type Theories*, PhD thesis, Amsterdam 2021.
  https://pure.uva.nl/ws/files/62028111/Thesis.pdf
  Read for: Remark 3.2.12; ch. 4 intro; §4.6.
- Uemura, *Abstract type theories*, HoTTEST slides, 2020.
  https://www.math.uwo.ca/faculty/kapulkin/seminars/hottestfiles/Uemura-2020-06-17-HoTTEST.pdf
  Read for: "judgments in DTT cannot have hypotheses of the form (X : Type)".
- Bocquet, *External univalence for second-order generalized algebraic
  theories*, arXiv:2211.07487, 2022.  https://arxiv.org/pdf/2211.07487
  Read for: §3, a third convention on order; local finite presentability.
- Bocquet, Kaposi, Sattler, *For the Metatheory of Type Theory, Internal
  Sconing Is Enough*, FSCD 2023.  https://arxiv.org/pdf/2302.05190
  Read for: §2.1, SOGATs without sort equations.  Partial.
- Capriotti, *Models of Type Theory with Strict Equality*, PhD thesis,
  Nottingham 2016.  https://arxiv.org/pdf/1702.04912
  Read for: §§2.5–2.7, the `(U → U) → U` counterexample.
- Isaev, *Algebraic Presentations of Dependent Type Theories*,
  arXiv:1602.08504.  https://arxiv.org/pdf/1602.08504
  Read for: §1.  Partial.
- Voevodsky, *A C-system defined by a universe category*, TAC 30, 2015.
  https://arxiv.org/pdf/1409.7925
  Read for: §§1–2, C-systems from a universe.  Partial.

**Categories with families and universes.**

- Awodey, *Natural models of homotopy type theory*, MSCS 28(2), 2018.
  https://arxiv.org/pdf/1406.3219
  Read for: a type former as a pullback square; the representable map
  `Tm → Ty`.
- Castellan, Clairambault, Dybjer, *Categories with Families: Unityped,
  Simply Typed, and Dependently Typed*, arXiv:1904.00827, 2020.
  https://arxiv.org/pdf/1904.00827
  Read for: CwFs as a GAT.  Partial.
- Coquand, *Canonicity and normalization for Dependent Type Theory*,
  arXiv:1810.09367, 2018.  https://arxiv.org/pdf/1810.09367
  Read for: a Tarski universe on a CwF.
- Palmgren, *On Universes in Type Theory*, in *Twenty-Five Years of
  Constructive Type Theory*, OUP 1998.  https://www2.math.uu.se/~palmgren/universe.pdf
  Read for: Tarski versus Russell; the abstract definition of a universe.
- Luo, *Notes on Universes in Type Theory*, IAS 2012.
  https://www.cs.rhul.ac.uk/home/zhaohui/universes.pdf
- Nordström, Petersson, Smith, *Programming in Martin-Löf's Type Theory*,
  OUP 1990, chs. 19–20.  https://www.cse.chalmers.se/research/group/logic/book/book.pdf
- Dybjer, *Internal Type Theory*, TYPES 1995.
  https://www.cse.chalmers.se/~peterd/papers/InternalTT.pdf
  Not obtained (text extraction failed); the two Dybjer-coauthored papers above
  cover the same ground.
- Hofmann, *Syntax and semantics of dependent types*, 1997.  Not obtained.

---

## 10. Gaps in this survey

- Cartmell 1986 (APAL) was not obtained; all Cartmell quotations are from the
  1978 thesis via the Lumsdaine transcription, whose Definitions 1–3 are the
  same system.  Anything the paper adds over the thesis is unchecked.
- Dybjer 1996 and Hofmann 1997 were not obtained.
- Schroeder-Heister 1984, *A natural extension of natural deduction*, the
  source of "higher-level rules" cited by Gratzer–Sterling and
  Arkor–McDermott, was seen only in abstract.  It is likely the earliest
  statement that rules may have rules as premises and is worth reading in full.
- Not searched: the essentially-algebraic / finite-limit-sketch literature
  (Freyd; Adámek–Rosický) except as cited by Cartmell §1.4; the clan and
  display-map-category literature (Joyal; Taylor) that §15.1 of the core note
  raises as the target generality.
- Whether strict morphisms avoid Capriotti's counterexample was looked for and
  not found addressed anywhere.
