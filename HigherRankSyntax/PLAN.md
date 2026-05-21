# PLAN — Closing `lift_inst_commute`

## State of the formalisation

The library defines a higher-rank binding syntax `Expr Γ` over a `Carrier C`,
together with the renaming functor `⟦ρ⟧ʳ` and two substitution-style walkers
`lift.aux` and `inst.aux`.  The goal is to witness the relative monad structure
on `Expr` (`SyntaxMonad/SyntaxMonad.lean`).  Everything works except one
substitution-composition law.

**Remaining `sorry`.**  `lift_inst_commute` in `Equations.lean:579` (= the "L5"
lemma).  Without it, `comp_lift` (the Kleisli composition law) does not close,
and the relative monad structure remains a proof obligation rather than a
theorem.

**No other open obligations.**  Build is otherwise green; the four fusion
lemmas in the AACMM sense are proved (F1=`Renaming.actExpr.map_comp`,
F2=`subst_after_ren`, F3=`ren_after_subst`, F4=`comp_lift.aux` modulo L5).

## The obstacle — two walkers instead of one

We have two recursive walkers:

* `lift.aux σ τ : Expr (Γ⋈*τ) → Expr (Δ⋈*τ)` for σ : Subst Γ Δ.  Substitution
  with a τ-stack of binders that have already been passed.
* `inst.aux ρ ι τ : Expr ((Δ⋈α)⋈*τ) → Expr (Ξ⋈*τ)` for ρ : Δ →ʳ Ξ,
  ι : Inst α Ξ.  Plugs the α-binder via ι; renames Δ-slots via ρ.

They interact at exactly one place: `lift.aux`'s `.base` case unfolds to a call
to `inst.aux` that threads the τ-stack as a renaming:

```
lift.aux σ τ (apply ((Γ↪ʳ*τ) q) args)
  = inst.aux (Δ↪ʳ*τ) (fun j => lift.aux σ (j.arity::τ) (args j)) [] (σ q)
```

In `comp_lift.aux`'s `.base q` case, this produces

```
lift.aux θ τ (inst.aux (Δ↪ʳ*τ) Λ_σ [] (σ q))
```

— **lift past inst** — which is exactly the statement of `lift_inst_commute`
(L5).  Our four fusion lemmas (F1–F4) handle ren∘ren, lift∘ren, ren∘lift,
lift∘lift, but **none** of them handles lift∘inst.

## Why this differs from AACMM

Allais–Atkey–Chapman–McBride–McKinna ("AACMM", JFP 2021, `papers/allais-et-al/`)
have a *single* generic `Semantics d 𝓥 𝓒` walker — substitution, renaming, and
constructor-by-constructor traversals are all instances of one record.  Their
`Sub²` lemma is proved at the generic `Fusion` level once and instantiated as
needed.  Because there is only one walker, there is no "lift past inst"
combination — it doesn't arise.

Schäfer et al. ("Autosubst", `papers/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf`)
work in untyped λ-calculus over the σ-calculus; their `comp_lift` analogue is a
rewrite system, and their two-level structural recursion (Adams) gives `Sub²`
from `RenSub` and `SubRen`.  They also have a single substitution operation —
no separate `inst`.

**Our two-walker split is structural to our higher-rank binding setting.**
Each `apply p args` node carries arity-indexed children indexed by
`C.Binder α`, so substituting at the α-binder layer is a one-off operation
(inst.aux), distinct from walking past binders that have already been passed
(lift.aux).  AACMM's `Kripke` encoding folds these two into one because their
constructor/variable separation lets the walker dispatch on the head node;
our `Expr` collapses constructor and variable into the same `apply` shape, so
we can't replicate that dispatch.

## What is already done in the framework

In `Renaming.lean`:
* `Renaming.id`, `comp`, `weaken`, `weakenList`, `extend`, `extendList`.
* `extendList_id`, `extend_id`, `extend_comp` (functoriality).
* `extendList_weakenList`, `weakenList_naturality` (naturality of weakening
  with extension).

In `Expr.lean`:
* `Renaming.actExpr` (= `⟦ρ⟧ʳ`), `map_id`, `map_comp` (F1).
* `Expr.η`, `T.map`, `J.map`, `T.map_η` (η-naturality).

In `Subst.lean`:
* `Subst`, `Inst`, `Subst.id`, `comp` (= `∘ˢˢ`), `weaken`, `weakenList`,
  `extend` (= `⇑ˢ`), `extendList` (= `⇑ˢ*`), `act` (= `⟦σ⟧ˢ`).
* `Renaming.toSubst`, `Renaming.preSubst` (= `∘ʳˢ`), `Subst.postRen` (= `∘ˢʳ`).
* `Inst.toSubst` (recently added).
* `Inst.map` (componentwise action of subst on inst).
* `tauSlot`, `XPos`, `classify`, `classify_weakenList`, `classify_tauSlot`.
* `inst.aux`, `lift.aux`, and per-case `@[simp]` unfolders:
  `inst_aux_{ext,base_there,base_here}_eq`, `lift_aux_{ext,base}_eq`.

In `Equations.lean`:
* `extendList_tauSlot`, `subst_extendList_tauSlot`,
  `subst_extendList_weakenList`.
* **F2** `subst_after_ren` (RenSub fusion).
* **F3** `ren_after_subst` (SubRen fusion), via `inst_aux_rename_id` and
  `inst_aux_factor_ren`.
* η-side: `inst_aux_η_tauSlot`, `inst_aux_η`, `inst_aux_η_inv`,
  `lift_aux_η_tauSlot`.
* `unit_left`, `unit_right`, `lift_toSubst` (renamings ↪ substitutions).
* `lift_aux_via_extendList` (LiftFactor: absorb the τ-stack into the subst).
* `lift_aux_nil_apply` (τ=[] specialisation of `lift_aux_base_eq`).
* `inst_aux_as_lift_aux` (recently added — see "Recent attempt" below).
* `lift_inst_commute` (sorried) and `comp_lift.aux` / `comp_lift` (depend on
  L5).

## Recent attempt — `Inst.toSubst` + `inst_aux_as_lift_aux`

Commit `401712c` adds the equation

```
inst.aux ρ ι τ e = lift.aux (ι.toSubst ρ) τ e
```

where `ι.toSubst ρ : Subst (Δ⋈α) Ξ` maps `.here i` to `ι i` and `.there r` to
`η (ρ r)`.  Proof: structural induction on `e`; three cases close via the
per-case unfolders and `inst_aux_η`.

This is a clean equation in its own right but **does not eliminate L5**.
Attempting to rewrite `comp_lift.aux`'s `.base` case with it leaves a nested
`lift.aux θ τ ∘ lift.aux S [] ∘ (σ q)`; reducing via comp_lift's IH would
require fusing two `lift.aux`'s at *differing* stacks (τ and []), which
LiftFactor brings to a common stack only at the cost of *extending* the outer
substitution (`θ ⇑ˢ* τ`), which causes non-termination — see "User
constraints" below.

## User constraints

The user has stated rules that any future attempt must respect:

1. **Never extend or weaken the substitution in recursive calls in walkers or
   in inductive proofs of substitution lemmas.**  Doing so makes the recursion
   diverge — the substitution grows at each step without bound, and no clean
   well-founded measure dominates both `e`-descent and `σ`-extension.  The
   existing walkers respect this: `lift.aux σ τ` carries σ unchanged through
   the recursion; the τ-stack grows, but σ does not.

2. **Recursive calls on substituted images (`σ q`) need their own induction
   principle.**  σ q is not a structural subterm of `apply ((Γ↪ʳ*τ) q) args`.
   Any proof that fuses two walkers via "do one walk, then walk the
   substitution image" must explain how termination is achieved without
   substitution-extension.

3. **The user prefers single explicit theorems over conjunctions in `bundle`
   lemmas**; if a mutual block is needed (e.g. lex on α with `subWf`),
   structure it as in `inst_aux_η` / `inst_aux_η_inv`.

## User's latest hint — fusion lemmas about lift and inst

> "Can you formulate suitable fusion lemmas about lift and inst?"

The framing.  The four fusion lemmas {ren, lift} × {ren, lift} closed
substitution composition for renamings and substitutions.  By analogy, we
might hope to find a set of fusion lemmas involving `inst.aux` such that
L5 (lift∘inst) becomes either a direct corollary or provable from them by
non-circular structural induction.

What we have so far in this family:
* **inst∘ren as a factoring**: `inst_aux_factor_ren` says
  `inst.aux ρ ι τ e = inst.aux 𝟙ʳ ι τ (⟦(ρ⇑ʳα)⇑ʳ*τ⟧ʳ e)`.  Pulls the renaming
  out *in front of* the walk.
* **ren∘inst**: `inst_aux_rename_id` says
  `⟦ρ⇑ʳ*τ⟧ʳ (inst.aux 𝟙ʳ ι τ e) = inst.aux 𝟙ʳ (renamed-ι) τ (⟦(ρ⇑ʳα)⇑ʳ*τ⟧ʳ e)`.
  Commutes renaming past the inst-walker (with ι renamed and the body
  pre-renamed).

What's missing for L5:
* **lift∘inst**: `lift.aux θ τ (inst.aux (Δ↪ʳ*τ) ι [] x) = ???`.

The structure of L5's proof if attempted directly is recorded in the older
notes below — three cases on `x`, the `.there r` case recursing on args
(structurally smaller), the `.here j` case using `subWf` on α, transport
bookkeeping for the general ρ-stack version.

A possibly cleaner approach (not yet tried): formulate a single fusion lemma
that **subsumes both `comp_lift` and `lift_inst_commute`** and prove them by
simultaneous induction.  The statement would generalise comp_lift to allow
an inst-style left-renaming pre-applied to the inner walk.  Worth thinking
about — see "Suggested next thinking" below.

## Suggested next thinking

A future instance could try the following directions, *without writing code*
until the user has approved a direction:

1. **Direct L5 proof via the bundle pattern.**  Mirror `inst_aux_rename_id`'s
   structure: outer `subWf` recursion on α, inner structural recursion on e.
   The `.there r` case is a transport-heavy reshuffling of `lift_aux_base_eq`
   followed by IH at deeper ρ-stack; the `.here j` case uses the outer IH
   at smaller α.  Estimated 150–250 lines of transport plumbing.  The ρ=[]
   instance comp_lift calls has no transports, so a τ=[]-restricted helper
   may be easier than the fully general L5.

2. **Generalised single fusion lemma.**  State a lemma
   `walk-then-walk = walk-of-composed` that has *both* `comp_lift.aux` and
   `lift_inst_commute` as specialisations.  The substitution of the
   composed walk would be `Inst.toSubst`–style with both ι- and σ-data.
   Prove by structural induction on the walked expression e, using IH on
   `args j` (structurally smaller) and the **already-proved** F2/F3 to
   handle the .base case (where σ q appears) without recursing into the
   lemma itself.  This is the AACMM-style fusion at the level of the
   "combined walker".  Promising if it works.

3. **Split var-nodes from constructor-nodes in `Expr`.**  Major refactor —
   make `Expr` a sum of `var (p : Γ ∋ α)` and `apply (head : something)
   (args : ...)`.  Then `inst.aux` collapses: substitution at a var is a
   one-step lookup; constructor nodes carry binders.  This is AACMM's
   structure exactly.  Cost: large refactor across `Expr.lean`, `Subst.lean`,
   `Equations.lean`, `SyntaxMonad.lean`, and `RelativeMonad/Examples.lean`.

## What was learned from the papers

Saving the next instance a re-read.

### Allais–Atkey–Chapman–McBride–McKinna ("AACMM"), JFP 2021

* **Generic semantics record** `Semantics d 𝓥 𝓒` (`src/Generic/Semantics.agda`)
  packages: a value type 𝓥, a computation type 𝓒, a thinning action on 𝓥, a
  variable injection `𝓥 → 𝓒`, and an algebra `⟦d⟧ (Kripke 𝓥 𝓒) σ Γ → 𝓒 σ Γ`.
  Renaming and substitution are both `Semantics`.  Walks are
  `sem : Semantics d 𝓥 𝓒 → (Γ ─Env) 𝓥 Δ → Tm d ∞ Γ → 𝓒 Δ`.

* **Kripke** `Kripke 𝓥 𝓒 [] σ Δ = 𝓒 σ Δ` and
  `Kripke 𝓥 𝓒 (β::Γ) σ Δ = ∀ Θ → Δ ≤ Θ → (β :: Γ) ─Env 𝓥 Θ → 𝓒 σ Θ`.  This is
  the "natural transformation in Δ" encoding of a body-with-free-variables.
  Plays the role of our τ-stack with `lift.aux`'s argument indexed by `τ`.

* **Fusion** (`src/Generic/Fusion.agda`).  A `Fusion d S₁ S₂ S₃ 𝓥ᴿ 𝓒ᴿ envᴿ`
  asserts that running `S₂` after `S₁` equals running `S₃` directly,
  modulo relations on environments and computations.  Generic Sub² is one
  instance.

* **Syntactic fusion** (`src/Generic/Fusion/Syntactic.agda` lines 34–104).
  Ren², RenSub, SubRen, Sub² as four concrete `Fusion` instances.

* **Crucial difference from us**: their `Tm d ∞ Γ` is a free monad over
  the signature functor `⟦d⟧`, with `var x` and `con d` as two separate
  constructors.  Substitution at a variable is direct lookup, no further
  recursion; substitution at `con` is structural recursion with the env
  threaded.  This is what lets `sub₂` close by structural induction on `e`
  alone — no need for an inst-style walker.

### Schäfer–Smolka–Tebbi, "Autosubst" (ITP 2015)

* **Two-level structural recursion (Adams)**, §2.1.  A function defined by
  recursion in both `e` and `σ` simultaneously, lexicographically.
  Closes Sub² for untyped λ-calculus without circularity.

* **σ-calculus rewrite system**.  Equational rules for substitutions:
  `(σ ∘ τ) [s] = τ [σ s]`, `↑ ∘ (s · σ) = σ`, etc.  Confluent and
  normalising.  Their `simp`-set automates substitution reasoning.

* **Crucial difference from us**: their substitutions are first-class
  syntactic objects (cons, shift, comp combinators), not functions.  Allows
  the rewrite system to reason about them without the meta-level
  computation we need.

### Carrier-based higher-rank syntax (our setup)

Not in the literature in this exact form — closest is the McBride school's
treatment of inductive families with binders, but they don't separate
the carrier from the syntax in the way we do.  The two-walker split is a
direct consequence of having `apply p args` collapse variable and
constructor: substitution at a slot p must either (a) plug a binder (the
inst case) or (b) lift through external structure (the lift case).

## Files

* `HigherRankSyntax/Carrier.lean` — the carrier interface.
* `HigherRankSyntax/Shape.lean` — shapes (binding contexts) and ⋈, ⋈*.
* `HigherRankSyntax/Renaming.lean` — Renaming and notation.
* `HigherRankSyntax/Expr.lean` — Expr W-type, η, renaming action ⟦·⟧ʳ.
* `HigherRankSyntax/Subst.lean` — Subst, Inst, the two walkers, all
  categorical operations.
* `HigherRankSyntax/Equations.lean` — fusion lemmas, η-side lemmas,
  comp_lift, lift_inst_commute (sorried).
* `HigherRankSyntax/SyntaxMonad/SyntaxMonad.lean` — the relative-monad
  witness; uses comp_lift.

## Reference materials

* `papers/allais-et-al/` — JFP 2021 paper and Agda formalisation.
  Key files: `src/Generic/Semantics.agda`, `src/Generic/Fusion.agda`,
  `src/Generic/Fusion/Syntactic.agda`, `src/Data/Environment.agda`.
* `papers/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf` — §2.1 on two-level
  structural recursion; §3 on the σ-calculus rewrite system.

## Verification

After any attempt:

* `lake build HigherRankSyntax` succeeds with **no remaining `sorry`**.
* `SyntaxMonad/SyntaxMonad.lean` typechecks: the relative monad on `Expr` is
  a closed term.
* No new `partial def`, `noncomputable def`, or `cast`-based workarounds.
