# PLAN — Substitution composition via four fusion lemmas

## Goal

Close the remaining `sorry` (`lift_inst_commute` in `Equations.lean:381`) and
discharge `comp_lift` in `SyntaxMonad.lean`, completing the relative-monad
structure on `Expr`.  The path: replicate the Allais–Atkey–Chapman–McBride–
McKinna (henceforth "AACMM") discipline of proving four fusion lemmas in
dependency order, adapted to our higher-rank carrier-based syntax.

## Why this approach

We hit a real obstacle in the direct attempt at `lift_inst_commute`: the
`.there` case produces a nested `inst.aux` whose head depends on `θ r`,
demanding a substitution-style commutation as a sibling.  This is exactly
the "snake-eating-its-tail" that the AACMM framework resolves by sequencing
proofs:

```
Ren²  →  RenSub  ─┐
                  ├→  Sub²
       SubRen  ───┘
```

The `.there` case in `Sub²` does not recurse into another `Sub²`; it uses
the *already-proved* `RenSub` and `SubRen` to fold the inner structure
into a single substitution.  Cross-check: Schäfer et al. (Autosubst §2.1)
describes the same dependency as a "two-level structural recursion"
(Adams).

## Vocabulary translation

| AACMM                                 | Ours                                   |
|---------------------------------------|----------------------------------------|
| `Tm d`                                | `Expr`                                 |
| `Var σ Γ`                             | `Γ ∋ α`                                |
| `Thinning Γ Δ`                        | `Renaming Γ Δ` (`Γ →ʳ Δ`)              |
| `(Γ ─Env) (Tm d ∞) Δ`                 | `Subst Γ Δ`                            |
| `Kripke 𝓥 𝓒 Δ σ`                     | implicit in `lift.aux` τ-stack         |
| `Ren = Semantics _`                   | `Renaming.actExpr` (`⟦ρ⟧ʳ`)            |
| `Sub = Semantics _`                   | `lift.aux σ`                           |
| `Ren² : Fusion d Ren Ren Ren _ _ _`   | `Renaming.actExpr.map_comp` **DONE**   |
| `RenSub : Fusion d Ren Sub Sub _ _ _` | **F2 below — TO PROVE**                |
| `SubRen : Fusion d Sub Ren Sub _ _ _` | **F3 below — TO PROVE**                |
| `Sub² : Fusion d Sub Sub Sub _ _ _`   | **F4 below — TO PROVE = `comp_lift`**  |

Idiosyncratic to us, with no direct AACMM counterpart:

- **Higher-rank binders.**  Each `ext` adds a *set* of binders indexed by
  `C.Binder α`, not a single variable.  Our `lift.aux` already carries a
  `τ : List C.Arity` stack for this; AACMM's `Kripke` does the same role.
- **`Inst α Γ`.**  A "partial substitution" at one α-binder.  Not in AACMM.
  Likely treated either as a special `Subst` (η on non-target slots) or
  inlined.  Decision deferred to Stage 3.

## Strategy decisions

**No generic `Semantics` record at this stage.**  We have two semantics
(Ren, Sub) and one syntax (Expr).  Building the AACMM abstraction would
add infrastructure without payoff.  We state F2/F3/F4 directly as concrete
lemmas about `Renaming.actExpr` and `lift.aux`.  If a third "semantics"
ever appears (printing, NbE, …), revisit then.

**Restate `comp_lift`'s proof rather than derive `lift_inst_commute`.**
Currently `comp_lift.aux`'s `.base` case invokes L5.  We'll rewrite it to
use F2/F3 + `inst_aux_factor_ren` (already proved) directly.  L5 becomes
either a derived corollary or deleted.

## The lemmas, stated

### F1.  Renaming ∘ Renaming — DONE

`Renaming.actExpr.map_comp` in `Expr.lean`:

```
⟦ σ ∘ʳ ρ ⟧ʳ e = ⟦ σ ⟧ʳ (⟦ ρ ⟧ʳ e)
```

### F2.  Substitution after renaming — TO PROVE

```
lift.aux σ τ (⟦ ρ.extendList τ ⟧ʳ e) = lift.aux (ρ ʳ∘ˢ σ) τ e
```
for `ρ : Γ →ʳ Γ'`, `σ : Subst Γ' Δ`, `τ : List C.Arity`,
`e : Expr (Γ ⋈* τ)`.  The composition `ρ ʳ∘ˢ σ = Renaming.preSubst ρ σ`
is already defined in `Subst.lean`.

Proof: structural induction on `e` via `Expr.Subterm`.  No F1 needed in
the body (we already have `actExpr` push-through).  Cases close by IH
on `args j`.  Estimated ~40 lines.

### F3.  Renaming after substitution — TO PROVE

```
⟦ ρ.extendList τ ⟧ʳ (lift.aux σ τ e) = lift.aux (σ ˢ∘ʳ ρ) τ e
```
for `σ : Subst Γ Δ`, `ρ : Δ →ʳ Δ'`.  The composition
`σ ˢ∘ʳ ρ = Subst.postRen σ ρ` is already defined in `Subst.lean`.

Proof: structural induction on `e`.  The `.base` case produces
`⟦ρ.extendList τ⟧ʳ (inst.aux α (Δ↪ʳτ) Λ [] (σ q))`, which we close by
**F1** (renaming-composition) plus the already-proved `inst_aux_factor_ren`
to pull the outer renaming through `inst.aux`.  Estimated ~60 lines.

### F4.  Substitution ∘ Substitution — TO PROVE (= `comp_lift`)

```
lift.aux θ τ (lift.aux σ τ e) = lift.aux (σ ˢ∘ˢ θ) τ e
```
for `σ : Subst Γ Δ`, `θ : Subst Δ Ε`.  The composition
`σ ˢ∘ˢ θ = Subst.comp σ θ` is already defined in `Subst.lean`.

Proof: structural induction on `e`.  The `.base` case produces
`lift.aux θ τ (inst.aux α_h (Δ↪ʳτ) Λ [] (σ q))`.  Here we invoke
**F3** to handle the outer `lift.aux θ τ` past the `inst.aux`-renaming
composition, reducing it to a single `lift.aux` on `σ q`, then close by
the IH.  The `.there` snake-eating-its-tail is broken because we use
F3 (already proved), not F4 recursively.  Estimated ~80 lines including
glue.

## Sequencing

1. **F2.**  New lemma in `Equations.lean`, placed after
   `subst_extendList_weakenList` and before
   `inst_aux_factor_ren`.
2. **F3.**  New lemma in `Equations.lean`, after F2.
3. **Rewrite `comp_lift.aux`** to use F3 in its `.base` case, eliminating
   the dependence on `lift_inst_commute`.
4. **Delete or rederive `lift_inst_commute`** depending on whether any
   downstream caller still needs it.  (Currently only `comp_lift.aux`
   uses it.)

Each step is a separate commit; build must be green between them.

## Concrete first step

Prove F2.  Open `Equations.lean`, insert after line ~60 (after
`subst_extendList_weakenList`):

```lean
private theorem subst_actExpr {C : Carrier} :
    ∀ {Γ Γ' Δ : Shape C} (ρ : Γ →ʳ Γ') (σ : Subst Γ' Δ)
      (τ : List C.Arity) (e : Expr (Γ ⋈* τ)),
      lift.aux σ τ (⟦ ρ.extendList τ ⟧ʳ e)
        = lift.aux (ρ ʳ∘ˢ σ) τ e
```

Termination by `(⟨Γ ⋈* τ, e⟩ : Σ Γ, Expr Γ)` via `Expr.Subterm.of_arg`.
The `XPos.ext` case closes by IH at deeper τ.  The `XPos.base` case
unfolds `lift.aux` via `lift_aux_base_eq` on both sides; the slots
agree by `ρ.extendList τ ((Γ↪ʳτ) q) = (Γ'↪ʳτ) (ρ q)` (an existing
`Renaming.extendList_weakenList`); the `inst.aux` outer structures
match by `congr` + funext + IH.

Build after F2.  Pause and re-evaluate before F3.

## Open questions to resolve during execution

1. **Statement form for F3 / F4.**  Whether `τ` is universally
   quantified or specialised to `[]` (= `Subst.act`).  Try generic
   first; specialise if the proof gets ugly.
2. **`Inst` vs `Subst` correspondence.**  After F4 is done: do we
   need to formally identify `inst.aux α 𝟙ʳ ι []` with a particular
   `Subst.act σ_ι`?  Probably not — `inst_aux_factor_ren` already
   gives us the necessary fusion in our codebase.
3. **`subst_after_ren` vs `Renaming.preSubst` lookup form.**  Two
   plausible statements: with `(ρ ʳ∘ˢ σ)` (composed) or with
   pointwise `σ ∘ ρ`.  Pick whichever simp-rewrites cleanly.
4. **Naming.**  Final names for F2/F3 in our codebase.  AACMM uses
   `RenSub`, `SubRen`; we may prefer `subst_after_rename`,
   `rename_after_subst`, or similar.  Decide just before committing.

## What we already have (assets)

In `Renaming.lean`:
- `Renaming.actExpr.map_comp` (= F1).
- `Renaming.extendList_weakenList` (slot-level composition under
  `extendList`).

In `Subst.lean`:
- `Renaming.preSubst`, `Subst.postRen`, `Subst.comp`, `Subst.under`,
  `Subst.extendList`, `Inst.map` — all the composition operations
  named.
- `lift.aux`, `inst.aux` walkers and their per-case `@[simp]` unfolders
  (`lift_aux_ext_eq`, `lift_aux_base_eq`, `inst_aux_ext_eq`,
  `inst_aux_base_there_eq`, `inst_aux_base_here_eq`).

In `Equations.lean`:
- `subst_extendList_tauSlot`, `subst_extendList_weakenList`
  (substitution-side composition).
- `inst_aux_factor_ren` (factor a renaming out of `inst.aux`).
- `lift_aux_via_extendList` ("LiftFactor": absorb the lift-stack into
  the substitution) and `lift_aux_nil_apply` (τ=[] specialisation).

These together likely cover most of what the proofs of F2/F3/F4 need.

## Verification

After each lemma:
- `lake build HigherRankSyntax` succeeds with no new `sorry`.

Final:
- `comp_lift` no longer relies on `lift_inst_commute`.
- `lift_inst_commute` is either deleted or stated as a one-line
  corollary of F4.
- `SyntaxMonad.SyntaxMonad` definition closes — the relative monad on
  `Expr` is fully witnessed.
- A brief expository update to the `README.md` in
  `HigherRankSyntax/HigherRankSyntax/` reflecting the cleaner picture.

## Status checkpoint

Updated after several execution steps.  Commits on the `action` branch:

* `044b3df` — LiftFactor (`lift_aux_via_extendList`).
* `21acb44` — **F2** (`subst_after_ren`): substitution after renaming.
* `66c2816` — `inst_aux_rename_id` + `Renaming.weakenList_naturality`.
* `da28a64` — **F3** (`ren_after_subst`): renaming after substitution.

The only remaining `sorry` is `lift_inst_commute` (Equations.lean:564),
unchanged from before.

## Discovery during execution

The `.base` case of `comp_lift.aux` *still* needs a lift-past-inst
lemma (= `lift_inst_commute`) even with F2 and F3 in hand, because
after `lift_aux_base_eq` we get
`lift.aux θ τ (inst.aux α_h (Δ↪ʳτ) Λ_σ [] (σ q))` on the RHS, and
neither F2 nor F3 handles "lift past `inst.aux`" directly.  F3 handles
"renaming past `lift.aux`", not "lift past `inst.aux`".

So the four-fusion-lemma framing buys us less than I'd hoped for our
specific syntax.  The `lift_inst_commute` lemma is still load-bearing.

## What's left

**`lift_inst_commute` — L5.**  Statement currently keeps the ρ-generalised
form with `extList_append` transports (Equations.lean:550–564).  Proof
needed.

The bundle-pattern approach (analogous to `inst_aux_rename_id` and
`inst_aux_η_bundle`) is the right structure:

1. `lift_inst_commute_inner α (ih_α : ∀ j : Binder α, L5 at j.arity) ...`
   — does structural recursion on `e` via `Expr.Subterm`.
2. `lift_inst_commute` — wraps with `C.subWf.induction` on α.

For the inner proof's cases:

* **XPos.ext.**  By IH at deeper ρ on args + transport bookkeeping
  (Expr.apply_transport, tauSlot_transport).
* **XPos.base, `.there r`.**  By IH at deeper ρ on args + transport
  bookkeeping (Expr.apply_transport, weakenList_transport).
* **XPos.base, `.here j`.**  By `ih_α` at j.arity + transport bookkeeping.

Needed auxiliary lemmas (none yet in the codebase):

- `Expr.apply_transport`: `h ▸ Expr.apply p args = Expr.apply (h ▸ p)
  (fun j => congrArg (·⋈j.arity) h ▸ args j)`.  Provable by `cases h`.
- `tauSlot_transport_extList_append`: `extList_append Δ (ta++β::tb) τ ▸
  tauSlot (Δ⋈*τ) ta β tb i = tauSlot Δ ta β (tb ++ τ) i`.  Provable by
  induction on `ta`.
- `weakenList_transport`: `extList_append Δ ρ τ ▸ ((Δ⋈*τ↪ʳρ) ((Δ↪ʳτ) p))
  = (Δ↪ʳ(ρ++τ)) p`.  Provable by induction on ρ.

Estimated work: ~150–250 more lines, mostly transport plumbing.

## Cleanup todo (deferred to after L5)

- Remove `CoeFun` on `Subst` — `Subst` is `def Subst := ∀ {α}, _ → _`,
  already a function type; the `CoeFun` adds nothing.

## Reference materials

- `papers/allais-et-al/` — JFP 2021 paper and Agda formalisation.
  Key files: `src/Generic/Semantics.agda`,
  `src/Generic/Fusion.agda`, `src/Generic/Fusion/Syntactic.agda`,
  `src/Data/Environment.agda`.  §8.3 of the paper gives the
  conceptual story; `Syntactic.agda` lines 34–104 give the
  concrete four fusion lemma derivations.
- `papers/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf` — §2.1
  describes the same two-level structural recursion (Adams) and the
  σ-calculus rewrite system, which is exactly the four fusion lemmas
  in equational form.
