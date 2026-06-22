# Handoff

Picking up the termination of `act_interchange` in
`HigherRankSyntax/HigherRankSyntax/Interchange.lean`.

## Repo state

- Branch: `diamond-new`. Most recent commit: `9fafd8e`.
- Does NOT build clean: `act_interchange.aux`'s `decreasing_by` has one
  failing bullet (line ~230), left in place at the stuck point. Everything
  else in the file is complete and error-free.
- `lake build` currently hits a macOS permission error
  (`couldn't find value of ELAN_HOME` / `Operation not permitted`) — that is
  a TCC / Full Disk Access issue, NOT a Lean error. Do not misread it. The
  Lean LSP (`lean_diagnostic_messages`, `lean_goal`) works and is the way to
  see errors/goals.

## What is done

- `act_ap_depth` (Interchange.lean): proven (no longer `sorry`).
- `act_interchange.aux`: all five head branches proven; mutual with the
  companion `act_interchange.subst`, which is fully proven.
- `act_interchange` wrapper: proven.
- Termination measures extracted into a new file `ListArity.lean`:
  - `ListArity C` (was `DomMeasure`), `ListArity.Lt` (was `DomLt`, with
    `.step`/`.acc_singleton`/`.wf`), `SlotAt.subArity` (was `subWitness`),
    `ListArity.Lt.of_slot` (slot → singleton descent).
  - `ListArity.Pair C`: opaque unordered pair of domains (`structure`
    wrapping `Sym2 (ListArity C)`, constructor `ofSym2`), well-founded via
    `Sym2.GameAdd` + `WellFounded.sym2_gameAdd`. API: `mk`, `lt_left`,
    `lt_right`, `lt_swap`. **`Sym2` is named only inside this file** — a
    future switch to `Multiset.IsDershowitzMannaLT` is confined here.
- `Subst.lean`: imports `ListArity`; `Subst.act`'s termination uses the
  relocated names. Greek cleanup done (`pre/dom/cod → Γ/Δ/Ξ`, depth `τ → Φ`);
  `LeftMiddleRight` constructor comments corrected (left = `Γ` prefix,
  middle = `Δ` domain, right = `Ξ` depth).

## The measure

Both mutual functions use the lexicographic measure
`(ListArity.Pair.mk ⟨A.toList⟩ ⟨B.toList⟩, (⟨_, e⟩ : Σ Γ, Expr Γ))`:
- `aux`: `A = Δ` (σ-domain), `B = Ψ` (κ-domain).
- `subst`: `A = Ψ` (θ-domain), `B = Λ` (κ-domain).

Each firing replaces one domain by the fired slot's singleton `⌊β⌋`
(`ListArity.Lt`-smaller) and keeps the other; the action↔instantiation role
swap at `aux.left→middle` is absorbed by the unordered `Sym2`. Per-argument
recursions keep the pair and shrink the `Expr`.

`decreasing_by` proof shapes:
- per-argument: `exact Prod.Lex.right _ (Expr.Subterm.of_arg x args _)`
- κ fires (slot `z`): `exact Prod.Lex.left _ _ (ListArity.Pair.lt_right (ListArity.Lt.of_slot z))`
- σ fires (slot `w`, swap): `exact Prod.Lex.left _ _ (ListArity.Pair.lt_swap (ListArity.Lt.of_slot w))`

`subst`'s `decreasing_by` is complete as four bullets in the order
`[per-arg, per-arg, κ-fire, per-arg]` (NOT source order).

## The open blocker (`aux.decreasing_by`)

`aux` produces 8 goals: per-argument descents, the κ/σ firing descents, and
at least one **type-coherence** goal
`Expr (Γ⋈Ξ⋈(Θ⋈Ω⋈Φ)) = Expr (Γ⋈Ξ⋈Θ⋈Ω⋈Φ)` (the dependent `Expr` index
re-associates at the σ-fire cross-call to `subst`; defeq by `⋈` associativity).

With positional `·` bullets the goals are interdependent: bullet 5 (line 230)
presents as a per-argument goal when it holds `rfl`, but as the coherence
equality when it holds `Prod.Lex.right` — i.e. whether/how an earlier bullet
closes shifts which goal a later bullet faces. So positional bullets cannot
stably hit each goal. This is exactly why `Subst.act` and the removed Codex
code used an order-independent `first | …` combinator.

Unresolved design point for Andrej: bullets (his stated preference, but they
do not stably target these interdependent goals) vs. one order-independent
closer (no `all_goals`/`try` — just `first` over the handful of clean
closers: the two descents and the coherence `rfl`/`congrArg Expr rfl`).

## Working rules (project `CLAUDE.md` is canonical)

- Idiomatic, human Lean. No `show`/`change`; exploit defeq via
  `convert`/`exact`/`apply`/`calc`. Bullets per subgoal; the user dislikes
  `all_goals first` and `refine ?_ … obtain … exact step _ _` scaffolding.
- `Proper` mismatches → `Subsingleton.elim`; act-depth mismatches →
  `Subst.act_irrel`.
- `rw` does not see through `Shape.nil ⋈ X = X` or `⋈` associativity; use
  `convert`.
- Never copy from `Equations.lean`/`Equations2.lean`.
- ASK rather than work around. Report at the first failure; do not iterate
  hacks. Never disable the sandbox. Leave failing attempts in place at the
  stuck point — do NOT bury them under `sorry`.
- Commits need explicit approval; never push without being asked.
