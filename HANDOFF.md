# Handoff

🎉 The substitution commuting square is **done**. `act_interchange` and its
machinery in `HigherRankSyntax/HigherRankSyntax/Interchange.lean` are fully
proven, termination and all — no `sorry`, no errors.

## Repo state

- Branch: `diamond-new`.
- `lake build HigherRankSyntax` is green. `Interchange` builds `✔` (no
  `sorry`, no `⚠`).
- If `lake build` ever dies with `couldn't find value of ELAN_HOME` /
  `Operation not permitted`, that is a macOS TCC / Full Disk Access issue, NOT
  a Lean error — restart resolves it. The Lean LSP (`lean_diagnostic_messages`,
  `lean_goal`) is the fast way to see errors/goals, but it can show stale
  goals mid-elaboration in the slow `mutual` block; trust a full `lake build`.

## What got built

- `act_ap_depth`: proven.
- `act_interchange.aux`: all five head branches proven; mutual with the
  companion `act_interchange.subst`, also fully proven.
- `act_interchange` wrapper: proven (the `Θ = nil`, `Φ = nil` instance; the
  consumer is `act_comp`).
- New file `ListArity.lean` holds the termination measures:
  - `ListArity C` (was `DomMeasure`), `ListArity.Lt` (was `DomLt`; `.step`,
    `.acc_singleton`, `.wf`), `SlotAt.subArity` (was `subWitness`),
    `ListArity.Lt.of_slot` (slot → singleton descent).
  - `ListArity.Pair C`: opaque unordered pair of domains (`structure` over
    `Sym2 (ListArity C)`, constructor `ofSym2`), well-founded via
    `Sym2.GameAdd` + `WellFounded.sym2_gameAdd`. API: `mk`, `lt_left`,
    `lt_right`, `lt_swap`. **`Sym2` appears only in this file** — switching to
    `Multiset.IsDershowitzMannaLT` later is confined here.
- `Subst.lean`: imports `ListArity`; Greek cleanup (`pre/dom/cod → Γ/Δ/Ξ`,
  depth `τ → Φ`); `LeftMiddleRight` constructor comments corrected
  (left = `Γ` prefix, middle = `Δ` domain, right = `Ξ` depth).

## The termination measure

Both mutual functions use the lexicographic measure
`(ListArity.Pair.mk ⟨A.toList⟩ ⟨B.toList⟩, (⟨_, e⟩ : Σ Γ, Expr Γ))`:
- `aux`: `A = Δ` (σ-domain), `B = Ψ` (κ-domain).
- `subst`: `A = Ψ` (θ-domain), `B = Λ` (κ-domain).

Each firing replaces one domain by the fired slot's singleton `⌊β⌋`
(`ListArity.Lt`-smaller) and keeps the other; the action↔instantiation role
swap at `aux.left→middle` is absorbed by the unordered `Sym2`. Per-argument
recursions keep the pair and shrink the `Expr` (`Expr.Subterm`).

`decreasing_by` is written as one `·` bullet per goal (no `all_goals`/`first`).
Bullet order is NOT source order — read each goal off the LSP/build. Shapes:
- per-argument: `exact .right _ (.of_arg x args _)`
- κ fires (slot `z`): `exact .left _ _ (ListArity.Pair.lt_right (.of_slot z))`
- σ fires (slot `w`, swap): `exact .left _ _ (ListArity.Pair.lt_swap (.of_slot w))`

## Lesson: the `Eq.Prod` / `lean.invalidField` trap

Writing the fully-qualified `Prod.Lex.right` / `Expr.Subterm.of_arg` made Lean,
when the bullet's expected type momentarily appeared as a coherence equality
`Expr X = Expr Y`, fall into field-notation resolution — projecting field
`Prod` off a term of the `Eq`-headed type, i.e. looking up `Eq.Prod` →
`Invalid field 'Prod'`. **Fix: leading-dot notation** (`.right`, `.left`,
`.of_arg`, `.of_slot`), which resolves the constructor purely from the expected
type's namespace and never tries the spurious field projection. The only names
that must stay qualified are `ListArity.Pair.lt_right`/`lt_swap` — their result
type is `Sym2.GameAdd`-headed, so `.lt_right` would look for
`Sym2.GameAdd.lt_right`.

## Working rules (project `CLAUDE.md` is canonical)

- Idiomatic, human Lean. No `show`/`change`; exploit defeq via
  `convert`/`exact`/`apply`/`calc`. One `·` bullet per subgoal; no
  `all_goals first`, no `refine ?_ … obtain … exact step _ _` scaffolding.
- `Proper` mismatches → `Subsingleton.elim`; act-depth mismatches →
  `Subst.act_irrel`. `rw` does not see through `Shape.nil ⋈ X = X` or `⋈`
  associativity; use `convert`.
- Never copy from `Equations.lean`/`Equations2.lean`.
- ASK rather than work around. Report at the first failure; never disable the
  sandbox. Leave failing attempts in place — do NOT bury them under `sorry`.
- Commits need explicit approval; never push without being asked.
