# Handoff

This file is for the next Claude instance picking up `act_interchange.aux`
in `HigherRankSyntax/HigherRankSyntax/Interchange.lean`.

## Repo state

- Branch: `diamond-new`.  Working tree clean.
- `lake build HigherRankSyntax` green (two open `sorry`s — see "Open
  work" below).
- Most recent commit: `b2c3cc3` (wip: w:Θ branch complete) — possibly
  amended to fold in a smaller `Subst.act` form in case left→right
  line 85–87.  Read the diff before assuming.

## The theorem

`act_interchange.aux` (Interchange.lean ~ line 47): acting by `σ`
commutes with instantiating `κ` pushed forward along `σ`.  The proof
is `match e with | .ap (α := β) x args =>`, then `head_cases x with
z`, splitting into five branches by where the head slot lives in
`Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ`:

| head_cases path        | slot           | role           | status     |
|------------------------|----------------|----------------|------------|
| `right`                | `z : Φ`        | both pass      | done       |
| `middle`               | `z : Ψ`        | κ fires        | **sorry**  |
| `left → right`         | `w : Θ`        | both pass      | done       |
| `left → middle`        | `w : Δ`        | σ fires        | **sorry**  |
| `left → left`          | `w : Γ`        | both pass      | done       |

## Auxiliary lemmas

- `act_ap_depth` (Interchange.lean line 35) is **sorry**.  Generalises
  `act_ap_right` from "slot at depth top" to "slot in an embedded
  telescope `Φ` inside depth `Λ ⋈ Φ ⋈ Ρ`".  The three done branches
  use it as a black box.  A plan for it lives in
  `~/.claude/plans/lazy-weaving-cascade.md`.

- `Subst.act_irrel` (Interchange.lean line 24): two `Subst.act`s on
  the same shape with different `Proper` witnesses agree.  Bridges
  act-depth witness mismatches.

- `Proper.compose_inl_inl` (ProperTele.lean line 391): `inl` past a
  composite equals iterated `inl` (by `rfl`).  Use to convert between
  `Proper.inl (Γ⋈Δ⋈Θ⋈Ψ) (Proper.inl (Γ⋈Δ⋈Θ) …)` (double-inl, past Ψ
  then past Φ) and `Proper.inl (Γ⋈Δ⋈Θ) …` past `Ψ⋈Φ` (single-inl).

- `pushforward σ κ` (Interchange.lean line 15): `σ.act ∘ κ` as a
  Subst.  Pushes `κ` along `σ`.

## Project rules (READ `HigherRankSyntax/CLAUDE.md` BEFORE ANY EDIT)

The rules below summarise; the canonical source is `CLAUDE.md`.

- **No `rw` on shape / `Proper` mismatches.**  `rw`'s syntactic
  matcher does not see through `Shape.nil ⋈ X = X` or `(X⋈Y)⋈Z =
  X⋈(Y⋈Z)`, and witness-comparison is hopeless.  Use `convert` +
  `Subsingleton.elim` / `Subst.act_irrel`.  `rw` is fine for clean
  syntactic rewrites (e.g. `rw [act_ap_left]`).

- **No `show` / `change`.**  Exploit defeq through `convert` /
  `exact` / `apply` / `calc`.

- **No `<;>` or `try` cleverness.**  Always open a `·` bullet for
  each subgoal and prove it there.

- **Never copy from `Equations.lean` / `Equations2.lean`** (retired
  references).  Derive from the current obligation.

- **Declare-and-halt.**  Before each tactic, state the single expected
  outcome.  Run it, compare.  Any deviation → stop and surface the
  verbatim outcome; no second attempt.

- **Do NOT use `cow`.**  It is a read-only marker showing the
  recursive call's shape — already in place in the sorry'd branches.
  The branch must end aiming at `act_interchange.aux σ κ (Φ ∷
  i.arity) (args i)` directly, not `cow i`.

- **Read-only git inspection ok; mutations need explicit approval.**

- **Never trigger a Mathlib source compile** — halt and let Andrej
  run `lake exe cache get` if needed.

## Strategies used in the done branches

### Two-step: write large, then shrink

Write the proof with **everything explicit** first (named args, `@`
forms, type ascriptions, `inferInstance` for instance args).  Once
green, shrink incrementally: replace each explicit value with `_` or
drop a named arg, build, keep if green, restore if red.

Concrete shrink dimensions in order:

1. `inferInstance` → `_`.
2. `@F a b c …` → `F (binder := value) …` (named args).
3. `@F C Γ Δ …` → drop the leading `C` first; then Δ etc.
4. Drop a named arg entirely (`(Ω := value)`).

Each remaining pin after shrinking is **load-bearing** — its removal
re-introduces a metavariable somewhere.

### Enumerate subgoals before proving them

A `convert … using N` produces an unknown number of subgoals.  Don't
assume.  After the `convert`:

1. Add **one** `· done` bullet.  Build.  Lean either prints the
   single open goal or "No goals to be solved" (= zero subgoals).
2. To check there are no MORE than N subgoals, add N bullets `· done`
   and build — the (N+1)th would error as "No goals".

Sometimes the easier preliminary is `all_goals sorry` to confirm
the convert accepted at all, then probe the count.

### Idioms

- **κ fires on prefix-side head**: `rw [act_ap_left]` (or `convert
  act_ap_left σ Φ w _ using 2` if σ's decomposition is ambiguous).
- **σ fires on depth-side head**: `act_ap_depth` (still sorry).
- **σ fires on depth-top head (`ι₂ x`)**: `act_ap_right`.
- **σ fires on dom-side head**: `act_ap_middle`.

### Proper-witness mismatches

After convert, a leftover subgoal of the form
`Proper.compose A B = Proper.compose A' B'` (with A,A',B,B' defeq) is
closed by `apply Subsingleton.elim` (since `Proper` is `Subsingleton`).

A leftover subgoal of the form `f e = f e'` where `f` is `(σ.act
shape)` and the e's differ only in their act-depth witness is closed
by `congr 1; apply Subst.act_irrel`.

### The decomposition-ambiguity workaround

`(pushforward σ κ).act Φ` cannot be elaborated by Lean on its own —
`Subst.act` needs to split pushforward's codomain `Γ⋈Ξ⋈(Θ⋈Ω)` as
`Γ_act ⋈ Ξ_act`, and Lean's first-order unifier can't pick.  Inside a
`convert`, named-args pin it:

```lean
Subst.act (Γ := Γ ⋈ Ξ ⋈ Θ) (Ξ := Ω) (pushforward (Ω := Θ ⋈ Ω) σ κ) Φ
```

The `(Ω := Θ ⋈ Ω)` on pushforward pins **its** own codomain
decomposition; without it pushforward's implicits stay metavariables.

If a wrapper for an inner `.act` appears in a position where the
surrounding `convert` has enough context to recover the wrapper from
the goal's structure, then `convert congrArg _ … using N` works
(case left → left line 93 is the model).  Otherwise spell it out.

## Compose-coherence lemmas (likely needed for `act_ap_depth`)

In `ProperTele.lean` under the local `Proper.compose` instance:

- `compose_inr_inr S T Γ x` (line 371): inr through compose of an
  inr-tagged slot.
- `compose_inr_inl S T Γ x` (line 378): inr through compose of an
  inl-tagged slot.
- `compose_inl_inl S T Γ x` (line 391, by `rfl`): inl past compose
  factors as inl past T composed with inl past S.

The strategy for `act_ap_depth` (sketched in the plan file): the
head `Proper.inl (Γ⋈Δ⋈Λ⋈Φ) (Proper.inr (Γ⋈Δ⋈Λ) z)` rewrites (via
`compose_inr_inl` for outer `(Λ⋈Φ)⋈Ρ` plus `compose_inr_inr` for
inner `Λ⋈Φ`) to `Proper.inr (Γ⋈Δ) (Proper.inl (Λ⋈Φ) (Proper.inr Λ
z))`.  Then `act_ap_right` fires.  Subgoals enumerate via bullets
afterwards.

## Bucket list (in priority order)

1. `act_ap_depth` (Interchange.lean line 35).  Plan file:
   `~/.claude/plans/lazy-weaving-cascade.md`.
2. `case middle` (z : Ψ).  κ fires.  HANDOFF older notes (in git
   history) sketched: `rw [act_ap_middle]`, then recursive call on
   `(κ z)` with `Θ := Θ ⋈ Ω`, `Ψ := ⌊β⌋`, `Ω := Φ`, `e := κ z`.
3. `case left → middle` (w : Δ).  σ fires.  Mirror of `middle`.

## How to talk to Andrej

- Direct answers.  Terse.  Show code/equations, not paragraphs of
  prose.
- No "shall I…?" closers.  Wait for an explicit imperative ("go",
  "execute", "approve", "do it") before non-trivial action.
- He'll review every commit himself.  Do not commit without an
  explicit `commit` from him.
- If he tells you you weren't authorised: stop, do not auto-revert,
  leave the change in place.
- Don't restate what you've done — he reads the diff.
- He uses scope-bearing modifiers carefully ("only" / "also" /
  "just").  Mirror that.  Prefer active voice.

## Key files

- `HigherRankSyntax/HigherRankSyntax/Interchange.lean` — main file.
- `HigherRankSyntax/HigherRankSyntax/Dispatch.lean` — `act_ap_left`,
  `_middle`, `_right`, `head_cases` macro.
- `HigherRankSyntax/HigherRankSyntax/Subst.lean` — `Subst.act`, `threeway`.
- `HigherRankSyntax/HigherRankSyntax/ProperTele.lean` — `Proper`
  class, `compose`, coherence lemmas.
- `HigherRankSyntax/HigherRankSyntax/Shape.lean` — `Shape`, `⋈`,
  `Shape.nil`, `∷`.
- `HigherRankSyntax/CLAUDE.md` — project rules.  **Read first.**
- `~/.claude/plans/lazy-weaving-cascade.md` — current plan for
  `act_ap_depth`.
