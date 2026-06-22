# Handoff: `act_interchange.aux`, the `case left / case right` branch

(Previous handoff content for the `endomaps` Shape-migration session is in git
history; this replaces it for the current `diamond-new` work.)

## Where we are

File: `HigherRankSyntax/HigherRankSyntax/Interchange.lean`.
Theorem: `act_interchange.aux` (line ~47). We are filling the last open
rebuild branch of the `.ap` case.

`act_ap_depth` (line ~35) is still `sorry` and is assumed as a black box for
this work.

## The proof skeleton

After `match e with | .ap x args =>`, `head_cases x with z` splits the head into
`right` / `middle` / `left`. The slot lives in the depth `Γ ⋈ Δ ⋈ Θ ⋈ Ψ ⋈ Φ`:

| head_cases path | slot | role | status |
|---|---|---|---|
| `right` | `z : Φ` | rebuild (both acts pass through) | **done** |
| `middle` | `z : Ψ` | κ fires | `sorry` |
| `left` → `right` | `w : Θ` | rebuild | **in progress (this handoff)** |
| `left` → `middle` | `w : Δ` | σ fires | `sorry` |
| `left` → `left` | `w : Γ` | rebuild | **done** |

The three rebuild branches all have the shape: fire κ on the LHS, fire the two
σ-acts (LHS outer, RHS inner), fire the pushforward on the RHS, then per-argument
the goal is the recursive call `act_interchange.aux σ κ (Φ ∷ i.arity) (args i)`.

## Per-act lemma choice (the key idea)

Each act sorts the head slot into: its **prefix** → `act_ap_left`; its
**domain** → fires; its **depth telescope** → `act_ap_depth` (`act_ap_right` is
the `Λ = Ρ = nil` instance). The three computation rules live in `Dispatch.lean`.

For the `w : Θ` branch:
- κ (`Subst Ψ ((Γ⋈Δ⋈Θ) ⋈ Ω)`, depth `Φ`): `Θ` is in κ's **prefix** → `act_ap_left`.
- σ (depth `Θ⋈Ω⋈Φ` resp. `Θ⋈Ψ⋈Φ`): `Θ` is at the **front of the depth telescope**
  → `act_ap_depth` with `Λ = Shape.nil`, `Φ_lemma = Θ`, `Ρ = Ω⋈Φ` (resp. `Ψ⋈Φ`).
- pushforward (`Subst Ψ ((Γ⋈Ξ⋈Θ) ⋈ Ω)`, depth `Φ`): `Θ` in its **prefix** → `act_ap_left`.

So this branch genuinely **mixes** `act_ap_left` (κ, pushforward) and `act_ap_depth`
(the two σ-acts). The two finished branches are uniform: `case right` is all
depth-telescope (`Ρ = nil`), `case left/left` is all prefix.

## What's been established (true facts)

- `nil ⋈ X` and `(X ⋈ Y) ⋈ Z` are **definitionally** equal to `X` and
  `X ⋈ (Y ⋈ Z)`. `⋈` is associative with `Shape.nil` as unit, definitionally.
- `Proper Γ` is a `Subsingleton` instance. `Proper.compose (Θ⋈Ω) Φ` and
  `Proper.compose Θ (Ω⋈Φ)` are **propositionally** equal (close with
  `Subsingleton.elim`), NOT defeq as terms. `Subst.act_irrel` handles
  act-depth-witness mismatches.
- `rw` and other syntactic tactics work badly here — they cannot see the defeq
  collapses above. The finished branches rely on `convert … using n` plus
  `Subsingleton.elim` / `Subst.act_irrel` to discharge witness mismatches.
- `act_ap_left` fires κ on this branch (`rw [act_ap_left]` succeeds: head
  `inl(inl(inr w))` matches `ι₁(ι₁ z)` with `z := inr w`).
- `convert act_ap_depth σ Shape.nil Θ (Ω⋈Φ) w _ using 2` fires the LHS outer
  σ-act and leaves exactly two subgoals: a clean
  `Proper.compose (Θ⋈Ω) Φ = Proper.compose (Shape.nil⋈Θ) (Ω⋈Φ)` (closed by
  `apply Subsingleton.elim`) and the main equation.

## Current code (committed, parked at the stuck point)

```lean
case right =>            -- w : Θ  (rebuild: both acts pass through)
  have cow := fun (i : C.Binder β) => act_interchange.aux σ κ (Φ ∷ i.arity) (args i)
  rw [act_ap_left]
  convert act_ap_depth σ Shape.nil Θ (Ω ⋈ Φ) w _ using 2
  · apply Subsingleton.elim
  · symm
    convert congrArg ((pushforward σ κ).act Φ) (act_ap_depth σ Shape.nil Θ (Ψ ⋈ Φ) w args) using 2   -- NO-OP, stuck here
```

Goal at the stuck `convert` (after `symm`):
```
Expr.ap (inl(inr w)) (fun j ↦ σ.act (Θ⋈Ω⋈(Φ∷j)) (κ.act (Φ∷j) (args j)))
  = (pushforward σ κ).act Φ (σ.act (Θ⋈Ψ⋈Φ) (Expr.ap (inl(inl(inr w))) args))
```

## The obstacle

We need to fire the inner σ-act `σ.act (Θ⋈Ψ⋈Φ) (Expr.ap (inl(inl(inr w))) args)`,
which sits **under** `(pushforward σ κ).act Φ (·)`, while the other side of the
equation is a bare `Expr.ap`.

```
goal inner head:    Proper.inl (Γ⋈Δ⋈Θ⋈Ψ) (Proper.inl (Γ⋈Δ⋈Θ) (Proper.inr (Γ⋈Δ) w))   -- double inl
act_ap_depth head:  Proper.inl (Γ⋈Δ⋈Θ)   (Proper.inr (Γ⋈Δ) w)                          -- single inl (weakening past Ρ=Ψ⋈Φ)
```

Defeq only if `inl` past the composite `Ψ⋈Φ` equals `inl` past `Φ` ∘ `inl` past `Ψ`.

Tried, all fail to fire it:
- `convert congrArg ((pushforward σ κ).act Φ) (act_ap_depth …) using 2` → no-op
  (different head symbols `Subst.act` vs `Expr.ap` block congruence descent into
  the `pushforward.act` argument).
- `convert congrArg _ (act_ap_depth …) using 2` → leaves the wrapper as an
  unsolvable function metavariable `?convert_2`.
- `… using 3` → `congrArg` application type mismatch.
- `rw` cannot match double-`inl` vs single-`inl`.

`case right` dodged this entirely: there the inner head was a single `inr z`
(`Φ` rightmost, `Ρ = nil`), so `convert congrArg _ (act_ap_depth …) using 2`
fired cleanly. This front-slot can't.

**Open question:** how to fire an inner `.act` whose head is the multi-`inl`
form when it is nested under another `.act`? Is there an `act`-congruence helper,
or a preferred idiom for rewriting an act under an act?

## Working rules (must follow)

- Idiomatic, human Lean. NO `<;>` / `try` cleverness. Address each generated
  subgoal by opening a bullet `·` and proving it there.
- No `show` / `change`. Exploit defeq through `convert` / `exact` / `apply` / `calc`.
- `Proper` mismatches → `Subsingleton.elim`; act-depth mismatches → `Subst.act_irrel`.
- Do NOT use `cow`. It is a read-only marker showing the shape the recursive call
  must take; it will be deleted once the branch is complete. The branch must end
  by aiming the rebuilt args at `act_interchange.aux σ κ (Φ ∷ i.arity) (args i)`.
- Never copy from `Equations.lean` / `Equations2.lean` (retired references).
- The LSP MCP reports goals correctly but fragment-by-fragment checks can hide an
  unsound flat structure; verify the whole branch with a real build. Do not
  trigger a Mathlib source compile — use `lake exe cache get` first if needed.
