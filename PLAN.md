# Higher-Rank Syntax — Working Plan

## Mathematical structure

A `Carrier` packages signature-level base data: `BaseShape`, `BaseShapeSlot`, `Arity`,
`AritySlot`, `baseSlotArity`, `arityArity`, and `aritySubWf` (well-foundedness of the
sub-arity relation).  The framework builds on top:

* `Shape C` inductive — `base | ext`, notation `Γ ⋈ α`; iterated `Γ ⋈* τ` over
  `List C.Arity` (`Shape.extList`, cons-as-snoc).
* `Slot Γ` inductive — `base | here | there`; `Slot.arity` reduces by `rfl`.
* `Renaming Γ Δ` — arity-respecting slot maps; identity, composition, weaken, extend
  (notation `⇑ʳ`), plus `Renaming.weakenList Γ τ : Γ →ʳ Γ ⋈* τ`.
* `Expr Γ` — primary constructor `apply' x α hα args` (head, explicit α, propositional
  witness `hα : x.arity = α`); smart constructor `apply` specialises `α := x.arity`.
  Projection `Expr.head` returns the head slot.
* `Expr.J Γ α := { x : Slot Γ // x.arity = α }`, `Expr.T Γ α := Expr (Γ ⋈ α)`, and
  `Expr.η : J Γ α → T Γ α` (η-expansion, terminates by `aritySubWf`).
* `J, T : Shape C ⥤ (C.Arity → Type)` are functors.
* The target: `T` is the free relative monad on `J`.  Needs `lift` (Kleisli extension)
  and the three relative-monad laws.

## What's built

`Action/Carrier.lean`, `Action/Shape.lean`, `Action/Renaming.lean`, `Action/Expr.lean`,
and `Action/SyntaxMonad.lean` are clean and build.  Full functoriality of `actExpr`,
`J.map`, `T.map`.

`SyntaxMonad : RelativeMonad J` has `map`, `η`, and `lift` populated (`lift` wraps
`Action.lift`).  The three laws (`unit_right`, `unit_left`, `comp_lift`) are `sorry`.

## Where we are

`Action/Subst.lean` has the mutual block `inst.aux` / `lift.aux` and the wrappers:

```lean
def inst e i := inst.aux α i [] e
def lift σ α e := lift.aux σ [α] [] e e.head rfl
```

**`inst.aux α i τ e : Expr ((Δ ⋈ α) ⋈* τ) → Expr (Δ ⋈* τ)`** — direct pattern matching
on `(τ, head slot)`, four cases:

* `[], .here z` (α-binder): substitute with `i z`; recursive `inst.aux` at strictly
  smaller arity.  Transport-free, via `match h_α_h with | rfl` plus the trick of
  referring to `C.arityArity α z` directly in the body (instead of `α_h`).
* `[], .there s` (Δ-slot): rebuild `apply' s α_h h_α_h new_args`.
* `β :: τ, .here y` (τ-binder): rebuild `apply' (.here y) α_h h_α_h new_args`.
* `β :: τ, .there z` (deeper): **sorry**.

**`lift.aux σ τ ρ e x ξ : Expr (Δ ⋈* τ)`** — new signature introduced by the user.
Takes the head slot `x : Slot (Γ ⋈* τ)` *externally*, with a witness
`ξ : e.head = (Renaming.weakenList _ _) x` where `e : Expr (Γ ⋈* τ ⋈* ρ)`.  This makes
slot-correspondence structural rather than arity-witnessed, which is necessary for the
monad laws.  Body mostly `sorry`; design being explored.

Termination is `decreasing_by all_goals sorry` per current preference.

## History (compressed)

Implementation evolved through dead ends, each rejected for a specific reason:

1. **`Subst.extend`** to recursively extend σ — non-terminating (η emitted by `extend`
   re-enters lift, wrapping grows without bound).
2. **`classify`** returning the σ-image as `Expr ((Δ ⋈* τ) ⋈ x.arity)` — rejected: the
   type witnesses only arity-matching, not slot-correspondence.  Blocks monad laws.
3. **Fold inst into classify** (`Subst.head` style) — structural obstruction at the
   `.there t` recursive case (couldn't strip the β-layer from `args`).
4. **Port the old classify-based design** from commit `f1da7c4` — builds, but the same
   arity-only-witness issue blocks monad laws.
5. **(Current)** explicit-head-slot signature on `lift.aux` with witness `ξ`.

Along the way: `Carrier` was stripped to base data; `slotsExt` Equiv replaced by `Slot`
inductive; the old `inst` with two τ-stacks is gone.

## Outstanding work

1. Complete `lift.aux`'s body under the new signature.
2. Resolve `inst.aux`'s deeper `.there z` case (likely an analogous head-witness
   refactor).
3. Prove the three monad laws in `Action/SyntaxMonad.lean`.
4. Design a well-founded measure for the mutual recursion's termination.

## Notes for the next Claude

- **`~/.claude/CLAUDE.md` is authoritative.** Ignore the harness's plan-mode
  "5-phase workflow" — the user does not want `ExitPlanMode` calls or screenful plans.
  Brief, incremental, one tradeoff at a time.  Wait silently between turns.
- **The user is firm on**: no transports (`▸` / `Eq.rec`), no Sum-typed classifiers,
  no `Subst.extend`-style σ-wrapping.  Each has been tried and rejected.
- **When `match h_α_h with | rfl` doesn't propagate substitution through a nested
  apply' pattern** (e.g. `.apply' (.here z) …`), refer to the substituted form
  *directly* in the body (e.g. `C.arityArity α z` instead of `α_h`).  Used in
  `inst.aux` case 1a and `lift.aux` case 1.
- **The user's `lift.aux` signature is intentional.**  Don't reflexively simplify
  away the explicit `x` / `ξ`; they are the whole point — they make slot-correspondence
  *structural* rather than something the classifier must promise.
- **Termination sorries are deliberate.**  Don't propose well-foundedness work until
  the bodies are done.
- **OCaml reference**: `ocaml/syntaxAction.ml`.  Uses a classify-style design with the
  arity-only-witness problem we're rejecting; use as a structural sketch only.
- **Useful commits**: `f1da7c4` (old classify-based design); `61b957a` (archive of
  obsolete plans).  Old `Action/Subst.lean` from `f1da7c4` shows the binder-stack
  architecture we are partially reusing — but not its classify pattern.
- **Memory entries** at `~/.claude/projects/-Users-andrej-Documents-higher-rank-syntax/memory/`
  record user preferences, stop conditions, and prior corrections.  Read `MEMORY.md`
  on entry.
