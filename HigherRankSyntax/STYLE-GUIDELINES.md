# Style guidelines

These are the coding and collaboration rules for AI agents (and humans) working in this repository.

## General guidelines

Code should be readable and maintainable by humans and AI agents.

### Indentation

A typical statement should be indented as follows:

```lean
@[ext]
theorem Cow
    {param} ... (param}
    (param) ... (param) :
  main-statement
  := by
  proof
```

The parameters should be bunched on lines in a meaningful way.

If there are few parameters that easily fit on a line you may use:

```lean
@[ext]
theorem Cow {param} ... (param} :
  main-statement
  := by
  proof
```

Write short equations on a single line and long equations as follows:

```
   long-left-hand-side
     = long-right-hand-side
```

### Do not write large proof terms

Large proof terms are strongly discouraged, in particular those appearing in `exact`, `refine`, `change` and `show`.

Do not write `(some-term).symm` or `(some-term).trans`, use tactics such as `symm` and `trans`, or `apply Eq.trans`.

### Forbidden tactics

The following tactics are forbidden in general:

- `exact`
- `show`
- `change`
- `refine`

All of the above can usually be replaced by `apply`, `induction`, and various forms of equational reasoning.

If you do not see how to prove a goal without these forbidden tactics, talk to the user and get their approval first.

### Do not insert explicit typing annotations

Do not insert explicit typing annotations in terms, let Lean infer types: do not write `... (e : long-type-expression) ...` when only `e` will work.

Do not explicitly type definitions whose type can be inferred by Lean: instead of `have x : long-type-exprssion := ...` just write `have x := ...`
and similarly for `let`.

### Do not unfold unless necessary

Do not `unfold` definitions unless necessary for the proof to proceed.

### Tactics to reach for

- **Field-syntax for structure methods**: `inl Γ := body`, not `inl := fun Γ => body`.  Arguments live on the LHS of `:=`; anonymise implicit arguments with `{_}`.
- **`apply f`** when args are inferable, over `exact f a b c`.
- **`constructor`** (+ `intro`) over `refine ⟨fun x => ?_⟩`.
- **`apply Acc.intro`** over `refine Acc.intro _ ?_`.
- **`exists w`** (Lean core), not `use w` (Mathlib), to introduce an existential witness.
- **`left` / `right`** to discharge `Or`, not `apply Or.inl` or `refine Or.inl ⟨_, ?_⟩`.

### Use bullets and `case <name> ...  => ...`

Use bullets or `case` to discharge subgoals.

Only discharge subgoals using `<;>` followed by a tactic when the tactic is the same and short on all subgoals.

### Do not write complicated tacticals

Do not write complicated tactics that humans cannot understand. Use bullets and cases to address goals.

### `calc` with `_` placeholders

Don't write out intermediate values the proof determines anyway:

```lean
calc lhs
    = _ := by rw [foo, bar]
  _ = _ := by symm ; apply baz
```

### Counting subgoals

`convert … using N` and `congr 1` produce an unknown number of subgoals — don't assume.  Probe with `· done` (or `· sorry`) bullets and build; Lean reports the open goal or "No goals to be solved".  `all_goals sorry` is a useful preliminary to confirm the outer tactic accepted.

### Two-step strategy: explicit, then shrink

If necessary to get the proof done, you may first write a proof that is very explicit at first — named arguments, `@`-forms, `inferInstance`, full type ascriptions.  Once green, shrink the proof by removing everything that Lean can infer by itself:

1. `inferInstance` → `_`.
2. `@F a b c …` → `F` with named arguments (`(binder := value)`).
3. Drop leading positional arguments.
4. Drop named arguments where Lean can still infer.
5. Drop type ascriptions where the expected-type machinery suffices.

### Drop redundant namespace prefixes

Inside `namespace Foo`, write `bar`, not `Foo.bar`.

### Don't write `let` and `have` definitions that are used only once

Inline them instead, unless they significantly improve readability of code.

### Don't `@[simp]` for a single use site

Pass the lemma explicitly: `simp only [my_lemma]`.  A `@[simp]` attribute fires automatically in every simp call across the project; reserve it for lemmas that justify global use.

### `rw` versus `convert`

Pay attention to the fact that `rw` does syntactic matching only and may fail in cases where full definitional equality must be checked. In these cases, use other tactics that work with full definitional equality, such as `convert` and `congr`.

### Layout

- Bullet `·` per subgoal; prove the subgoal in that bullet.
- One semicolon-chained line is acceptable for tight branches; multi-tactic branches go on their own indented lines.
- No `<;>` or `try` as a catch-all (the symmetric-close exception above is the only case).

### Anti-patterns

- **No `show` or `change` to reshape a goal.**  Exploit definitional equality through term-mode, `apply` / `exact` / `calc` / `rw`.
- **No large hand-written proof terms.**  `(X.trans Y).trans Z.symm`, `exact (foo.trans (by rw […]; omega))` with embedded tactics, multi-line anonymous constructors — reach for tactic mode and break it up.
- **No `refine X ⟨_, ?_⟩`** to provide a witness and open a hole in one step.  Split into `left`/`right`/`exists`, then prove the subgoal separately.
- **No `if … return; rest`** — use `if … else`.
- **No single-use `let`s** that don't earn their name; inline them.  Exception: a name that substantially improves readability.
- **Don't pave roads before there's traffic.**  Don't introduce helper abbrevs, defs, or inductives until the same construction has appeared two or three times.  Inline first, abstract later.
- **Reuse existing apparatus.**  Before defining a new dispatch type, classifier, termination measure, or coherence lemma, search for an existing one.
- **Auxiliaries are standalone mathematical claims.**  A helper shaped like the goal at one branch is a tactic step in lemma's clothing.  Either generalise it or inline it.

## Project guidelines

### Naming

- **Arity:** upper-case Greek letters `Γ Δ Ξ Θ Ψ Ω Φ Π Σ Λ` for arities appearing on the left of `∋` and lower Greek letters `α β γ` for arities appearing on the right of `∋`. This is not always possible, in which case the default choise is an upper-case Greek letter.
- **Substitutions**: `σ θ κ`.
- **Slots, positions, indices**: lowercase (`x z w i j`).
- **No abbreviations.**  Spell identifiers out: `Config`, not `Cfg`; `parseDependentPair`, not `parseDepPair`; `unique`, not `uniq`. Established acronyms (`IO`, `JSON`) are fine.
- **Pair related identifiers with two distinct letters**, never with an `X_in` / `X_out` suffix scheme.
- **Drop redundant prefixes.**  Theorem names should not repeat what the surrounding namespace conveys: `Proper.inr_inr`, not `Proper.compose_inr_inr`.
