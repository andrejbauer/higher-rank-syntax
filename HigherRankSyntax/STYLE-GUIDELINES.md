# Style guidelines

These are the coding and collaboration rules for AI agents (and humans) working in this repository.

## General guidelines

Code should be readable and maintainable by humans and AI agents.

### Indentation

A typical statement should be indented as follows:

```lean
@[ext]
theorem Cow
    {param} ... {param}
    (param) ... (param) :
  main-statement
  := by
  proof
```

The parameters should be bunched on lines in a meaningful way.

If there are few parameters that easily fit on a line you may use:

```lean
@[ext]
theorem Cow {param} ... {param} :
  main-statement
  := by
  proof
```

Write short equations on a single line and long equations as follows:

```
   long-left-hand-side
     = long-right-hand-side
```

### No `let` or `letI` in theorem statement

A theorem statement may not contain any `let` or `letI`, so the following is forbidden:

```lean
theorem Cow (param) ... (param) :
  let x := ...
  letI y := ...
    main-statement
```

If you think `letI` is needed, you must talk to the user to first solve issues with typeclass instance resolution (do not work around problems, report them instead).


### Prefer `apply` over `exact`

A short `exact h` is acceptable, but `apply h` is preferred when arguments are inferable.  A long `exact <complicated-term>` is forbidden — break it into smaller tactic steps.

### No `show`, `change`, `refine` or `unfold` without need

Don't use `show` or `change` to reshape a goal; exploit definitional equality through term mode, `apply`, `calc`, or `rw`.  Don't `unfold` definitions unless the proof genuinely cannot proceed otherwise.

Do not use `refine` when other tactics can be used instead. Only use it as a last resort.

### No large proof terms

Don't write `(some-term).symm` or `(some-term).trans` chains; use the tactics `symm`, `trans`, `apply Eq.trans`.  Don't write multi-line anonymous-constructor blocks `⟨…, …⟩` as proof terms — break them up.

If you cannot prove a goal without one of the forbidden constructs above, talk to the user before proceeding.

### Don't insert explicit type annotations

Let Lean infer types: don't write `(e : long-type-expression)` when `e` will work.  Don't explicitly type definitions whose type can be inferred: instead of `have x : long-type-expression := ...`, write `have x := ...`.  Same for `let`.

### Drop redundant namespace prefixes

Inside `namespace Foo`, write `bar`, not `Foo.bar`.

### One subgoal per bullet

Use `·` or `case <name> => …` to discharge each subgoal.  No nested tacticals, no `<;>` or `try` as catch-alls — humans must be able to read each step.

Exception: when a single tactic discharges all subgoals symmetrically (e.g. `apply Eq.trans <;> apply inl_tag`), `<;>` is acceptable.

### `calc` with `_` placeholders

Don't write out intermediate values the proof determines anyway:

```lean
calc lhs
    = _ := by rw [foo, bar]
  _ = _ := by symm ; apply baz
```

### Counting subgoals before proving

`convert … using N` and `congr 1` produce an unknown number of subgoals — don't assume.  Probe with `· done` (or `· sorry`) bullets and build; Lean reports the open goal or "No goals to be solved".  `all_goals sorry` is a useful preliminary to confirm the outer tactic accepted.

### Two-step strategy: explicit, then shrink

If a proof is hard to find, write it with everything explicit first — named arguments, `@`-forms, `inferInstance`, full type ascriptions.  Once green, shrink incrementally and build between each step: `inferInstance` → `_`; `@F …` → `F` with named arguments; drop positional arguments; drop named arguments where Lean infers; drop type ascriptions where expected-type machinery suffices.

### Don't `@[simp]` for a single use site

A `@[simp]` attribute fires automatically in every simp call across the project.  Reserve it for lemmas that justify global use; otherwise pass the lemma explicitly: `simp only [my_lemma]`.

### Don't introduce single-use `let` or `have`

Inline them, unless naming substantially improves readability.

### `rw` is syntactic — use `convert`/`congr` for defeq

`rw`'s matcher is purely syntactic.  When full definitional equality is needed (associativity rewrites, instance-witness mismatches, `nil ⋈ X = X`-style reductions), use `convert` or `congr` and discharge the leftovers with `Subsingleton.elim` or a dedicated coherence lemma.  Plain `rw` is fine when the goal literally contains the pattern.

### Don't introduce helpers without need

If you think that a new definition, lemma or a theorem shoud be introduced, you must first propose it to the user and get their permission to do so.

### Helper statements must be general and mathematically meaningful

When you propose helper statements to the user, make sure they have value beyond a single use case in the current proof. Ideally, hepler lemmas should be generalized and have independent mathematical meaning. Investigate the code to see if a helper lemma might have multiple uses.

When introducing a helper statement that will solve a goal, proceed as follows:

1. Consult the user.
2. State the helper statement and `sorry` its proof.
3. Immediately use the helper statement to close the goal. If the goal cannot be easily closed, this indicates the helper statement might be inappropriate or wrong.
4. Once you are sure the helper statement is warranted, prove it.

### Top-down approach

When working on a main goal that has several subgoals that require furhter helper statements, proceed in a breadth-first fashion:

1. Make a little bit of progress on the immediate subgoals.
2. Observe similarities between the subgoals and formulate helper statements as necessary, consult the user about further plans.
3. Test the helper statements to see if they will close the subgoals.
4. Proceed to the subgoals, always looking for similarities. Do not deeep-dive into a single small goal, lest you lose track of the big picture.
5. Periodically review progress and update your idea of the big picture.

## Project guidelines

### Naming

- **Arity**: upper-case Greek letters `Γ Δ Ξ Θ Ψ Ω Φ Π Σ Λ` for arities appearing on the left of `∋`, and lower-case Greek letters `α β γ` for arities appearing on the right of `∋`.  When this is not possible, default to upper-case Greek.
- **Substitutions**: `σ θ κ`.
- **Slots, positions, indices**: lowercase (`x z w i j`).

### No abbreviations

Spell identifiers out: `Config`, not `Cfg`; `parseDependentPair`, not `parseDepPair`; `unique`, not `uniq`.  Established acronyms (`IO`, `JSON`) are fine.  For a pair of related identifiers pick two distinct letters; never an `X_in` / `X_out` suffix scheme.

### Drop redundant prefixes in theorem names

Theorem names should not repeat what the surrounding namespace already conveys: `Proper.inr_inr`, not `Proper.compose_inr_inr`.

### `Proper` is a `Subsingleton` — use it

`Proper Γ` is a subsingleton (`Proper.subsingleton`); keep it an `instance`.  For two `Proper Γ` witnesses on the same shape, `apply Subsingleton.elim` (inside `convert`) closes the mismatch.  For `Subst.act` calls on the same shape with different `Proper` witnesses for the depth, `apply Subst.act_irrel`.  Never carry `Proper` witnesses as structure fields with coherence laws; let `convert` + the two lemmas above do the work.

### Renaming notation

`Γ →ʳ Δ` is the type of renamings; `𝟙ʳ` is the identity; `g ∘ʳ f` is composition "g after f" (single `ʳ`); `ρ ⇑ʳ α` extends a renaming through a fresh position.

### Substitution notation

`Subst Δ Γ` is a substitution from domain `Δ` into target `Γ`.  `σ.act Φ e` is the action at depth `Φ`.  `⟦ σ ⟧ˢ e` is the ground action, `Subst.act σ Shape.nil e`.
