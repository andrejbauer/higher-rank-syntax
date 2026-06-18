# Scoped-Core Refactor Handoff

This note summarizes the refactor direction and the current proof state for the
next agent.

## Main Idea

The old backend proves relative-monad equations over flat expressions

```lean
Expr (Γ ⋈ τ)
```

where free variables, active substitution variables, passive binders, and local
argument binders are all represented as slots of one telescope.  Most of
`Equations.lean` is therefore not conceptual mathematics; it is bookkeeping:
recovering where a head came from and aligning proof-relevant `Proper`
witnesses.

The scoped refactor changes the proof backend to expressions with two explicit
parts:

```lean
ScopedExpr Γ τ
```

Here `Γ` is the free context and `τ` is the local binder telescope.  A head is
literally one of:

```lean
ScopedHead.free  : Γ ∋ α → ScopedHead Γ τ α
ScopedHead.local : τ ∋ α → ScopedHead Γ τ α
```

Descending into an application argument only extends the local telescope:

```lean
ScopedExpr.ap :
  ScopedHead Γ τ α →
  ((i : C.Binder α) → ScopedExpr Γ (τ ∷ i.arity)) →
  ScopedExpr Γ τ
```

This keeps the important distinction, "free variable versus local binder", in
the syntax instead of recovering it with `Proper.cover`.

## Why `ProperSpine`

The first scoped prototype used lists for local binder stacks, but list
associativity made the one-binder proofs awkward.  The current version uses
`Shape C` again for local stacks, so telescope associativity is definitional.

However, arbitrary `Proper` witnesses are still proof-relevant.  The solution
is `ProperSpine`, a canonical witness for proper telescopes.  New scoped proofs
should use explicit `ProperSpine` values and their structural operations:

- `ProperSpine.inl`
- `ProperSpine.inr`
- `ProperSpine.classify`
- `ProperSpine.coverEq`
- `ProperSpine.append`
- `ProperSpine.append_inl`
- `ProperSpine.append_inr_inl`
- `ProperSpine.append_inr_inr`

The important design rule is: use canonical spines in the scoped backend, and
only bridge back to old `Proper` where compatibility requires it.

## Current Proof Ladder

The central local operation is one-active-binder substitution:

```lean
instOneAt
  (pχ : ProperSpine χ) (υ : Shape C) (α : C.Arity)
  (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity)) :
  ScopedExpr Γ ((υ ∷ α) ⋈ χ) →
  ScopedExpr Γ (υ ⋈ χ)
```

The intended reading is:

- `υ` is the older local tail;
- `α` is the active binder being substituted;
- `χ` is the newer passive prefix;
- source local context is `(υ ∷ α) ⋈ χ`;
- target local context is `υ ⋈ χ`.

Implemented in `ScopedExpr.lean`:

- telescope-indexed `ScopedHead` and `ScopedExpr`;
- free/local renaming and their identity/composition laws;
- `etaHead` and `eta`;
- local vocabulary `localPrefix`, `localTail`, `localMapTail`;
- `LocalSite` classifier with cases `.pre`, `.active`, `.tail`;
- `instOneAt` and its computation lemmas for free, passive-prefix, older-tail,
  and active heads;
- site-head restatements of the `instOneAt` computation lemmas;
- `instOneAtUnder`, the argument-shaped facade for recursive calls under a
  newly opened binder;
- `renameLocal_instOneAt`, proving that tail-renaming commutes with
  `instOneAt`;
- passive-extension normalizers and naturality:
  - `extendPassiveRen`
  - `extendPassiveRen_cons`
  - `passiveInsert`
  - `localPrefix_extendPassive`
  - `localTail_extendPassive`
  - `renameLocal_extendPassiveAtFiller`
  - `instOneAt_extendPassiveAt`
  - `instOneAt_extendPassive`
  - `instOneAt_extendPassiveUnder`

The old flat backend in `Equations.lean` is still present and still powers
`SyntaxMonad.lean`.  The scoped backend is proof infrastructure only so far.

## What Was Learned From Local-Local Interchange

The next major theorem is local-local interchange: substituting an upper active
binder `β` and a lower active binder `α` should commute in the shape required
by environment action.

A scratch proof in `/tmp/ScopedInterchange2.lean` got this far:

- free-head case works;
- outer passive `ψ` head case works;
- upper-active `β` case works using `instOneAt_extendPassiveUnder`;
- inner passive `χ` case works;
- older-tail `υ` case works;
- the remaining blocker is the active-`α` case.

The active-`α` branch exposes one missing lemma.  After `α` fires, the upper
`β` substitution is acting on the selected `α`-filler, but that filler was only
weakened through the passive insertion of `β`.  We need a theorem saying that
substituting a binder through an expression that merely contains that binder as
a passive weakening contracts in the expected way.

Informally:

```text
instOneAt for β, applied to a term obtained by weakening past β,
is the same as the original term, with arguments transformed recursively.
```

This is not just a tactic issue.  It should be proved as a small named scoped
lemma before finishing `LocalInterchange.localLocal`.

## Suggested Next Pass

1. Add a small "passive active-binder absence" lemma for `instOneAt`.

   The theorem should cover the active-`α` situation from local-local
   interchange: a term/filler has been weakened through a passive `β`, and then
   `instOneAt` tries to substitute `β`.  Since no head in the original term is
   the active `β`, the result should be the original substitution/renaming
   shape, with recursive argument equalities.

2. Prove it with the same style as existing scoped lemmas.

   Use semantic head cases:

   - free head: preserved, recurse on arguments;
   - passive-prefix head: preserved;
   - older-tail head: preserved;
   - active impossible/absent by construction, or converted to the intended
     filler equation depending on the exact statement.

   Use `instOneAtUnder` or an analogous under-binder facade if the argument
   shape exposes one extra binder.

3. Return to `LocalInterchange.localLocal`.

   Use the scratch structure:

   ```lean
   namespace LocalInterchange
   private def upperThenLower ...
   private def lowerThenUpper ...
   private def upperThenLowerUnder ...
   private def lowerThenUpperUnder ...
   private theorem localLocal ...
   end LocalInterchange
   ```

   The already-understood branch split is:

   - free;
   - outer passive `ψ`;
   - active `β`;
   - tail, then classify again into:
     - inner passive `χ`;
     - active `α`;
     - older tail `υ`.

4. After local-local interchange is green, prove the environment laws.

   Define:

   ```lean
   Env Γ Δ := ∀ {α}, Γ ∋ α → ScopedExpr Δ ⌊α⌋
   ```

   Then prove:

   - `Env.act`;
   - `Env.act_renameLocal`;
   - `Env.act_instOneAt`;
   - `Env.act_id`;
   - `Env.act_η`;
   - `Env.act_comp`.

5. Only then migrate `SyntaxMonad.lean`.

   The target presentation is:

   ```lean
   T Γ α := ScopedExpr Γ.tele ⌊α⌋
   η := ScopedExpr.eta
   lift f := Env.act (fun p => f _ p)
   ```

   `SyntaxMonad.lean` should eventually use scoped `Env.act_comp`, not the old
   flat `Subst.act_kcomp`.

## Validation State

As of this handoff, these checks passed from `HigherRankSyntax/`:

```bash
lake env lean HigherRankSyntax/ScopedExpr.lean
lake env lean HigherRankSyntax/Equations.lean
lake env lean HigherRankSyntax/SyntaxMonad.lean
lake build HigherRankSyntax
```

Also checked:

```bash
rg -n '\b(sorry|axiom)\b' HigherRankSyntax/HigherRankSyntax
git diff --check
```

No new `sorry` or `axiom` is present in tracked Lean files.

## Practical Advice

- Keep theorem statements in the scoped local vocabulary: `localPrefix`,
  `localTail`, `localMapTail`, `instOneAtUnder`, and `extendPassiveRen`.
- Confine raw `ProperSpine.append_*` rewrites to small helper lemmas.
- Avoid global simp rules for these coherence lemmas; local `rw`/`change`
  blocks have been more predictable.
- Do not migrate `SyntaxMonad.lean` until `Env.act_instOneAt` and
  `Env.act_comp` are green.
- Do not delete `Equations.lean` yet.  It is still the production proof backend.
