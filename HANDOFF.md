# Handoff

This file is for the next Claude instance picking up work on this project.

## Repo state

- Branch: `endomaps`. 6 commits ahead of `origin/endomaps` (all cleanup;
  see `git log` for messages).
- Build green: `lake build HigherRankSyntax` (run from `HigherRankSyntax/`).
- Working tree clean.
- One unrelated stash: `stash@{0}` — the failed lists-to-Shape migration
  attempt (see "Major pending task" below).

## What just happened (this session)

Sequence of cleanup commits, every one builds:

1. `38f0893` — drop 19 redundant `change` clauses before
   recursive-call `exact`s.
2. `8bc7a7c` — drop 7 defensive `(by exact Proper.{extendList,ofList} …)`
   instance supplies; 3 `«args✝»` hygiene names in `decreasing_by` → `_`;
   40+ `(Tele.ofList υ : Shape C)` ascriptions → bare expressions.
3. `49e88af` — drop 3 more `@`-explicit forms with `inferInstance`
   defensive args.
4. `4f5bad9` — doc comments on 22 sites in the interchange machinery;
   `:= by` reflowed to its own line at every theorem statement.
5. `dcfc261` — `Subst.act_inst.instOne`'s `cod` made explicit (was
   implicit, caused decomposition ambiguity); the 8 facade abbrevs'
   single-use `let κ := …; κ.act …` patterns inlined.
6. `d51a042` — five proof-body `Subst.inst ⌊_⌋ (fun q => match q with | .here _ => …)`
   collapsed to the equivalent `instOne` calls.
7. `5b86740` — flatten the `Subst.act_inst.` private namespace: 18
   private declarations now reside directly (`instOne`, `underListAt`,
   `UnderList.actThenInst`, etc.) instead of under `Subst.act_inst.`.
   Public `Subst.act_inst.{η, id}` kept as-is.

## User preferences captured (apply to all future work)

- **No `open`s** beyond the bare minimum. Andrej dislikes them.
- **Shallow namespaces preferred over `open`.** Private declarations
  should not be deeply namespaced — flatten when possible.
- **Don't optimise for "less work".** "It is always valuable to make
  the code better structured — it doesn't matter if that requires a
  lot of work." Quality first.
- **No just-in-case additions.** Don't add code, identifiers,
  comments, infrastructure preemptively. Add when actually needed.
  (This is also in `~/.claude/CLAUDE.md` under global rules.)
- **`:= by` on its own line** at the same indent as the conclusion,
  with the tactic body 2-space-indented below. (Confirmed style.)
- **Empirical first.** Run preliminary experiments before mass edits;
  build green between batches; don't trust assumed correctness.
- **No proof structure rewrites** for hacky workarounds. Cleanup OK;
  forcing things through with letI/show shadowing is not.
- **No `git checkout` / `reset --hard` to revert** — Andrej decides
  when to revert. Stash if you need to set aside.
- **Andrej wants to review every commit.** Don't commit without an
  explicit `commit` from him.

## Major pending task — the Shape migration

The intended outcome: replace every `(ρ : List C.Arity)` τ-stack
parameter with `(S : Shape C) [Proper S]`, and every `Tele.ofList ρ`
expression with `S`. The user's goal is to lift the interchange
machinery from working on list-shaped τ-stacks to working on arbitrary
telescopes.

### What we learned by trying

Attempted in this session; 16 build errors; stashed at `stash@{0}`.
The errors are NOT bugs in the swap — they are a genuine **associativity
diamond** in Lean's `Proper` instance synthesis:

- Two `rfl`-equal shapes `(A ++ B) ∷ X` (left-assoc) and `A ++ (B ∷ X)`
  (right-assoc) get **different `Proper` instance terms**
  (`instCons X (A ++ B)` vs `compose A (B ∷ X)`) because Lean's
  first-order instance synthesis matches on the outermost `++`/`∷`.
- The two terms inhabit the same proposition, but `Proper` is not
  `Subsingleton`, so they're not defeq.
- The proofs of `underListAt`, `preNaturalityLiftAt`, `preNaturalityAt`,
  `interchange` mix both associativity forms (the outer `have hfill`
  uses one form, the recursive call's substituted abbrev body uses the
  other), so the `change`/`exact` chain hits the diamond.

### What works in the original code

In the list-based version, `Tele.ofList` is `@[reducible]` and `Tele.ofList ρ`
reduces to a uniquely-determined nested chain. `instExtendList` (also
`@[reducible]`) follows the recursion, producing a canonical nested-`instCons`
skeleton. Both syntactic forms of "the same composite shape" reduce to the
same instance term modulo `@[reducible]`. The diamond is invisible.

With Shape (a structureless record over `List → List`), no canonical
form exists, no `@[reducible]` reduction normalises the term, and the
diamond becomes visible.

### Options to bridge the diamond (decided against, but in scope)

1. **Canonicalise parenthesisation in proofs.** Every shape expression
   in proof bodies follows a fixed convention (left- or right-assoc;
   `∷ α` vs `++ ⌊α⌋`). Mechanical but invasive; brittle to maintenance
   (the convention lives in our heads, not in the type system).
2. **`Subsingleton` (Proper S)` coherence lemma.** Provable from
   the existing axioms by funext, then used as a transport at each
   diamond site. Real proof work; expands the API.
3. **Revert to explicit-passing.** Take composite `Proper` instances
   as explicit non-instance binders, propagate by hand. Verbose
   signatures, but no instance-synthesis surprises.

Andrej preferred a different path: **clean up the proofs first to
shrink the diamond's attack surface.** That's what the recent commits
have been doing. After this cleanup, the diamond hits fewer sites in
the proofs, but it's still there. The next attempt would benefit from
trying option 1 or 2 with a smaller surface.

## Bucket list (deferred, in rough priority order)

1. Retry the Shape migration. The cleanups have reduced the diamond
   surface; option 1 or 2 above is the bridging strategy. See
   `stash@{0}` for prior work.
2. The remaining 22 `change` / `show` clauses in proof bodies. Most
   are load-bearing (`change` before `rw` to expose a head shape).
   Some may yield to higher-level lemma extraction.
3. Higher-level lemmas extracting repeated tactic patterns. E.g.
   `refine (congrArg (κ'.act _) (Subst.act_ap_inr σ _ x args)).trans ?_;
   rw [extendList_inr_inr …]` shows up 4–5 times across the proofs;
   a named lemma would compress these.
4. Reformulate metric plumbing (`DomLt`, `DomMeasure`,
   `SlotAt.subWitness`) onto `Shape` instead of `List`. Currently the
   only remaining `List C.Arity` use outside τ-stacks.
5. Long-line / 100-col reflow pass — deferred.

## Key files

- `HigherRankSyntax/HigherRankSyntax/Equations.lean` — the main file
  (most cleanup happened here).
- `HigherRankSyntax/HigherRankSyntax/Proper.lean` — `Proper`
  class + `compose` def + instances. The `compose` is currently a
  `def` (not an instance) and `instExtendList` is alive.
- `HigherRankSyntax/HigherRankSyntax/Subst.lean` — `Subst.act` and
  related infrastructure.
- `HigherRankSyntax/HigherRankSyntax/SyntaxMonad.lean` — the relative
  monad witness.

## Plan-file references

- `~/.claude/plans/lazy-weaving-cascade.md` — the running session
  plan file with detailed write-ups of each cleanup step taken. The
  newest plan at the top, older plans below.
- `PLAN.md` and `HigherRankSyntax/PLAN.md` — pre-session high-level
  plans about the project as a whole.

## How to talk to Andrej

- Direct answers. No "shall I…?" closers.
- Don't restate what you've done after the fact — he can read the diff.
- Use his global preferences (`~/.claude/CLAUDE.md`): modifier placement,
  active voice, etc.
- If he asks a question, answer the question — don't infer permission
  to act from it.
- If he tells you you weren't authorised, stop and wait — do not
  auto-revert.
- He prefers terse responses that fit on the screen.
