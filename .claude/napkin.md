# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-05-19] Current active work is the Lean `Action` subtree**
   Do instead: start from `PLAN.md` and `HigherRankSyntax/HigherRankSyntax/Action/*.lean`; check with `lake env lean HigherRankSyntax/Action/SyntaxMonad.lean` from `HigherRankSyntax/`.
2. **[2026-05-19] Scratch imports can use stale `.olean`s**
   Do instead: after changing an imported module, run `lake build HigherRankSyntax.Action.<Module>` before testing scratch files that `import` it.

## Shell & Command Reliability
1. **[2026-05-19] Generated Agda interface files are noise for repo exploration**
   Do instead: exclude `*.agdai` from broad searches and file lists.

## Domain Behavior Guardrails
1. **[2026-05-19] `inst.aux` carries target renaming**
   Do instead: in `lift.aux`'s Γ-slot branch, call `inst.aux q.arity (Renaming.weakenList Δ τ) new_args [] (σ q)`; do not pre-weaken `σ q`.
2. **[2026-05-19] WF-recursive walker equations need `_unary.eq_1`**
   Do instead: prove one-step equations by `delta inst.aux`/`delta lift.aux`, `rw [*.aux._unary.eq_1, WellFounded.fix_eq]`, then `simp [classify_*]`.
3. **[2026-05-19] Avoid rejected substitution designs**
   Do instead: keep the indexed `XPos` classifier, avoid transports/`Eq.rec`, Sum classifiers returning expressions, and `Subst.extend`-style wrapping.

## User Directives
1. **[2026-05-19] Collaborator onboarding matters**
   Do instead: keep `PLAN.md` aligned with the active formalization after implementation changes.
