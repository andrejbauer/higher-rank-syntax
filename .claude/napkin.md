# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-06-22] `diamond-new` live backend is modular**
   Do instead: treat `Equations.lean`/`Equations2.lean` as retired references only; work in `Dispatch.lean`, `Instantiation.lean`, `Interchange.lean`, and `MonadLaws.lean`, checking with `lake build HigherRankSyntax` from `HigherRankSyntax/`.
2. **[2026-05-19] Scratch imports can use stale `.olean`s**
   Do instead: after changing an imported module, run `lake build HigherRankSyntax.Action.<Module>` before testing scratch files that `import` it.

## Shell & Command Reliability
1. **[2026-05-19] Generated Agda interface files are noise for repo exploration**
   Do instead: exclude `*.agdai` from broad searches and file lists.

## Domain Behavior Guardrails
1. **[2026-06-24] Carrier products need reassociation and unit laws**
   Do instead: when porting old `ProperTele` proofs, use `Carrier.inr_inl`, `Carrier.inr_inr`, `Carrier.unit_right`, and `Carrier.unit_left`; add `Expr.η` type ascriptions when Lean guesses the wrong product spine.
2. **[2026-06-22] Current interchange theorem is `act_interchange.aux`**
   Do instead: map old `diamondAt` regions to new variables as `P,D,D',T,S,S',U = Γ,Δ,Ξ,Θ,Ψ,Ω,Φ`; finish current active cases in `Interchange.lean`.
3. **[2026-06-18] `Subst` is now full-context**
   Do instead: translate old prefix substitutions `Subst C pre dom cod` as `Subst C dom (pre ⋈ cod)`; when acting at the monad level use `(Γ := Shape.nil)` explicitly.
4. **[2026-05-25] Tele unit proofs need one-binder instantiation bundle**
   Do instead: prove beta-for-eta and identity instantiation together by arity; keep expression recursion in a separate fixed-shape helper like `Subst.act_inst.idOf`.
5. **[2026-05-19] `inst.aux` carries target renaming**
   Do instead: in `lift.aux`'s Γ-slot branch, call `inst.aux q.arity (Renaming.weakenList Δ τ) new_args [] (σ q)`; do not pre-weaken `σ q`.

## User Directives
1. **[2026-06-22] Prefer goal-directed `apply` for Proper coherence**
   Do instead: orient small coherence goals with `symm`/`convert` as needed, then use bare `apply Proper.foo` so Lean infers shapes and slots; avoid `exact (Proper.foo _ _ _ z).symm` and similar explicit witness plumbing.
2. **[2026-06-16] Avoid defensive Lean witness boilerplate**
   Do instead: add `letI`, type ascriptions, or explicit instance arguments only when they select a computationally necessary `Proper` witness; remove no-op `show ... from rfl` rewrites and tiny tactic wrappers when direct terms elaborate.
3. **[2026-06-14] Present `Equations.lean` thesis-style**
   Do instead: organize explanations/refactors around action, unit/generic application, action-instantiation interaction, composition, and relative-monad laws; use `HigherRankSyntax/equations-math.tex` and `HigherRankSyntax/equations-refactor-plan.md` as the current guide.
4. **[2026-06-14] Treat `preNaturalityLiftAt` as a readability hotspot**
   Do instead: target the PreLift/β-side interaction with named head cases and branch helpers before retrying arbitrary-target diamonds.
5. **[2026-05-19] Collaborator onboarding matters**
   Do instead: keep `PLAN.md` aligned with the active formalization after implementation changes.
