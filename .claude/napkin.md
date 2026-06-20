# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-05-25] Current active work is `endomaps` / `HigherRankSyntax`**
   Do instead: start from root `PLAN.md` and `HigherRankSyntax/HigherRankSyntax/*.lean`; check with `lake env lean HigherRankSyntax/Equations.lean` and `lake build HigherRankSyntax` from `HigherRankSyntax/`.
2. **[2026-05-19] Scratch imports can use stale `.olean`s**
   Do instead: after changing an imported module, run `lake build HigherRankSyntax.Action.<Module>` before testing scratch files that `import` it.

## Shell & Command Reliability
1. **[2026-05-19] Generated Agda interface files are noise for repo exploration**
   Do instead: exclude `*.agdai` from broad searches and file lists.

## Domain Behavior Guardrails
1. **[2026-06-18] `Subst` is now full-context**
   Do instead: translate old prefix substitutions `Subst C pre dom cod` as `Subst C dom (pre ⋈ cod)`; when acting at the monad level use `(Γ := Shape.nil)` explicitly.
2. **[2026-05-31] Interchange termination uses paired fuel plus subterms**
   Do instead: for `Subst.act_inst.oneDiamondAt`/`oneLiftAt`, keep the private `InterchangeFuel` measure; use `DomLt` for filler jumps and `Expr.Subterm.of_arg_ofList_cons` for ordinary argument recursion.
3. **[2026-06-15] General diamonds need explicit composite witnesses**
   Do instead: parameterize `Diamond`/`Lift` facades by the exact `Proper (τ ⋈ src)` and `Proper (τ ⋈ dst)` witnesses; the `src` recursive call needs `Proper.extendList (τ ⋈ dst) υ`, not `Proper.compose (τ ⋈ dst) (Tele.ofList υ)`.
4. **[2026-06-15] Env-centered singleton interaction still needs canonical spines**
   Do instead: do not install a private `Env` bridge alone. The hard theorem still needs explicit coherence between `Γ ⋈ (base ∷ α ⋈ υ)` and `((Γ ⋈ base) ⋈ ⌊α⌋) ⋈ υ`; either keep `Proper.AppendCoherence`/diamond or first build a canonical spine layer for these witnesses.
5. **[2026-06-08] Core interchange is a one-binder mutual pair**
   Do instead: state the central commute through `OneDiamond`/`OneLift`; keep `PreNaturality` and `Interchange` only for remaining derived stages.
6. **[2026-06-20] `Subst.comp` is postcomposition; `Subst.kcomp` is Kleisli composition**
   Do instead: use `Subst.kcomp σ θ` for ordinary empty-depth Kleisli composition and reserve `Subst.comp θ Ω κ` for postcomposition at passive depth `Ω`.
7. **[2026-05-27] Keep singleton α-slots abstract in under-list proofs**
   Do instead: avoid case-splitting the whole α-head branch on `xα`; use `ListSlotAt.sub_single xα` for termination and only case-split inside local definitional sub lemmas.
8. **[2026-06-07] Single `diamondAt` facade is not enough**
   Do instead: replace the interchange stack only with a mutual `oneDiamondAt`/`oneLiftAt` pair; the `dom` branch needs the lifted companion theorem, not just the main diamond.
9. **[2026-05-25] Tele unit proofs need one-binder instantiation bundle**
   Do instead: prove beta-for-eta and identity instantiation together by arity; keep expression recursion in a separate fixed-shape helper like `Subst.act_inst.idOf`.
10. **[2026-05-19] `inst.aux` carries target renaming**
   Do instead: in `lift.aux`'s Γ-slot branch, call `inst.aux q.arity (Renaming.weakenList Δ τ) new_args [] (σ q)`; do not pre-weaken `σ q`.

## User Directives
1. **[2026-06-16] Avoid defensive Lean witness boilerplate**
   Do instead: add `letI`, type ascriptions, or explicit instance arguments only when they select a computationally necessary `Proper` witness; remove no-op `show ... from rfl` rewrites and tiny tactic wrappers when direct terms elaborate.
2. **[2026-06-14] Present `Equations.lean` thesis-style**
   Do instead: organize explanations/refactors around action, unit/generic application, action-instantiation interaction, composition, and relative-monad laws; use `HigherRankSyntax/equations-math.tex` and `HigherRankSyntax/equations-refactor-plan.md` as the current guide.
3. **[2026-06-14] Treat `preNaturalityLiftAt` as a readability hotspot**
   Do instead: target the PreLift/β-side interaction with named head cases and branch helpers before retrying arbitrary-target diamonds.
4. **[2026-05-19] Collaborator onboarding matters**
   Do instead: keep `PLAN.md` aligned with the active formalization after implementation changes.
