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
1. **[2026-06-16] Full-context `Subst` still needs active-domain heredity**
   Do instead: expose `Subst C Γ Δ` as the public Kleisli environment, but keep/replace a backend that measures only active binders for one-binder instantiation; direct self-recursion on fired fillers counts the target prefix and does not terminate cleanly.
2. **[2026-06-17] Telescope-scoped stacks still hit `Proper` injection coherence**
   Do instead: `Shape` local stacks fix context associativity, but not proof-relevant `Proper.inl`/`Proper.inr` coherence through `compose`/`cons`; use an exact-witness local-spine layer or redesign proper telescopes so injections compose definitionally before retrying local-local interchange.
3. **[2026-06-17] Scoped renaming needs argument-shaped recursion**
   Do instead: prove `renameLocal_instOneAt` equation-style with a private `instOneAtUnder` facade for arguments; stable branches use `hargs`, while the active branch makes the arity-decreasing recursive call before `renameLocal_activeFiller`.
4. **[2026-06-16] `Env.act_instOneAt` needs passive-extension naturality before interchange**
   Do instead: before local-local interchange, prove `instOneAt` commutes with weakening by an outer passive `ProperSpine ψ`; the upper-active branch of interchange needs this before `renameLocal_instOneAt` can finish the filler equation.
5. **[2026-06-17] Scoped local-local active-α branch needs an absence lemma**
   Do instead: after passive-extension naturality, prove that substituting an active binder through an expression merely weakened past that binder contracts the weakening; this is the missing step after α fires and β is only a passive weakening of the selected α-filler.
6. **[2026-06-16] Scoped local algebra should avoid proof-returning cover in recursive theorems**
   Do instead: state recursive proofs by separate `.free`/`.local` equations and use computational classifier-stability lemmas such as `LocalSite.classify_mapTail`; reserve `LocalSite.cover` for nonrecursive normalization.
7. **[2026-05-31] Interchange termination uses paired fuel plus subterms**
   Do instead: for `Subst.act_inst.oneDiamondAt`/`oneLiftAt`, keep the private `InterchangeFuel` measure; use `DomLt` for filler jumps and `Expr.Subterm.of_arg_ofList_cons` for ordinary argument recursion.
8. **[2026-06-15] General diamonds need explicit composite witnesses**
   Do instead: parameterize `Diamond`/`Lift` facades by the exact `Proper (τ ⧺ src)` and `Proper (τ ⧺ dst)` witnesses; the `src` recursive call needs `Proper.extendList (τ ⧺ dst) υ`, not `Proper.compose (τ ⧺ dst) (Tele.ofList υ)`.
9. **[2026-06-15] Env-centered singleton interaction still needs canonical spines**
   Do instead: do not install a private `Env` bridge alone. The hard theorem still needs explicit coherence between `Γ ⧺ (base ∷ α ⧺ υ)` and `((Γ ⧺ base) ⧺ ⌊α⌋) ⧺ υ`; either keep `TargetProper`/diamond or first build a canonical spine layer for these witnesses.
10. **[2026-05-27] `act_kcomp` reduces to general substitution composition**
   Do instead: use public `Subst.comp` and `Subst.act_comp`; the old `fusion` wrapper is deleted, while `interchange` still supports the `dom` branch of `act_comp`.

## User Directives
1. **[2026-06-16] Avoid defensive Lean witness boilerplate**
   Do instead: add `letI`, type ascriptions, or explicit instance arguments only when they select a computationally necessary `Proper` witness; remove no-op `show ... from rfl` rewrites and tiny tactic wrappers when direct terms elaborate.
2. **[2026-06-14] Present `Equations.lean` thesis-style**
   Do instead: organize explanations/refactors around action, unit/generic application, action-instantiation interaction, composition, and relative-monad laws; use `HigherRankSyntax/equations-math.tex` and `HigherRankSyntax/equations-refactor-plan.md` as the current guide.
3. **[2026-06-14] Treat `preNaturalityLiftAt` as a readability hotspot**
   Do instead: target the PreLift/β-side interaction with named head cases and branch helpers before retrying arbitrary-target diamonds.
4. **[2026-05-19] Collaborator onboarding matters**
   Do instead: keep `PLAN.md` aligned with the active formalization after implementation changes.
