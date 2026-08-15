# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-06-23] Verify Lean snippets locally**
   Do instead: use the project toolchain or Lean LSP on minimal snippets before giving Lean/mathlib API advice.
2. **[2026-06-26] Rebuild changed Lean interfaces**
   Do instead: after changing exported theorem signatures, use `lake build Target` for downstream checks; `lake env lean File.lean` may read stale imported `.olean`s.

## Shell & Command Reliability
1. **[2026-06-23] Prefer focused shell reads**
   Do instead: use `rg`, `sed`, `ls`, and related commands directly with concise output, and parallelize independent reads when useful.

## Domain Behavior Guardrails
1. **[2026-08-08] Distinguish ordinary and protected-prefix lifting**
   Do instead: use `Subst.liftPrefixed` for substitutions `Γ → S ⋈ Δ`; ordinary `Subst.lift` treats the entire codomain as unprotected and does not state the required action-below-`S` law.
2. **[2026-08-03] Prove telescope-tensor coherence through base extension**
   Do instead: package `Subst.lift_one` and `Subst.lift_assoc` as the natural isomorphisms `extendByOne` and `extendByAssoc`; use functorial images of those isomorphisms for unitor/associator transport.
3. **[2026-08-03] Use HEq at dependent telescope-tensor projections**
   Do instead: name the transported sigma value, strip whole-sigma and component transports with small `castObj_heq` projection lemmas, and finish with `Sigma.ext`; broad cast simplification becomes brittle.
4. **[2026-08-03] Telescope reindexing uses a specialized pushforward**
   Do instead: define `Subst.lift σ Φ` minimally as `pushforward σ id`, use it for concatenation naturality, and derive its action comparison from `act_interchange` without a parallel theorem hierarchy.
5. **[2026-06-23] Carrier product slots need cover**
   Do instead: use `Carrier.cover` to split arbitrary `Γ ⋈ Δ` slots; `classify_inl`/`classify_inr` only handle injected slots.
6. **[2026-08-03] Extract decorated prefixes through precedence factorization**
   Do instead: cast the ambient decoration along `Precedence.factor x` to `before x ⋈ after x`, then restrict classifier paths through `Carrier.inl`.
7. **[2026-08-03] Compare dependent decoration paths through packed sites**
   Do instead: package a path and its precedence prefix in a sigma, apply `congrArg` along carrier slot coherences, use `classifierFromSite_congr`, and normalize classifier transports with `cast_comp`.
8. **[2026-08-03] Eliminate dependent product-slot data through a sigma**
   Do instead: use `Carrier.copair` into `Σ Λ, F Λ`, then transport along the precedence equality; `Carrier.cover` is Prop-valued and cannot itself eliminate into classifier data.
9. **[2026-06-24] Reassociate nested product slots with Carrier coherences**
   Do instead: use `C.inr_inl`, `C.inr_inr`, and `C.inl_inl` before recursive η/substitution calls whose slot lives across `Γ * (Δ * Ξ)` versus `(Γ * Δ) * Ξ`.
10. **[2026-06-23] Match project mathlib version**
   Do instead: inspect `lean-toolchain`/`lakefile.toml` or run local Lean checks when API names may vary by version.

## User Directives
1. **[2026-08-10] Keep foundational syntax discussions exploratory and explicit about uncertainty**
   Do instead: separate settled constraints, candidate definitions, and unresolved forks; do not disguise a speculative construction as a polished final model.
2. **[2026-08-03] Implement staged roadmaps one pass per turn**
   Do instead: update the active roadmap, build and report the current pass, state the next pass, and stop before implementing it.
3. **[2026-06-23] Keep Lean answers practical**
   Do instead: include a minimal compiling example and explain the key imported names.
