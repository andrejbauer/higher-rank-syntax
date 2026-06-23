# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-06-23] Verify Lean snippets locally**
   Do instead: use the project toolchain or Lean LSP on minimal snippets before giving Lean/mathlib API advice.

## Shell & Command Reliability
1. **[2026-06-23] Prefer focused shell reads**
   Do instead: use `rg`, `sed`, `ls`, and related commands directly with concise output, and parallelize independent reads when useful.

## Domain Behavior Guardrails
1. **[2026-06-23] Carrier product slots need cover**
   Do instead: use `Carrier.cover` to split arbitrary `Γ ⋈ Δ` slots; `classify_inl`/`classify_inr` only handle injected slots.
2. **[2026-06-23] Match project mathlib version**
   Do instead: inspect `lean-toolchain`/`lakefile.toml` or run local Lean checks when API names may vary by version.

## User Directives
1. **[2026-06-23] Keep Lean answers practical**
   Do instead: include a minimal compiling example and explain the key imported names.
