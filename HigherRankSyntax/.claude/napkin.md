# Napkin Runbook

## Curation Rules
- Re-prioritize on every read.
- Keep recurring, high-value notes only.
- Max 10 items per category.
- Each item includes date + "Do instead".

## Execution & Validation (Highest Priority)
1. **[2026-06-20] Prefer local Lean validation**
   Do instead: run focused Lean/LSP checks from the repo root before claiming integration changes work.
2. **[2026-06-20] Lean MCP command**
   Do instead: use Codex MCP `lean-lsp`, configured as `/home/imfm/.local/bin/uvx lean-lsp-mcp` with `LEAN_PROJECT_PATH=/home/imfm/higher-rank-syntax/HigherRankSyntax`.

## Shell & Command Reliability
1. **[2026-06-20] Network installs may need escalation**
   Do instead: try the package-manager command once normally; if DNS/index access fails, rerun with `require_escalated`.

## Domain Behavior Guardrails
1. **[2026-06-20] Preserve user Lean work**
   Do instead: inspect git status first and avoid reverting unrelated Lean or config edits.

## User Directives
1. **[2026-06-20] Lean MCP is welcome**
   Do instead: when Lean tooling would help, prefer the configured `lean-lsp-mcp` server if available.
