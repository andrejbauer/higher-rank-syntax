# Higher-rank syntax — project working rules

These rules OVERRIDE default behavior. Follow them exactly, every session.

## Ask, don't work around

Ask for what you need — a missing lemma, a design decision, a clarification, a
fact about the code — rather than building a workaround. Workarounds and
instance hacks are not wanted; when something is missing or unclear, stop and
ask.

## Never copy from the reference files

`Equations.lean` and `Equations2.lean` are RETIRED REFERENCES, kept only until
the rewrite is finished. Read them ONLY for hints: which cases are hard, the
rough shape of an argument. NEVER copy a statement, definition, inductive (e.g.
a bespoke dispatch type), proof, tactic block, or piece of terminology into the
live files. Everything live must be DERIVED from the current code's own
obligations. If you notice yourself transcribing from a reference, stop and redo
by deriving.

## Methodology: derive top-down, make the statement fit the use site

- Before stating an auxiliary, OBSERVE the actual proof obligation it must
  serve (inspect the goal at the real call site). State the auxiliary to FIT
  that obligation.
- Auxiliary statements must not be over-specialized to the call site; make an effort
  to make them mathematically sensible stand-alone statements.
- When formulating an auxiliary statement, test it immediately at the call site,
  where it should be usable without too many complications. If it needs heavy
  massaging to apply, consult the user.
- Breadth-first: when a proof splits into branches, explore each briefly to see
  the structure before deep-diving any one.

## Declare-and-halt

Before each tactic, write one line stating the single expected proof-state
outcome. Run only that tactic, then compare. On ANY deviation (error,
"no progress", "pattern not found", a goal other than predicted) the turn ENDS:
quote the verbatim outcome and wait. No second attempt, no switching tactic
family, no changing lemmas/args, no "let me try one thing". Carve-out: fix a
genuine typo and rerun the SAME intended tactic.

## Naming

- Shapes / telescopes: UPPER-CASE Greek only — `Γ Δ Ξ Θ Ψ Ω Φ Π Σ Λ`. Never
  lowercase words (`pre`, `dom`, `cod`, `src`, `dst`) and never lowercase Greek
  (`τ`) for a shape.
- Substitutions: `σ θ κ`. Slots / binders / indices: lowercase (`x z w i j`).
- No abbreviations. For a pair of related things pick two distinct letters,
  never an `X_in` / `X_out` suffix scheme.

## Comments and docstrings

Economic; only current-state WHAT-facts about the identifier being documented.
FORBIDDEN:
- Invented terminology (e.g. "passive", "under-depth", "fuel") and any term
  borrowed from the reference files.
- Rationale, history, "forced by the recursion", comparisons to other systems.
- Content-free descriptions such as "the `τ = nil` instance of `X`" — state what
  the thing actually asserts.
If you cannot say something specific and true, write nothing.

## Idiomatic Lean

- Never use `show` or `change` to reshape a goal. Exploit definitional equality
  through term-mode, `apply` / `exact` / `calc` / `rw`.
- No large hand-written proof terms. No multi-line `⟨…⟩` anonymous-constructor blocks.

## Proper / Subsingleton

`Proper Γ` is a subsingleton (`Proper.subsingleton`); keep it an `instance` so
`Subsingleton.elim` / `convert` discharge `Proper`-witness mismatches by
synthesis rather than by hand.

## Communication

Terse. No long textual explanations of findings.

Show directly what is wrong, do not explain it with elaborate text.
Examples: show the equation that is mismatched; show proof structure as pseudo-code,
tactic skeletons, or relevant snippets of code.

## Experimenting with sorries

It is OK to edit the live files while experimenting, as long as the edits just fill in
`sorry`s or are very easy to revert. No need to hide experiments from the user,
on the contrary - it is counter-productive to hide attempts from the user and then
describe them with words. Show the attempts, leave them sitting in the code.

If you intend to communicate about an unfinished or unsuccessful attempt with the
user, leave it in IN PLACE at the stuck point. Do NOT revert to a bare `sorry` and
explain in words what went wrong — that hides the work. Show the stuck place in
the file.

## When stuck

Report at the FIRST failure or first sign of thrashing: surface the exact
symptom and either one proposed next step or wait. Do not iterate workarounds.
Do not auto-revert when admonished — leave the change and wait.

## Build / environment

Never trigger a Mathlib source compile (halt and let me run `lake exe cache get`).
Never install software. Remote/local git mutations need explicit approval.
