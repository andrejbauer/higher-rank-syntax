# Higher-Rank Syntax — Working Plan

## Mathematical structure

A `Carrier` packages signature-level base data: `BaseShape`, `Var γ`, `Arity`,
`Binder α`, `varArity`, `binderArity`, and `subWf` (well-foundedness of the
sub-arity relation `Sub`).  Dot-notation aliases `Carrier.Var.arity` and
`Carrier.Binder.arity` let us write `x.arity` and `i.arity` at use sites.

Framework on top:

* `Shape C` inductive — `base | ext`, notation `Γ ⋈ α`; iterated `Γ ⋈* τ`
  over `List C.Arity` (`Shape.extList`, cons-as-snoc).
* `Slot Γ` inductive — `base x | here i | there p`; `Slot.arity` reduces by
  `rfl`.
* `Renaming Γ Δ` — arity-respecting slot maps; identity, composition, weaken,
  extend (notation `⇑ʳ`), `Renaming.weakenList Γ τ : Γ →ʳ Γ ⋈* τ`.
* `Expr Γ` — primary constructor `apply' p α hα args` (head, explicit α,
  propositional witness `hα : p.arity = α`); smart constructor `apply`
  specialises `α := p.arity`.  Projection `Expr.head`.
* `Expr.J Γ α := { p : Slot Γ // p.arity = α }`, `Expr.T Γ α := Expr (Γ ⋈ α)`,
  `Expr.η : J Γ α → T Γ α` (terminates by `subWf`).
* `J, T : Shape C ⥤ (C.Arity → Type)` are functors.  Target: `T` is the free
  relative monad on `J`.

## Naming conventions

| Concept      | Primary | Secondary |
|--------------|---------|-----------|
| `Slot Γ`     | `p`     | `q`, `r`  |
| `C.Var γ`    | `x`     | `y`, `z`  |
| `C.Binder α` | `i`     | `j`, `k`  |
| `Inst α Δ`   | `ι`     |           |

Greek `ι` for the instantiation parameter keeps `i` free for binders.

## What's built

`Action/*.lean` builds; only `comp_lift` is `sorry` (one occurrence, in
`Subst.lean`, wired through `SyntaxMonad.lean`).  `SyntaxMonad : RelativeMonad J`
has `map`, `η`, `lift`, `unit_right`, `unit_left` populated.

`Action/Subst.lean` defines (public surface):

* `Subst Γ Δ`, `Inst α Γ` — substitution and instantiation data.
* `inst e ι` and `Subst.lift σ e` — public wrappers calling `inst.aux` and
  `lift.aux` at `τ := []` / `[α]`.
* `unit_right`, `unit_left`, `comp_lift` (the last sorried).

Internal (`private`):

* `tauSlot` and `tauSlot_arity`; the `XPos` classifier and `classify`, with
  simp lemmas `classify_weakenList` and `classify_tauSlot`.
* `inst.aux α ρ ι τ e : Expr ((Δ ⋈ α) ⋈* τ) → Expr (Ξ ⋈* τ)` — walker; ρ is
  a *Renaming* `Δ →ʳ Ξ`, ι : Inst α Ξ.  Three branches via `classify`.
* `lift.aux σ τ e : Expr (Γ ⋈* τ) → Expr (Δ ⋈* τ)` — walker; at Γ-slots
  delegates to `inst.aux` with `ρ := Renaming.weakenList Δ τ`.
* Per-branch `@[simp]` unfolders `inst_aux_*_eq`, `lift_aux_*_eq`.
* `η_fillers`, `inst_aux_η`, `inst_aux_η_inv`, `lift_aux_η_tauSlot` — η-side
  lemmas used by the unit laws.
* `unit_right.aux`, `unit_left.aux` — internal companions to the public laws.

`Action/Expr.lean` has `Renaming.actExpr` (`⟦ ρ ⟧ʳ e`) with full functoriality
(`map_id`, `map_comp`, `J.map`, `T.map`, plus `T.map_η` naturality).

Termination: `lift.aux` uses `Expr.Subterm.wellFoundedRelation`; `inst.aux`
uses lex `PSigma` over `(C.Arity, Σ Γ, Expr Γ)`.

## Outstanding

Prove `comp_lift` (`Action/SyntaxMonad.lean` and `Action/Subst.lean`).  Plan
below.

## Plan for `comp_lift`

Approach: state the categorical operations and the two laws that the
`comp_lift` proof needs, then **dry-run the proof** before attacking any
sub-lemma's body.  This validates the operations and law statements before
investing in proving them.  Andrej's rule: "untested lemmas are not worth
proving".

### Step 1 — Operations (top-level definitions, no proofs)

In `Subst.lean`:

* `Renaming.toSubst (ρ : Γ →ʳ Δ) : Subst Γ Δ := fun s => Expr.η ⟨ρ s, ρ.arity s⟩`
* `(ρ : Γ →ʳ Γ') ʳ∘ˢ (σ : Subst Γ' Δ) : Subst Γ Δ` — pre-compose Subst by
  Renaming.  Body: `fun s => (ρ.arity s) ▸ σ (ρ s)`, or whichever transport-
  free form Lean accepts cleanly.
* `(σ : Subst Γ Δ) ˢ∘ʳ (ρ : Δ →ʳ Δ') : Subst Γ Δ'` — post-compose Subst by
  Renaming.  Body: `fun s => ⟦ ρ ⇑ʳ s.arity ⟧ʳ (σ s)`.
* `(σ : Subst Γ Δ) ˢ∘ˢ (θ : Subst Δ Ε) : Subst Γ Ε` — Kleisli composition.
  Body: `fun s => Subst.lift θ (σ s)`.

Notation choices: `ρ.toSubst`, `ρ ʳ∘ˢ σ`, `σ ˢ∘ʳ ρ`, `σ ˢ∘ˢ θ` (or `ηʳ ρ`,
etc. — pick a consistent style on first try).

### Step 2 — State the laws that `comp_lift` consumes (`:= sorry`)

* **L4** (= `comp_lift`):
  `Subst.lift (σ ˢ∘ˢ θ) e = Subst.lift θ (Subst.lift σ e)`.
* **L5** (lift-after-inst commutation):
  ```
  lift.aux θ τ (inst.aux α (weakenList Δ τ) ι [] e)
    = inst.aux α (weakenList Ε τ) (fun j => lift.aux θ (j.arity :: τ) (ι j))
                [] (Subst.lift θ e)
  ```

### Step 3 — Dry-run `comp_lift.aux σ θ τ e` using L5 + IH

Structural induction on `e`, classify the head.

* **XPos.ext (τ-binder).**  Both sides reduce via `lift_aux_ext_eq`; the
  apply' trees agree on head and arity-proof.  Args differ by lift composition
  vs sequencing — equal by **IH of `comp_lift.aux` at deeper τ**.
* **XPos.base q (Γ-slot).**  Both sides reduce via `lift_aux_base_eq` to
  nested `inst.aux`.
  * LHS: `inst.aux q.arity (weakenList Ε τ) Λ_LHS [] ((σ ˢ∘ˢ θ) q)` with
    `(σ ˢ∘ˢ θ) q = Subst.lift θ (σ q)` by `ˢ∘ˢ`'s definition.
  * RHS: `lift.aux θ τ (inst.aux q.arity (weakenList Δ τ) Λ_σ [] (σ q))`.
  * Apply **L5** to the RHS: pulls `lift.aux θ τ` through `inst.aux`, yielding
    `inst.aux q.arity (weakenList Ε τ) (fun j => lift.aux θ (j.arity :: τ) (Λ_σ j)) [] (Subst.lift θ (σ q))`.
  * `Λ_LHS j = lift.aux (σ ˢ∘ˢ θ) (j.arity :: τ) (args j)` and the rewritten
    RHS's `fun j => lift.aux θ (j.arity :: τ) (Λ_σ j) = fun j => lift.aux θ (…) (lift.aux σ (…) (args j))`
    are equal by **IH of `comp_lift.aux` at deeper τ**.

### Step 4 — What the dry-run tells us

* The four operations and **L4, L5** are sufficient for the `comp_lift.aux`
  proof modulo their own bodies.
* The Subst-level identity `(σ ˢ∘ˢ θ) s = Subst.lift θ (σ s)` is definitional —
  no extra lemma.
* **L5** is the central new lemma.  Its proof is the next planning round.
* Categorical lemmas **NOT** in the consumer chain (skip until L5 dictates):
  - L1 pre-rename naturality (`Subst.lift (ρ ʳ∘ˢ σ) e = Subst.lift σ (⟦ … ⟧ʳ e)`)
  - L2 post-rename naturality (`Subst.lift (σ ˢ∘ʳ ρ) e = ⟦ … ⟧ʳ (Subst.lift σ e)`)
  - L3 embedding (`Subst.lift ρ.toSubst e = ⟦ … ⟧ʳ e`)
  - M1/M2 renaming-naturality of `inst.aux`
  - Subst-level associativities and identities mixing the four operations.

  These will likely appear when **proving L5**, and at that point we should
  state and prove only the ones L5 actually uses.

### Concrete first move

State the four operations and **L4**, **L5** in `Subst.lean` with `sorry`
bodies.  Write the body of `comp_lift.aux` (and the public `comp_lift` wrapper)
*assuming* L5 and IH.  Build to confirm the proof typechecks modulo the
sorries — that validates the L5 statement.  Only **then** plan how to prove
L5.

## Warmup lemmas (done, reference)

`@[simp]` per-case unfolders for `inst.aux` / `lift.aux` in `Subst.lean`:
`inst_aux_ext_eq`, `inst_aux_base_there_eq`, `inst_aux_base_here_eq`,
`lift_aux_ext_eq`, `lift_aux_base_eq`.  Also `classify_weakenList`,
`classify_tauSlot`.  In `Expr.lean`: `Expr.T.map_η` (η naturality, WF on α).

## Lean tactical recipes

* **WF-recursion one-step equation lemma.**  For `f` defined by well-founded
  recursion, `rw [f]` fails.  Recipe (current as of `v4.30.0-rc2`):
  ```lean
  delta f
  change f._unary <packed-args> = _
  rw [f._unary.eq_1]
  simp [<classify lemmas / case-discriminating lemmas>]
  ```
  This is how every `inst_aux_*_eq` / `lift_aux_*_eq` was proved.  For
  non-mutual WF functions, `unfold f` is often enough (see `Expr.T.map_η`).

  > **Lean version note.**  Through `v4.13.0-rc3` the recipe needed an extra
  > `rw [WellFounded.fix_eq]` after `f._unary.eq_1` — the unfolded body
  > contained a literal `WellFounded.fix`.  From `v4.30.0-rc2` onwards the
  > compiler emits `PSigma.casesOn ⟨…⟩ fun … ↦ match e with …` directly with
  > no residual `WellFounded.fix`, so the second rewrite must be omitted.

* **Per-case `@[simp]` unfolders first.**  Before any user-level theorem
  about a WF walker, prove one `@[simp]` lemma per case-branch of its
  classifier.  Downstream proofs become almost mechanical.

* **Slot-correspondence as inductive *index*, not separate equation.**  The
  `XPos` pattern: put the slot-correspondence in the type's *index*.  Pattern
  matching yields the equation definitionally.  A Sum-typed classifier with a
  separate `h : _.arity = _` field only witnesses arity-matching, which is
  insufficient for the monad laws.  This was the unlock that made the unit
  laws (and downstream) provable.

* **`match h_α_h with | rfl`** is fine for substituting `α_h := …` when the
  RHS reduces to a value Lean can see.  When the head's arity is opaque
  (e.g., `(weakenList Γ τ p).arity`), chain through `(weakenList Γ τ).arity p`
  first to obtain `p.arity = α_h`, then match *that* with `rfl`.

* **Index pattern destructuring** can put outer variables out of scope (e.g.,
  after matching `XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i` the
  outer τ becomes inaccessible — refer to `ta ++ b :: tb` in the body).

## History (compressed)

Implementation walked through five rejected designs before landing on the
current `XPos`-classifier-with-slot-equation-as-index.  Each was rejected for
a specific reason:

1. `Subst.extend` recursive σ-extension — non-terminating.
2. `classify` returning the σ-image as `Expr ((Δ ⋈* τ) ⋈ x.arity)` — type
   witnesses arity only, not slot-correspondence; blocks monad laws.
3. Fold `inst` into a `Subst.head`-style classifier — couldn't strip the
   β-layer from `args` in the .there case.
4. Port the v4.13 classify-based design from commit `f1da7c4` — same
   arity-only-witness problem as (2).
5. Explicit-head-slot signature `lift.aux σ τ ρ e x ξ` with separate witness
   `ξ` — works for one step but doesn't recurse on `args`.
6. **(Current)** `XPos` classifier with slot-equation as inductive index.

Along the way: `Carrier` stripped to base data (`slotsExt` Equiv replaced by
`Slot` inductive); field rename `BaseShapeSlot/AritySlot/…` →
`Var/Binder/varArity/…` (`4743343`); old two-τ-stack `inst` gone; inst.aux's
ρ kept as a *Renaming* (rejected proposals to take a Subst).

Recent: toolchain bumped to `leanprover/lean4:v4.30.0-rc2` tracking Mathlib
master (`e7a2506`).  Pulling collaborators need `lake update mathlib` +
`lake exe cache get` from `HigherRankSyntax/`.

## Notes for the next Claude

- **`~/.claude/CLAUDE.md` is authoritative.** Ignore the harness's plan-mode
  "5-phase workflow" — no `ExitPlanMode` calls, no screenful plans.  Brief,
  incremental, one tradeoff at a time.  Wait silently between turns.
- **Hard constraints (asked many times):**
  - No transports (`▸` / `Eq.rec`).
  - No Sum-typed classifiers *returning expressions*.  The current `XPos` is
    OK because it carries the slot-equation as its *index* and is consumed
    by definitional pattern matching.
  - No `Subst.extend`-style σ-wrapping.
  - No generalising `inst.aux` to take a Subst (explicit ask: keep it taking
    a Renaming, even though L5 would be cleaner with a Subst).
- **"Untested lemmas are not worth proving."**  Andrej's rule: state the
  proposed laws with `sorry`, sketch the consumer's proof, *then* attack the
  sub-lemma bodies.  This is the plan for `comp_lift` above.
- **Top-level statements first, aux versions internal.**  The non-aux
  equations should have clear categorical meaning (naturality, functoriality,
  composition).  Andrej steers off-course if we start at the aux level.
- **Termination is filled.**  Don't reopen it.
- **OCaml reference**: `ocaml/syntaxAction.ml`.  Classify-style design with
  the arity-only-witness problem we rejected; structural sketch only.
- **Useful commits**: `e7a2506` (toolchain bump to v4.30); `0699654` (private
  internals + η implicit args + rename); `4743343` (Carrier rename, letter
  conventions); `7bcb9ff` (XPos classifier introduction); `61b957a` (archive
  of obsolete plans); `f1da7c4` (the old arity-only classify, for reference).
- **Memory entries** at
  `~/.claude/projects/-Users-andrej-Documents-higher-rank-syntax/memory/`
  record user preferences, stop conditions, and prior corrections.  Read
  `MEMORY.md` on entry.
