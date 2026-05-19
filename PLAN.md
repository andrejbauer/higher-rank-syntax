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

`Action/*.lean` builds.  `SyntaxMonad : RelativeMonad J` is fully populated
modulo the **one remaining `sorry`** — `lift_inst_commute` (= **L5**) in
`Action/Equations.lean`.  The composition law `comp_lift` is proved modulo
that sorry.

The substitution layer is split across two files:

`Action/Subst.lean` — **machinery**:

* Types: `Subst Γ Δ`, `Inst α Γ`.
* Slot classification: `tauSlot`, `tauSlot_arity`; the `XPos` inductive and
  `classify`; the @[simp] lemmas `classify_weakenList`, `classify_tauSlot`.
* Walkers: `inst.aux α ρ ι τ e : Expr ((Δ ⋈ α) ⋈* τ) → Expr (Ξ ⋈* τ)` (ρ is a
  *Renaming*, three branches via `classify`); `lift.aux σ τ e` (at Γ-slots
  delegates to `inst.aux` with `ρ := Renaming.weakenList Δ τ`).
* Per-case @[simp] unfolders: `inst_aux_ext_eq`, `inst_aux_base_there_eq`,
  `inst_aux_base_here_eq`, `lift_aux_ext_eq`, `lift_aux_base_eq`.
* Helper: `η_fillers`.
* Public wrappers: `inst e ι`, `Subst.lift σ e`.
* Categorical operations: `Renaming.toSubst`, `Renaming.preSubst` (`ʳ∘ˢ`),
  `Subst.postRen` (`ˢ∘ʳ`), `Subst.comp` (`ˢ∘ˢ`).

`Action/Equations.lean` — **theorems** (imports `Subst`):

* `extendList_tauSlot` — naturality of `Renaming.extendList` against `tauSlot`.
* η-side lemmas (private): `inst_aux_η_tauSlot`, `inst_aux_η_inv_of`,
  `inst_aux_η_bundle`, `inst_aux_η`, `inst_aux_η_inv`, `lift_aux_η_tauSlot`.
* `unit_left.aux` (private) and public `unit_left`.
* `L3.aux` (private) and public `L3 : Subst.lift ρ.toSubst e = ⟦ ρ ⇑ʳ α ⟧ʳ e`
  — the categorical embedding lemma.
* Public **`unit_right`** as a one-line corollary of `L3` at `ρ := 𝟙ʳ`.
* **`lift_inst_commute`** (L5, still `sorry`'d).
* `comp_lift.aux` (private) and public `comp_lift` (proved modulo L5).

`Action/Renaming.lean` adds `Renaming.extendList ρ τ : Γ ⋈* τ →ʳ Δ ⋈* τ` and
naturality `extendList_weakenList`, `extendList_id`.

`Action/Expr.lean` adds `Renaming.actExpr_apply'` as a @[simp] unfolder of
`⟦ ρ ⟧ʳ (apply' …)` — avoids motive-correctness issues when rewriting slots
through the dependent witness `hα`.

Termination: `lift.aux` uses `Expr.Subterm.wellFoundedRelation`; `inst.aux`
uses lex `PSigma` over `(C.Arity, Σ Γ, Expr Γ)`.

## Outstanding

Prove **L5** (`lift_inst_commute` in `Action/Equations.lean`).  Plan below.

## Plan for `lift_inst_commute` (L5)

Statement:

```
lift.aux θ τ (inst.aux α (weakenList Δ τ) ι [] e)
  = inst.aux α (weakenList Ε τ)
      (fun j => lift.aux θ (j.arity :: τ) (ι j)) [] (Subst.lift θ e)
```

A direct structural induction on `e` does not close: at the `.here j`
sub-case of `e`'s head (`.here j : Slot (Δ ⋈ α)` with `j : Binder α`), the
walker plugs `ι j : Expr ((Δ ⋈* τ) ⋈ j.arity)` and re-enters `inst.aux` at
`j.arity` with `ρ = 𝟙ʳ` — the source shape is no longer `Δ ⋈ α` and the
inst-walker's own `τ_inst` is no longer `[]`.  So L5 must be generalised in
two directions at once.

### Likely generalisation

```
lift.aux θ (τ_inst ++ τ) (inst.aux α (weakenList Δ τ) ι τ_inst e)
  = inst.aux α (weakenList Ε τ)
      (fun j => lift.aux θ (j.arity :: τ) (ι j))
      τ_inst (lift.aux (Subst.under θ α) τ_inst e)
```

where `Subst.under (θ : Subst Δ Ε) (α : C.Arity) : Subst (Δ ⋈ α) (Ε ⋈ α)`
sends the topmost α-binder to itself and pushes Δ-slots through θ (then
weakens through α on the codomain side).  Type-aligning the two sides needs
`Shape.extList_append : Γ ⋈* (xs ++ ys) = (Γ ⋈* ys) ⋈* xs`; this is
provable by structural recursion on `xs`.

### Induction structure

Lex on `(α, e)`, parallel to `inst_aux_η_bundle`:

* **XPos.ext (τ_inst slot).**  Both sides reduce via `inst_aux_ext_eq` /
  `lift_aux_ext_eq`; recurse on args at deeper `τ_inst`.
* **XPos.base, .there r (Δ-slot).**  Reduces both sides through the
  Δ-renaming chain; recurse on args at deeper `τ_inst`.
* **XPos.base, .here j (α-binder).**  Plugs `ι j` and reenters `inst.aux` at
  `j.arity` (strictly smaller α via `subWf`).  Apply IH at `α := j.arity`.

### Categorical infrastructure likely needed

* `Subst.under θ α` and its compatibility with `Renaming.weaken`.
* A Fubini-style law for nested `inst.aux` at distinct arities — used when
  `Subst.lift θ` on a `.there r` head produces an inst.aux that then sits
  inside the outer `inst.aux α`.
* Inst.aux × renaming naturality (the M1/M2 family from earlier plans).

State each new law with `sorry` and dry-run the L5 proof using them, as we
did for `comp_lift`, before investing in their bodies.

## Warmup lemmas (done, reference)

* `@[simp]` per-case unfolders for `inst.aux` / `lift.aux`:
  `inst_aux_ext_eq`, `inst_aux_base_there_eq`, `inst_aux_base_here_eq`,
  `lift_aux_ext_eq`, `lift_aux_base_eq` (Subst.lean).
* `classify_weakenList`, `classify_tauSlot` (Subst.lean).
* `Renaming.actExpr_apply'`, `Expr.T.map_η` (Expr.lean).
* `Renaming.extendList`, `extendList_id`, `extendList_weakenList`
  (Renaming.lean).
* `extendList_tauSlot`, `inst_aux_η`, `inst_aux_η_inv`, `L3` (Equations.lean).

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

Most recent: dry-run of `comp_lift` validated the four categorical operations
+ L5 + IH (`08f2408`); the conceptual refactor added `L3` (embedding lemma
`Subst.lift ρ.toSubst e = ⟦ ρ ⇑ʳ α ⟧ʳ e`), turned `unit_right` into a
one-liner `(L3 𝟙ʳ e).trans (by simp)`, and split `Subst.lean` into
`Subst.lean` (definitions) + `Equations.lean` (theorems).  Note: Lean's
`private` is file-scoped, so anything moved to `Equations.lean` needed its
mentioned dependencies (`tauSlot`, `classify`, `inst.aux`, `lift.aux`,
`η_fillers`, per-case unfolders) promoted to non-private in `Subst.lean`.

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
