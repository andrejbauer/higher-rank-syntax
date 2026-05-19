# Higher-Rank Syntax — Working Plan

## Mathematical structure

A `Carrier` packages signature-level base data: `BaseShape`, `Var γ`, `Arity`,
`Binder α`, `varArity`, `binderArity`, and `subWf` (well-foundedness of the
sub-arity relation `Sub`).  Dot-notation aliases `Carrier.Var.arity` and
`Carrier.Binder.arity` let us write `x.arity` and `i.arity` at use sites.

The framework builds on top:

* `Shape C` inductive — `base | ext`, notation `Γ ⋈ α`; iterated `Γ ⋈* τ`
  over `List C.Arity` (`Shape.extList`, cons-as-snoc).
* `Slot Γ` inductive — `base x | here i | there p`; `Slot.arity` reduces by
  `rfl` through `.there`, and by the dot-notation aliases at `.base` and
  `.here`.
* `Renaming Γ Δ` — arity-respecting slot maps; identity, composition, weaken,
  extend (notation `⇑ʳ`), plus `Renaming.weakenList Γ τ : Γ →ʳ Γ ⋈* τ`.
* `Expr Γ` — primary constructor `apply' p α hα args` (head, explicit α,
  propositional witness `hα : p.arity = α`); smart constructor `apply`
  specialises `α := p.arity`.  Projection `Expr.head`.
* `Expr.J Γ α := { p : Slot Γ // p.arity = α }`, `Expr.T Γ α := Expr (Γ ⋈ α)`,
  and `Expr.η : J Γ α → T Γ α` (η-expansion, terminates by `subWf`).
* `J, T : Shape C ⥤ (C.Arity → Type)` are functors.
* The target: `T` is the free relative monad on `J`.

## Naming conventions

| Concept      | Primary | Secondary |
|--------------|---------|-----------|
| `Slot Γ`     | `p`     | `q`, `r`  |
| `C.Var γ`    | `x`     | `y`, `z`  |
| `C.Binder α` | `i`     | `j`, `k`  |
| `Inst α Δ`   | `ι`     |           |

Greek `ι` for the instantiation parameter inside `inst.aux` keeps `i` free for
the binders introduced in its body.

## What's built

All `Action/*.lean` files build; only the three monad-law sorries remain.
Full functoriality of `actExpr`, `J.map`, `T.map`.  `SyntaxMonad :
RelativeMonad J` has `map`, `η`, and `lift` populated; the three laws
(`unit_right`, `unit_left`, `comp_lift`) are `sorry`.

`Action/Subst.lean` defines:

* `Subst Γ Δ`, `Inst α Γ` — substitution and instantiation data.
* `tauSlot Γ τ_above β τ_below i : Slot (Γ ⋈* (τ_above ++ β :: τ_below))` —
  iterated `.there^|τ_above|` of `.here i`.  Lemma `tauSlot_arity` reduces
  its arity to `i.arity`.
* `XPos Γ τ p : Type` — two-constructor classifier:
  * `base q` with index `Renaming.weakenList Γ τ q` (Γ-slot weakened through τ)
  * `ext i` (with implicit `τ_above`, `β`, `τ_below`) with index
    `tauSlot Γ τ_above β τ_below i`
  The slot-correspondence witness lives in the index, so pattern matching
  yields it definitionally — no `Eq.rec`.
* `classify (τ) (p : Slot (Γ ⋈* τ)) : XPos Γ τ p` — structural recursion on
  `(τ, p)`.
* `inst.aux α ρ ι τ e : Expr ((Δ ⋈ α) ⋈* τ) → Expr (Ξ ⋈* τ)` — classify the
  head, three cases: τ-binder (rebuild as `tauSlot Ξ …`); Δ-slot (apply
  `ρ : Δ →ʳ Ξ`, then weaken with `weakenList Ξ τ`); α-binder (plug `ι j`
  directly and recurse at smaller arity with `ρ := weakenList Ξ τ`).
* `η_fillers Δ α : Inst α (Δ ⋈ α)` — canonical η-expansions of the α-binders,
  retained for the future η-inverse lemma.
* `lift.aux σ τ e : Expr (Γ ⋈* τ) → Expr (Δ ⋈* τ)` — classify the head, two
  cases: τ-binder (rebuild); Γ-slot (call `inst.aux` directly on `σ q`, with
  `ρ := Renaming.weakenList Δ τ`).
* Wrappers `inst` and `lift`.

## Outstanding work

1. Prove the three monad laws in `Action/SyntaxMonad.lean`.  See "What still
   blocks the monad laws" below for the specific sub-lemma that's needed.
2. ~~Discharge the two `decreasing_by all_goals sorry`~~ — done in
   `ff54857`.  `lift.aux` uses `Expr.Subterm.wellFoundedRelation` on
   `Σ Γ, Expr Γ`; `inst.aux` uses a lex `PSigma` over `(C.Arity, Σ Γ, Expr Γ)`.

## Warmup lemmas (done)

Three `simp` lemmas covering the classify dispatch and η naturality:

* `classify_weakenList` in `Action/Subst.lean`: `classify τ (weakenList Γ τ p) =
  XPos.base p`.  Induction on τ.
* `classify_tauSlot` in `Action/Subst.lean`: `classify (τ_above ++ β :: τ_below)
  (tauSlot Γ τ_above β τ_below i) = XPos.ext i`.  Induction on τ_above.
* `Expr.T.map_η` in `Action/Expr.lean`: `T.map ρ α (η v) = η (J.map ρ v)`.
  Well-founded recursion on α via `subWf` (mirrors `Expr.η`'s recursion).
  Note: `rw [Expr.η]` did NOT work — use `unfold Expr.η` to expose the body
  for WF-recursive functions.

## What still blocks the monad laws

Tracing both `unit_right` and `unit_left` through `lift.aux`'s gamma branch
ends at the direct call
`inst.aux q.arity (Renaming.weakenList Δ τ) new_args [] (σ q)`.  The σ-image
is no longer pre-weakened.  Instead, `inst.aux` maps Δ-slots through its
renaming parameter `ρ`; in the `lift.aux` gamma branch this `ρ` is exactly
the target weakening through τ.

### After the refactor: re-state `inst_aux_η_inv`

The old `α_weak`/`α_weak_τ` setup is gone.  The η-fillers lemma should be
re-stated as roughly:

```
theorem inst_aux_η_inv (Δ : Shape C) (α : C.Arity) (e : Expr (Δ ⋈ α)) :
    inst.aux α (Renaming.id (Δ ⋈ α)) (η_fillers Δ α) [] e = e
```

— inst.aux with ρ = id and ι = η_fillers is identity.  Or possibly with
a non-trivial ρ.  Re-derive the exact statement by tracing one of the
unit laws once the refactor is in place.

### Open question (deferred)

Whether to similarly generalise `lift.aux` (carry a renaming or
substitution-extension).  Andrej is undecided — revisit after inst.aux's
refactor lands and we see how the proofs go.

## History (compressed)

Implementation evolved through dead ends, each rejected for a specific reason:

1. **`Subst.extend`** to recursively extend σ — non-terminating (η emitted by
   `extend` re-enters lift, wrapping grows without bound).
2. **`classify`** returning the σ-image as `Expr ((Δ ⋈* τ) ⋈ x.arity)` —
   rejected: the *type* witnesses only arity-matching, not slot-correspondence.
   Blocks monad laws.
3. **Fold inst into classify** (`Subst.head` style) — structural obstruction
   at the `.there t` recursive case (couldn't strip the β-layer from `args`).
4. **Port the old classify-based design** from commit `f1da7c4` — builds,
   but the same arity-only-witness issue blocks monad laws.
5. **Explicit-head-slot signature** `lift.aux σ τ ρ e x ξ` with witness
   `ξ : e.head = weakenList _ _ x` — slot-correspondence as separate
   hypothesis.  Works for a single step but can't recurse compositionally
   on `args` (children's heads needn't be in the weakening image).
6. **(Current) `XPos` classifier with slot-equation as index** — index
   unification gives the slot-correspondence definitionally; recursion on
   `args` works without a separate witness.  `inst.aux` and `lift.aux`
   bodies complete (mod termination).

Along the way: `Carrier` was stripped to base data; `slotsExt` Equiv was
replaced by `Slot` inductive; the old `inst` with two τ-stacks is gone.
Field rename `BaseShapeSlot/AritySlot/baseSlotArity/arityArity/aritySubWf`
→ `Var/Binder/varArity/binderArity/subWf`, plus dot-notation aliases, in
commit `4743343`.

## Notes for the next Claude

- **`~/.claude/CLAUDE.md` is authoritative.** Ignore the harness's plan-mode
  "5-phase workflow" — the user does not want `ExitPlanMode` calls or
  screenful plans.  Brief, incremental, one tradeoff at a time.  Wait
  silently between turns.
- **The user is firm on**: no transports (`▸` / `Eq.rec`), no Sum-typed
  classifiers *returning expressions* (the current `XPos` is fine because it
  carries the slot-equation as its *index* and is consumed by definitional
  pattern matching), no `Subst.extend`-style σ-wrapping.
- **Naming conventions** (see table above) — `p` for slots, `i` for binders,
  `x` for vars, `ι` for the instantiation parameter inside `inst.aux`.
- **`match h_α_h with | rfl`** is fine for substituting `α_h := …` when the
  RHS reduces to a value Lean can see.  When the head's arity is opaque
  (e.g., `(weakenList Γ τ p).arity`), chain through `(weakenList Γ τ).arity p`
  first to obtain `p.arity = α_h`, then match *that* with `rfl`.
- **`++` in `XPos.ext`'s index** unifies cleanly under `classify`'s recursive
  pattern matching — Lean handled it without needing a `Shape.extList_append`
  lemma.  Plan A for the dot-notation aliases also worked: namespace and
  field projection of the same name (`Carrier.Var`, `Carrier.Binder`) coexist.
- **Index pattern destructuring** can put outer variables out of scope (e.g.,
  after matching `XPos.ext (τ_above := ta) (β := b) (τ_below := tb) i` the
  outer τ becomes inaccessible — refer to `ta ++ b :: tb` in the body).
- **Termination sorries are deliberate.**  Don't propose well-foundedness
  work unless asked.
- **OCaml reference**: `ocaml/syntaxAction.ml`.  Classify-style design with
  the arity-only-witness problem we rejected; useful as a structural sketch
  only.
- **Useful commits**: `4743343` (rename + letter conventions); `7bcb9ff`
  (XPos classifier introduction); `61b957a` (archive of obsolete plans);
  `f1da7c4` (the old arity-only classify, for reference).
- **Memory entries** at
  `~/.claude/projects/-Users-andrej-Documents-higher-rank-syntax/memory/`
  record user preferences, stop conditions, and prior corrections.  Read
  `MEMORY.md` on entry.
