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

All `Action/*.lean` files build (only `decreasing_by all_goals sorry` and the
three monad-law sorries remain).  Full functoriality of `actExpr`, `J.map`,
`T.map`.  `SyntaxMonad : RelativeMonad J` has `map`, `η`, and `lift`
populated; the three laws (`unit_right`, `unit_left`, `comp_lift`) are `sorry`.

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
* `inst.aux α ι τ e : Expr ((Δ ⋈ α) ⋈* τ) → Expr (Δ ⋈* τ)` — classify the
  head, three cases: τ-binder (rebuild as `tauSlot Δ …`); Δ-slot (rebuild
  with `weakenList Δ τ`); α-binder (plug `ι j` weakened through τ, recurse
  at smaller arity).
* `lift.aux σ τ e : Expr (Γ ⋈* τ) → Expr (Δ ⋈* τ)` — classify the head, two
  cases: τ-binder (rebuild); Γ-slot (weaken `σ q` through τ, then `inst.aux`).
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
ends at the same point: `inst.aux α ι [] (η <weakened slot>)`.

In `unit_right` this `inst.aux` call needs to return `apply' p α_h h_α_h
args` — the same expression we started with.  The Δ-slot branch peels one
`.there`, but recurses on `inst.aux` of each η-child.  Each η-child is
`η ⟨.here i, _⟩`, which fires the α-binder case (since `.here i` is a binder
of α), producing yet another `inst.aux` at smaller arity `i.arity` on
`weakened (ι i)`.  By `subWf` this terminates, but the proof has to capture
"the chain of `inst.aux` calls on η-images of binders unwinds to give back
the original `args`".

The required generalised lemma is roughly:

```
inst.aux α ι τ (η-expansion-image) =
  apply' (corresponding-slot) … (corresponding-new-args)
```

with two flavours depending on whether the η's slot is `.there p` (Γ-slot,
which gives the Δ-slot rebuild) or `.here i` (binder, which plugs ι and
recurses at `i.arity`).

### Attempted in session and learned

Tried the smallest natural form:

```
inst.aux α ι [] (Expr.η Δ α ⟨w, hw⟩) = Expr.apply' w α hw ι
```

This is *too small*.  Proof can't close at this granularity:

* Outer `.there w` head → `.there r` branch produces `apply' w α _ new_args_inst`.
* Need `new_args_inst = ι`.  But `new_args_inst i = inst.aux α ι [i.arity]
  (η-child i)`; inside, `.here i` fires the α-binder branch with
  `ι i` weakened by `R := (weakenList Δ [i.arity]) ⇑ʳ i.arity`, and recurses
  to `inst.aux i.arity new_args' [] (⟦ R ⟧ʳ (ι i))`.
* For arbitrary `ι i` this final recursion has no reason to return `ι i` —
  it depends on `new_args'` acting as a *left inverse* of weakening along `R`.

So the real load-bearing fact is a separate "inst-aux undoes weakening
under η-style fillers" lemma — not just one statement about η-images.
Likely shape:

```
inst.aux α (η-fillers Δ α τ) τ (⟦ (weakenList Δ τ) ⇑ʳ α ⟧ʳ e) = e
```

where `η-fillers Δ α τ : Inst α (Δ ⋈* τ)` is the canonical instantiation by
η-extensions.  Once this is in hand, the η-image equation follows.  Proof
by induction on `e` (Expr.Subterm); the α-binder case will need a
companion lemma by `subWf` on α (analogous to `Expr.T.map_η`).

`unit_left` lands on the same gamma branch but with σ being arbitrary `f`
(rather than η).  The same sub-lemma's "Δ-slot rebuild" + "binder plug"
machinery is what gets us back to `f α v`.

`comp_lift` adds substitution-composition on top — likely needs both the
above and a renaming/substitution commutation lemma
(`lift.aux σ τ (⟦ ρ ⟧ʳ e) = ⟦ ρ' ⟧ʳ (lift.aux σ' τ' e)` style).

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
