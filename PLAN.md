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

`HigherRankSyntax/*.lean` builds.  `SyntaxMonad : RelativeMonad J` is fully populated
modulo the **one remaining `sorry`** — `lift_inst_commute` (= **L5**) in
`Equations.lean`.  The composition law `comp_lift` is proved modulo
that sorry.

The substitution layer is split across two files:

`Subst.lean` — **machinery**:

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

`Equations.lean` — **theorems** (imports `Subst`):

* `extendList_tauSlot` — naturality of `Renaming.extendList` against `tauSlot`.
* η-side lemmas (private): `inst_aux_η_tauSlot`, `inst_aux_η_inv_of`,
  `inst_aux_η_bundle`, `inst_aux_η`, `inst_aux_η_inv`, `lift_aux_η_tauSlot`.
* `unit_left.aux` (private) and public `unit_left`.
* `L3.aux` (private) and public `L3 : Subst.lift ρ.toSubst e = ⟦ ρ ⇑ʳ α ⟧ʳ e`
  — the categorical embedding lemma.
* Public **`unit_right`** as a one-line corollary of `L3` at `ρ := 𝟙ʳ`.
* **`lift_inst_commute`** (L5, still `sorry`'d).
* `comp_lift.aux` (private) and public `comp_lift` (proved modulo L5).

`Renaming.lean` adds `Renaming.extendList ρ τ : Γ ⋈* τ →ʳ Δ ⋈* τ` and
naturality `extendList_weakenList`, `extendList_id`.  Also @[simp]
slot-action lemmas `extend_here`, `extend_there`, `weaken_apply`, `id_apply`.

`Expr.lean` adds `Renaming.actExpr_apply'` as a @[simp] unfolder of
`⟦ ρ ⟧ʳ (apply' …)` — avoids motive-correctness issues when rewriting slots
through the dependent witness `hα`.

Termination: `lift.aux` uses `Expr.Subterm.wellFoundedRelation`; `inst.aux`
uses lex `PSigma` over `(C.Arity, Σ Γ, Expr Γ)`.

## Newly added infrastructure (work-in-progress on L5)

In `Subst.lean`:

* `Subst.under (σ : Subst Δ Ε) (α : C.Arity) : Subst (Δ ⋈ α) (Ε ⋈ α)` —
  `.here i ↦ Expr.η ⟨.here i, rfl⟩`; `.there p ↦ ⟦ Renaming.weaken Ε α ⇑ʳ
  p.arity ⟧ʳ (σ p)`.
* `Subst.extendList (σ : Subst Δ Ε) (τ) : Subst (Δ ⋈* τ) (Ε ⋈* τ)` —
  cons-recursion through `Subst.under`.
* `Inst.map (ι : Inst α Δ) (σ : Subst Δ Ε) : Inst α Ε := fun j => σ.lift (ι j)`.

In `Equations.lean`:

* `inst_aux_factor_ren` (a.k.a. **InstWeaken**, general τ): proved.
  ```
  inst.aux α ρ ι τ e = inst.aux α 𝟙ʳ ι τ (⟦ (ρ ⇑ʳ α).extendList τ ⟧ʳ e)
  ```
  The "renaming on the substrate" factor of `inst.aux`.  Provable by
  structural induction on `e` using `inst_aux_*_eq` + `extendList_tauSlot`
  + `extendList_weakenList`.

## Outstanding

Prove **L5** (`lift_inst_commute` in `Equations.lean`).  *Multiple
proof attempts today did not close.*  See "Lessons from today" below for
what was learned.

## Lessons from today (2026-05-20)

We attempted several formulations of L5 / a substitution–instantiation
commutation lemma and **all hit the same structural obstruction**.  Recording
the lessons so the next attempt does not re-tread them.

### Statements tried

1. **substitutionLemma at τ = 0**:
   `σ.act (ι.act e) = (ι.map σ).act (σ.lift e)` for σ : Subst Δ Ε,
   ι : Inst α Δ, e : Expr (Δ ⋈ α).

   At the `.here j` recursive case, args j : Expr ((Δ ⋈ α) ⋈ k.arity), so the
   IH lives at τ_inst = [k.arity], not 0.  Needs a τ-generalized aux.

2. **τ-generalized substitutionLemma_aux**:
   `(σ.extendList τ).act (inst.aux α 𝟙ʳ ι τ e) = inst.aux α 𝟙ʳ (ι.map σ) τ (lift.aux (σ.under α) τ e)`.

   At the `.there r` sub-case (r : Slot Δ):
   * LHS reduces (inst → lift) to `inst.aux r.arity (Ε ↪ʳ τ) Λ_L [] (σ r)`.
   * RHS reduces (lift first) to
     `inst.aux α 𝟙ʳ (ι.map σ) τ (inst.aux r.arity ((Ε ⋈ α) ↪ʳ τ) Λ_R [] (⟦weaken⟧ (σ r)))`.

   The outer `inst.aux α … τ` of RHS doesn't fire on an inner `inst.aux`-result
   (its pattern-match is on `apply'`).  After `inst_aux_factor_ren` flattens
   the inner to `Λ_R.act (⟦…⟧ʳ (σ r))`, the outer doesn't fire on a
   `Subst.act`-result either.

3. **Subst.act_comp** as a route to comp_lift:
   `(σ ˢ∘ˢ θ).act e = θ.act (σ.act e)`.  At base case the inner walker on
   `args k` lands at τ_inst = [k.arity] — same τ-generalization need.

### The structural obstruction

Every formulation reduces the `.there r` case to a **nested walker
composition** `outer_walker ∘ inner_walker e'` where `e'` is some renamed
form of `σ r` — handed to us by σ.  To close, we need to "push" the outer
walker through the inner walker's result.  No subterm of the original `e`
decreases at this step; the recursion would have to descend into `σ r`,
which has no termination measure relative to `e`.

This is a *real* obstruction, not a tactic glitch.

### Hypothesis for tomorrow

Recast `inst.aux α ρ ι []` as a `Subst.act` of a derived `Subst (Δ ⋈ α) Ξ`:

```
def Inst.bind {α Δ Ξ} (ρ : Δ →ʳ Ξ) (ι : Inst α Ξ) : Subst (Δ ⋈ α) Ξ
  | .here i  => ι i
  | .there p => ρ.toSubst p  -- i.e., Expr.η ⟨ρ p, ρ.arity p⟩
```
and prove `inst.aux α ρ ι [] e = (Inst.bind ρ ι).act e`.  Then both
`inst.aux` and `lift.aux` are *the same* `Subst.act` machinery at the same
shape, just with different substitutions.  The commutation
becomes the Kleisli associativity `Subst.act_comp`, which still requires a
τ-generalized aux (comp_lift.aux at τ-generalized form, which we already
have)— **but** now the `.there r` case may close because both walkers are
the same operation, and we can compose at the substitution level
(`σ ˢ∘ˢ θ`) before walking, avoiding nested walkers entirely.

This is a structural reformulation, not a small tactic.  Confirm with
Andrej before executing.

## Warmup lemmas (done, reference)

* `@[simp]` per-case unfolders for `inst.aux` / `lift.aux`:
  `inst_aux_ext_eq`, `inst_aux_base_there_eq`, `inst_aux_base_here_eq`,
  `lift_aux_ext_eq`, `lift_aux_base_eq` (Subst.lean).
* `classify_weakenList`, `classify_tauSlot` (Subst.lean).
* `Renaming.actExpr_apply'`, `Expr.T.map_η` (Expr.lean).
* `Renaming.extendList`, `extendList_id`, `extendList_weakenList`,
  slot-action @[simp] lemmas (Renaming.lean).
* `extendList_tauSlot`, `inst_aux_η`, `inst_aux_η_inv`, `lift_toSubst`
  (Equations.lean).
* `inst_aux_factor_ren` (InstWeaken general, Equations.lean) — proven today.

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

## HigherRankSyntaxSig — alternate library (hand-off)

`HigherRankSyntaxSig/` is a parallel rebuild on a List-Arity `Shape`,
with `Subst.dom : List C.Arity` (replacing the original single-arity
dom) so every Kleisli map of the relative monad corresponds directly
to a `Subst` record — sidestepping the OCaml-style "two flavours of
walker" obstruction (`lift`/`inst` split, `comp_lift` quagmire) that
the original library hit.

### What's built

- **`Shape.lean`**: `abbrev Shape (C : Carrier) := List C.Arity`;
  `.nil` / `.ext Γ α` as `@[match_pattern] abbrev`s for `[]` / `α ::
  Γ`.  `extList Γ τ := τ ++ Γ` as `abbrev`, notation `⋈*`.  `SlotAt`
  inductive on `Shape`.
- **`Carrier.lean`**, **`Renaming.lean`**, **`Expr.lean`**: ported
  from the original library; identical structure (`actExpr`'s
  `map_id`/`map_comp` already proved).
- **`Subst.lean`**:
  - `Subst { pre : Shape C, dom : List C.Arity, cod : List C.Arity,
    sub : ∀ {α}, (dom ∋ α) → Expr ((pre ⋈* cod) ⋈ α) }`.  Source =
    `pre ⋈* dom`, target = `pre ⋈* cod`.
  - `XPos pre dom : (τ : List Arity) → {α} → SlotAt … → Type` with
    three constructors `.pre`, `.dom`, `.ext` (pre, dom as
    parameters; τ as index varying via `.ext`).
  - `PreOrDom pre dom : {α} → SlotAt → Type` (two constructors) —
    return type of `classifyDom`, dodges the impossible-but-not-
    eliminable `.ext` case at τ=[].
  - `classify`/`classifyDom`: two-phase walk (τ then dom).
  - `Subst.act`: walker, terminates by lex `(DomLt, Expr.Subterm)`.
  - `DomLt`: WF relation on `List C.Arity` ([β] ≺ dom iff β is a
    sub-arity of some αⱼ ∈ dom); WF via `Carrier.Sub`-induction.
- **`SyntaxMonad.lean`** (stub):
  - `ShapeCat`, `ArityFunc`: categories on `Shape C` (with Renamings)
    and on `C.Arity → Type` (wrapped to dodge instance ambiguity if
    two carriers share `Arity`).
  - `J : Shape ⥤ ArityFunc` (`Γ ↦ α ↦ Γ ∋ α`).
  - `T : Shape ⥤ ArityFunc` (`Γ ↦ α ↦ Expr (Γ ⋈ α)`), `map_id`/
    `map_comp` proved from `Renaming.actExpr.map_id`/`map_comp`.
  - `toSubst {Γ Δ} (f : J Γ ⟶ T Δ) : Subst C` — wraps `f` as a
    pre=[] Subst, with `sub := cast … ∘ f` along
    `(List.append_nil Δ).symm`.
  - `fromSubst (σ : Subst C) : J (σ.pre ⋈* σ.dom) ⟶ T (σ.pre ⋈*
    σ.cod)` — dispatches via `classifyDom`: pre-slot → `Expr.η`
    at the weakened target position, dom-slot → `σ.sub`.
  - `SyntaxMonad : RelativeMonad J` with `η = Expr.η`, `lift`
    defined via `toSubst` + `Subst.act` + two casts.

### Open (`sorry`)

- `unit_right`, `unit_left`, `comp_lift` — relative-monad laws.
- `fromSubst_toSubst` (was sketched, then removed) — `fromSubst
  (toSubst f) = f` modulo casts.  Deferred until we know what
  consumer needs it; might fall out of a unit-law proof.

### Key design decisions

- **Transports at the Kleisli boundary are allowed.**  The "no `▸`"
  rule applies inside `Subst.act`'s recursion (transports there
  block computation and break inductive hypotheses); at `lift`'s
  outer wrap/unwrap they're the right tool — O(1) cast vs O(|Expr|)
  for the structural-renaming alternative.  Previously had
  `toAppendNil`/`fromAppendNil` renamings; replaced with `cast
  (congrArg (Expr ∘ (· ⋈ α)) (List.append_nil _))`.
- **List-`dom` Subst captures all Kleisli maps.**  A Kleisli `f : Γ
  →ˢ Δ` is exactly `toSubst f : Subst C` with `pre = []`.  The
  residual friction is `[] ⋈* X = X ++ [] ≠ X` propositionally for
  abstract `X` — absorbed by the two boundary casts in `lift`.
- **`Shape = List C.Arity` as `abbrev`** with `.nil`/`.ext` as
  `@[match_pattern] abbrev`s.  Beware: `Γ ⋈* []` reduces to `Γ`
  definitionally (τ-recursion of `extList`), but `[] ⋈* Γ` does
  **not** reduce to `Γ` for abstract `Γ` (it unfolds to `Γ ++ []`,
  which `List.append` doesn't simplify on the second arg).
- **Why `XPos` has `pre`/`dom` as parameters and `τ` as index**: pre
  and dom are known at all `classify` call sites, so making them
  parameters keeps Lean's pattern matcher happy.  `τ` varies via
  `.ext`'s implicit `(τ_above ++ β :: τ_below)` decomposition.
- **`PreOrDom`**: a two-constructor companion to `XPos` whose return
  type at τ=[] hides the impossible `.ext` case.  Lean's matcher
  can't eliminate `[] = τ_above ++ β :: τ_below` automatically;
  using `PreOrDom` avoids `nomatch` gymnastics.

### What to do next

Pick `unit_right` or `unit_left` and try directly via induction.
`fromSubst_toSubst` is probably a stepping-stone, but state and
prove the *consumer* (unit law) first — only extract a lemma when
the proof gets stuck on a recognizable shape.

`comp_lift` is the historically hard law.  The hope of the list-dom
design: lift-after-lift composes at the `Subst`-record level, and
`Subst.act`'s self-similar recursion handles the composition
without the OCaml-flavoured nested walker.  Untested.

## `endomaps` branch — Tele experiment, conclusion

A branch `endomaps` off `with-signature` (head `9bbb9e5`) explored
replacing `Shape := List C.Arity` with a *telescope* representation
`Shape := Tele C.Arity := { val : List α → List α // ∀ x xs, val (x ::
xs) = x :: val xs }`, with the goal of getting *strict* monoid laws
(`Γ ⋈* nil ≡ Γ`, `nil ⋈* Γ ≡ Γ`, `Γ ⋈* (Δ ⋈* Ε) ≡ (Γ ⋈* Δ) ⋈* Ε`)
definitionally, eliminating the `List.append_nil` cast in `lift`.

### What worked

- **`Tele.lean`** builds clean.  Strict monoid laws via function
  composition + Lean η-equivalence + Prop irrelevance for the
  subtype — all `rfl`.
- **`Shape.lean`** builds clean with `abbrev Shape := Tele C.Arity`,
  `⋈ := ∘ᵗ Tele.snoc`, `⋈* := ∘ᵗ`.  All three monoid `simp` lemmas
  are `rfl`.
- **Recursive `ofList`** (`ofList (β :: rest) = ofList rest ∘ᵗ snoc β`
  by `rfl`) makes `Γ ⋈* (ofList (β :: rest)) ≡ (Γ ⋈* ofList rest) ⋈
  β` definitional — the key reduction needed for List-recursive
  classify to interact with Tele-based shapes.
- **Church-encoded lists** (alternative formulation) verified to
  give the same strict-monoid laws as `rfl` in a tiny test.

### What broke (the fundamental obstacle)

**Lean 4's pattern-matching unifier cannot invert `SlotAt (Γ ⋈ α)`
when `⋈` is defined via function composition (Tele).**

Concretely, `cases p` on `p : SlotAt (Γ ⋈ β) α` fails:

```
Dependent elimination failed: Failed to solve equation
  (fun x ↦ Γ.val ((Tele.snoc β).val x))
  = fun x ↦ Γ✝.val ((Tele.snoc α✝).val x)
```

The two sides are α-equivalent (Γ ≔ Γ✝, β ≔ α✝), but Lean's matcher
doesn't go "inside" the `Tele` struct's `.val` lambda to unify.  This
breaks every `cases p` in `Renaming.lean` (`extend_id`,
`extend_comp`), and would equally break classify, classifyDom,
Subst.act's per-case dispatch, and Expr.actExpr.

### What this means

The whole architecture relies on inverting slot constructors —
SlotAt is *inherently* inductive and we pattern-match on it
constantly.  Without inversion, the entire `HigherRankSyntaxSig`
machinery cannot be ported to Tele as-is.  Workarounds (non-
inductive SlotAt via Fin/Sigma, custom recursors, etc.) require
deep rewrites that propagate everywhere SlotAt is consumed.

### Breakthrough — cons-style Tele + SlotAt-via-list

The original obstacle came from using **snoc-style** telescopes
(`Tele.snoc α := λxs. xs ++ [α]`).  Switching to **cons-style**
(`Tele.cons α := λxs. α :: xs`) with `Γ ⋈ α := Tele.cons α ∘ᵗ Γ`
gives `(Γ ⋈ α).toList = α :: Γ.toList` *definitionally* — because
`Tele.cons α (Γ [])` is just β-reduction.

Combined with `SlotAt Γ α := ListSlotAt Γ.toList α` (inductive on
`List`, abbrev'd for `Tele`), pattern matching on slots at
`Γ ⋈ α`-shaped Tele's goes through cleanly — Lean matches on the
underlying list, which reduces.

**Tele.lean, Shape.lean, Renaming.lean all build clean** with this
design.  The strict monoid laws are still all `rfl`.

### Remaining obstacle: Subst.dom

`Subst.dom`, `Subst.cod` need to be either:

- **`List C.Arity`** — `classifyDom` walks inductively, but the
  `lift` bridge sets `σ.dom := Γ.toList` and the source shape
  becomes `ofList Γ.toList ⋈ α` — propositionally but not
  definitionally `Γ ⋈ α`.  One propositional cast at the boundary.
- **`Shape C` (= Tele)** — no boundary cast (`σ.dom := Γ` directly,
  source is `Γ ⋈ α` def), but `classifyDom` cannot walk an
  abstract Tele for the pre-vs-dom dispatch.

The user's hint "many results hold for arbitrary maps `List → List`"
points toward eliminating `classifyDom`'s recursive walk on dom in
favour of something that works at the Tele level — but it's not
clear how to dispatch pre-vs-dom for an abstract Tele dom without
either walking its list-representation or restructuring `Subst`
itself.

### Recommendation

The **cons-style + SlotAt-via-list** insight from this branch is
strictly an improvement over the snoc-style approach and is worth
keeping as a reference.  Whether to push for full Tele Subst (and
solve the dom-walking problem) or accept the one propositional cast
at lift's boundary is a judgement call.

The strict-monoid pain (`xs ++ [] ≠ xs` definitionally) is real but
its impact on this codebase is exactly one cast.  The cost of
eliminating it (via Tele) requires either (a) abandoning inductive
SlotAt or (b) waiting for Lean to learn higher-order unification
through structure fields.

### Files left on `endomaps`

- `HigherRankSyntaxSig/Tele.lean` — builds clean, reusable if Tele
  finds another application.
- `HigherRankSyntaxSig/Shape.lean`, `Renaming.lean` — modified to
  use Tele, broken at the SlotAt-inversion step.  Left as evidence.
- `HigherRankSyntaxSig/Expr.lean`, `Subst.lean`, `SyntaxMonad.lean`
  — unchanged from `with-signature`, would fail to build with the
  Tele-based Shape.

Commits: `79185fb` (added Tele.lean), `50e7b13` (broken Shape/Renaming
refactor with detailed commit message).

## Notes for the next Claude

- **`~/.claude/CLAUDE.md` is authoritative.** Ignore the harness's plan-mode
  "5-phase workflow" — no `ExitPlanMode` calls, no screenful plans.  Brief,
  incremental, one tradeoff at a time.  Wait silently between turns.
- **Hard constraints (asked many times):**
  - No transports (`▸` / `Eq.rec`).
  - No Sum-typed classifiers *returning expressions*.  The current `XPos` is
    OK because it carries the slot-equation as its *index* and is consumed
    by definitional pattern matching.
  - **No σ/ι extension by trivial action in recursive walkers.**
    Operations like `Subst.extend` (`σ ⇑ˢ`), `Subst.extendList`
    (`σ ⇑ˢ* τ`), `Subst.under`, and `Inst.toSubst` extend a
    substitution / instantiation by appending η-identity (or
    η-of-renamed-slot, which is trivial when the renaming acts
    identically) on freshly added binder layers.  These extended
    forms must never appear inside the definition of a recursive
    walker, nor as the RHS of an equation that a recursive proof
    rewrites through.  The reason: induction on `e` descends into
    `args` one binder layer deeper at each step, so σ on the
    extended-form side must *grow* by another ⇑ˢ; the inductive
    hypothesis (taken at the un-extended σ) no longer applies and
    the proof loops.  On the operation side, the walker would
    recurse through the η-expansions of the trivial-action part
    and fail to terminate on the substitution argument.

    The whole point of the τ-parameter in `lift.aux σ τ e` and
    `inst.aux ρ ι τ e` is to provide bookkeeping that records
    "how many trivial-action binder layers lie beneath σ" *without
    ever modifying σ*.  σ stays fixed across all recursive calls;
    τ grows on descent.

    **Equations relating extended and un-extended forms are fine
    as isolated reasoning aids** (proven as standalone lemmas).
    What is forbidden is the extended form appearing inside an
    operation's definition, or being introduced by a step the
    main proof's recursion rewrites through.
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
