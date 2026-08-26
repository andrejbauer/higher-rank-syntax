# Formalization plan

Tracks the state of formalizing `equational-telescopes-core.md`. Section numbers
below refer to that note. The note states the mathematics; this file states what is
done, what is decided, and what was measured.

## Decisions

| # | question | status |
|---|---|---|
| 1 | Lean name for the equality judgement — `Eq` is taken by core | **settled**: `Eq_e`, beside `Wf_e`, `Wf_s`, `Wf_t` |
| 2 | rename `Boundary → Bd`, `DecoratedTelescope → dTel` | **settled**: yes, step 1, one mechanical commit |
| 3 | `DTel` (module, `DecorationModule.lean`) vs `dTel` (type) differ only in case | **settled**: rename the module |
| 4 | `⊢` notation: four judgements, one turnstile | **settled**: declare all four in step 5, tested on dummy types first; see *Measured* |

## Steps

One step per commit; green before the next under **all three targets** —
`lake build`, `lake build ListCarrier`, `lake build "ML-Sigma"` — since
`defaultTargets` names only the first and the examples break silently otherwise. Statements first with
`sorry`, then proofs, `sorry`s left visible. At the first mismatch between a
statement and its use site: stop, show the goal, do not adjust the statement to fit.
Each pass ends with a report — the symptom, or every name added — per CLAUDE.md's
*Reporting each pass*.

| # | content | file | status |
|---|---|---|---|
| 0 | the two raw lemmas of 8.2 | `MonadLaws.lean` | **done** — `ap_eq_act_η`, `act_copair_id`, plus `Subst.copair`, `Renaming.extend_unit` |
| 1 | renames (decisions 2, 3) | all | **done** — `Bd`, `dTel`, `dTelModule`; file names unchanged |
| 2 | `Bd.eq`, `Bd.isEq`, actions (2.1–2.3) | `Typing/Boundary.lean` | **done** |
| 3 | `SlotPath.inl`, `Decoration.restrict`, projections (3.4) | `SlotPath.lean`, `Typing/Decoration.lean` | **done** |
| 4 | `boundaryOf` (§4) | `Typing/ExprBoundary.lean` | **done** |
| 5 | notation, `Wf_e`, `Eq_e`, `Eq_bd`, `Wf_s` (§5, §6) | `Typing/Judgement.lean` | **done** — gate 1 passed |
| 6 | `Wf_t`, `≈` on telescopes (§7) | `Typing/TelescopeWf.lean` | **definitions done**; 7.2 and its three restriction lemmas stand as `sorry` |
| 7 | §8's eleven items, in 8.1's order | `Typing/Substitution.lean` | todo — **gate 2** |
| 8 | `Ctx`, `𝒯₀`, extension (§9, §10) | `Typing/Context.lean` | todo |
| 9 | `TelFam`, tensor, monoid (§11) | `Typing/TelescopeMonoid.lean` | todo |
| 10 | `ℰ₀`, `ℬ₀`, `q`, representability (§12, §13) | `Typing/Expressions.lean`, `Typing/NaturalModel.lean` | todo |

**Gate 1 — passed.** `(σ ↾ z) ⋆ Θ.binding z` and `(σ ↾ z) ⋆ Θ.boundary z` assemble
from `⇑` and `⋆` with no transport, as `dTel.bindingAt` and `dTel.boundaryAt`, and
`(Ξ.extend (Θ.bindingAt σ z)).arity` reduces to `Ξ.arity ⋈ Λ` by `rfl`, which is
what lets `σ z` be a premise of a judgement over the extended ambient.

**Gate 2.** The substitution lemma. (3) and (4) are mutually inductive; (7) comes
after them, its clause-3 case applying (3) to a derivation the induction hypothesis
produced rather than to a subderivation.

## Measured

Facts checked against the current library, not assumed.

**The monoid laws on `⋈` are definitional.** `Ω ⋈ 1 = Ω`, `1 ⋈ Ω = Ω`,
`Γ ⋈ Δ ⋈ Φ = Γ ⋈ (Δ ⋈ Φ)` all by `rfl`, for an arbitrary carrier, and they
transport `∋`, `Bd` and `dTel` with no cast. The
`castBase (mul_one …)` at `DecoratedTelescopeMonoid.lean:275`, `castBase (mul_assoc …)`
at `:348` and `Bd.cast_injective (mul_assoc …)` at `DecorationModule.lean:91`
are therefore not needed for types to agree; removing them is optional cleanup.

**Arity invariance is definitional.** `Decoration.rename`, `.act` and `.substitute`
each set `arity := Θ.arity`.

**`Eq` collides with core.** `inductive Eq` at root: "already declared". Inside a
namespace it declares, and `=` keeps working, but `open` makes a bare `Eq`
ambiguous — and §§7–13 use the name constantly.

**`⊢` notation needs precedence work.** With `notation:50 Ξ " ⊢ " e => Wf_e Ξ e`
declared, `Ξ ⊢ e ≈ e'` parses as `Ξ ⊢ (e ≈ e')` via core `HasEquiv`. The argument
must be parsed at a precedence above `≈`. Two of the four judgements share the
shape `⊢ _ : _` (expression:boundary, substitution:telescope), so that one is
overloaded and resolved by elaboration.

**4.2 assembles with no transport** — the gate-1 question, answered in advance for
`boundaryOf`. This compiles against the current library:

```lean
def boundaryOf (Ξ : dTel (C := C) 1) : Expr Ξ.arity → Bd Ξ.arity
  | .ap (α := α) x args =>
      Bd.instantiate args
        (Bd.rename (Renaming.prefixed 1 (C.inclusion x) ⇑ʳ α)
          (Ξ.decoration.boundary x))
```

`Bd.instantiate` is 3.6's plain `Bd` line, already in the library. Only
`Ξ.before x` needs `Decoration.restrict`; `boundaryOf` itself needs only
`C.before x`.

**Why the base must be the unit.** The same definition over an arbitrary base `Ω`
with `Θ : dTel Ω` compiles for heads in `|Θ|` and has no data for heads in `Ω`;
at `Ω = 1` that branch is killed by `C.unit_is_empty`. Totality is what forces the
ambient.

**`Carrier.inl`/`inr` are not renamings as written.** They bind their arity `{α}`
where `Renaming` wants `⦃α⦄`, so bare `C.inr` is rejected at `Δ →ʳ Γ ⋈ Δ` and
`Subst.ofRenaming C.inl` needs `fun ⦃_⦄ x => C.inl x`. Changing those two binders
should be invisible at existing call sites, an explicit argument following.

## Open questions

None blocking.

## Notes from the passes

**Step 6.** `Wf_t` and `Eq_d` are **well-founded recursions on `Θ.arity`**, not
inductives, decreasing by `⟨z⟩` against `C.subWf`; being plain `def`s they may use
`match` and `∧` freely, which the mutual block of step 5 may not.

`Eq_d` compares two decorations of a **common arity**, and `Eq_t` is the
`∃ h : Θ.arity = Θ'.arity` wrapper around it. Stating 7.4 directly on two
telescopes would need a transport at every recursive step — `Θ'.binding (h ▸ z)`
lives over `Θ'.before (h ▸ z)`, not over `Θ.before z`. At a common arity the two
`nested` decorations have literally the same type and no transport arises; the one
transport left is `Decoration.castArity h.symm` at the top.

**7.2 is blocked on the carrier, not on bookkeeping.** All four `sorry`s reduce to
`Carrier.inclusion_inclusion` — that including from `before w` into `before z` and
then into the whole is including directly. After `unfold Carrier.inclusion` the
goal is

```
⋯ ▸ C.inl (⋯ ▸ C.inl x) = ⋯ ▸ C.inl (⋯ ▸ x)
```

four transports along `factor z`, `factor w`, `factor (C.inclusion z w)` and
`before_inclusion z w`. `C.inl_inl` is the associativity coherence that should
close it, but the transports cannot be discharged by `subst`: `factor z` reads
`C.before z * C.after z = Δ`, and substituting `Δ` makes `z : Δ ∋ α`
self-referential, so the motive is not type correct. Three ways forward, for the
user to choose:

1. add `inclusion_inclusion` as a **carrier axiom** — every intended carrier
   satisfies it, and `before`/`after`/`factor`/`before_inl` are already axioms of
   the same kind;
2. derive it, which means transport surgery around `slotAt_mul` and probably more
   coherence lemmas of the `inl_inl` family;
3. reformulate `dTel.before` so that restriction is definitional — the routes tried
   (recursion through `SlotPath.inclusion` instead of `restrict` + `factor`; making
   `Wf_t` assert its own restriction) either hit the same law or fail
   `C.subWf` termination, `C.before z` not being a binding arity of `Θ.arity`.

Left standing, five `sorry`s, all one obstruction: 7.2 (`Wf_t.before`) factors
through three restriction-compatibility facts — `before_before`, `binding_before`,
`boundary_before` in `Decoration.lean` — saying that `Θ.before z` at `w` decorates
as `Θ` does at `C.inclusion z w`. The note gives these one sentence; in Lean the
last two are `HEq`, since their types differ by `before_before`. The arity
ingredient is `Carrier.before_inclusion` (with `Carrier.before_cast`), both proved;
the composition law above is what remains. The judgements are **four** mutual inductives, not three: §5's
boundary equality is `Eq_bd`, a member of the block. Lifting a relation through a
`def`, as 5.1 states it, would put `Eq_e` under an opaque application inside a
constructor type; as a fourth inductive with three constructors it is positive by
construction.

Two encoding facts, both forced by the kernel rather than chosen:

- **`∧` cannot appear in the block.** 6.2's `Ξ ⊢ e : β` is a conjunction, and using
  it inside `Wf_s`'s constructor gives *invalid nested inductive datatype 'And',
  nested inductive datatypes parameters cannot contain local variables*. `Wf_s.mk`
  therefore carries `filler` and `declared` as two separate `∀` premises. The
  notation `Ξ ⊢ e : β` still abbreviates the conjunction — outside the block.
- **The ambient is an index, not a parameter.** 6.3's premises and 6.5(3) both
  speak of ambients other than the one in the conclusion, so `Wf_e`, `Eq_e`,
  `Eq_bd` and `Wf_s` are indexed by `Ξ : Ambient C`, with `Expr Ξ.arity` a
  dependent index.

The §3.6-at-a-slot wrappers live with their ingredients, not with the judgements:
`Subst.restrict` in `Subst.lean`, `dTel.instantiate`, `Ambient.weaken` in
`DecorationModule.lean`, `Ambient.extend` in `DecoratedTelescopeMonoid.lean`.
`Θ.binding z` and `Θ.boundary z` under `σ ↾ z` are written out at each use site
rather than abbreviated. Note `Ambient` is an `abbrev` for `dTel 1`, so an
`Ambient.foo` must be declared outside `namespace dTel` or dot-notation looks for
`dTel.foo`.

`Wf_s`'s two branches are guarded implications — `Θ.boundaryAt σ z = .eq l r → …`
and `¬ (Θ.boundaryAt σ z).isEq → …` — rather than a `match`, so 6.9's warning about
a `Prop`-valued match in a constructor type never arises. Lemma 2.3 is what makes
exactly one guard fire.

Notation: all five declared, with arguments parsing at 51 so `Ξ ⊢ e ≈ e'` is not
read as `Ξ ⊢ (e ≈ e')` by core `HasEquiv`. Both overloads of `⊢ _ : _`
(substitution against telescope, expression against boundary) and both of `⊢ _ ≈ _`
(expressions, boundaries) resolve by elaboration; five smoke tests in the file
exercise them.

**Step 4.** `boundaryOf` is `Typing/ExprBoundary.lean`, defined on `Ambient C`
(the old `Theory`, renamed to the note's word) by one non-recursive match. 4.1 is
recorded as a smoke test: `args : Subst α Ξ.arity` is accepted where
`Subst ((Ξ.binding x).rename (Ξ.inclusion x)).arity Ξ.arity` is expected, which is
the whole content of "the arguments of an application are a substitution filling
the telescope its head binds". `dTel.inclusion` names the renaming of 3.5 once,
since 6.4's premise needs the same one for the telescope.

Pass 1's rename had silently broken `examples/dependent/ML-Sigma.lean`: it uses
`Boundary`, `DecoratedTelescope` and `Theory`, and `lake build` does not reach it.
Repaired here by the same rename, `Theory → Ambient` included.

**Step 3.** `SlotPath.inl` compiles exactly as 3.4 writes it, both transports
along `C.before_inl`. `Decoration.castArity` is one definition the note does not
name: `dTel.before` restricts `Θ.decoration` along `(C.factor z).symm` first, and
the transport is forced — `castArity`'s direction is the only one that typechecks,
so a silent mis-transport is not possible here. The erasures of 3.4 hold by `rfl`
(`arity_before`, `arity_binding`), which is what lets `dTel.binding` and
`dTel.boundary` state their own types in terms of the previous projections.

Gate 1 answered for 4.2: `boundaryOf` reassembles from `Ξ.boundary x` — the
projection, not `Ξ.decoration.boundary x` — with `Bd.rename` and `Bd.instantiate`
and no transport.

**Step 2.** `Bd.isEq` is `Prop`-valued by pattern match, with `isEq_rename` and
`isEq_act` as Lemma 2.3 — both `cases β <;> rfl`. No `Decidable` instance yet:
nothing needs one, 6.3's branch being a premise rather than a test. `Bd.instantiate`
inherits 2.3 only through `isEq_act (Ξ := 1) σ 1`, which is enough for 6.3, whose
boundary carries the suffix `|Θ.binding z|` and so is an `act`, not an
`instantiate`. Adding the constructor broke exactly one proof outside the file,
`Bd.act_ofRenaming` in `DecorationModule.lean`.

**Step 1.** Renamed by word-boundary regex, `import` lines protected: `Boundary →
Bd` (69), `DecoratedTelescope → dTel` (54), and the module family `DTel →
dTelModule`, `DTelArityMod → dTelArityMod`, `DTelOne/Mul/Mon` and the private
`dtel*` lemmas to `dTel…`. **File names were not changed**, so
`Typing/Boundary.lean` now declares `Bd` and `Typing/DecoratedTelescopeMonoid.lean`
declares the `dTel` monoid; the one surviving `Boundary` in the source is that
file's module path.

**Step 0.** `ap_eq_act_η` is `act_inst_η` at replacement `1` plus `C.unit_right`;
it was not new work. `act_copair_id` needed a general suffix `Φ` for its induction,
hence `Renaming.extend_unit` (`f ⇑ʳ 1 = f`) to read it back at `Φ = 1`.
`Subst.copair` is stated in general — `σ` on `Γ`-slots, `θ` on `Δ`-slots — because
step 10's splitting and pairing want the same combinator.

Two traps met, both worth remembering. Writing `Expr.η x` where the expected type
is `Expr (Γ ⋈ α ⋈ 1)` makes the elaborator split at the *last* `⋈`, inferring
`Expr.η : (Γ ⋈ α) ∋ 1 → …`; ascribe the term, as `act_inst_η` does. And `rw` needs
a syntactic match, so a lemma stated at prefix `Γ` will not rewrite a goal whose
prefix is the defeq `Γ ⋈ 1` — the file's `trans` / `apply` idiom is what gets
through.
