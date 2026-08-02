# Plan: the theory of groups as a formalized example

Target: the rank-1 row of `Raw-plus-typing-redesign.md` §8.1 — the group
signature as an instance of the existing simply-typed framework, with
the adequacy theorem against classical first-order group terms.  This
realizes §2 of `Syntax-algebras-and-Lawvere.md` in Lean.  Everything
is layer 0: no decorations, no typing layer.

## 0. Design decisions (settled)

**(D1) General list carrier first.**  The carrier is the general one
of `examples/list-carrier.md` (`listCarrier Ty`); groups pick out the
three reachable entries.  (The earlier bespoke-light-carrier variant
survives only as a remark: the sub-carrier reachable from the group
signature is `List {nullary, unary, binary}`.)

**(D2) File layout.**

```
HigherRankSyntax/Examples/ListCarrier.lean       per examples/list-carrier.md
HigherRankSyntax/Examples/GroupSignature.lean    Phases 1–2
HigherRankSyntax/Examples/GroupTerm.lean         Phase 3
HigherRankSyntax/Examples/GroupAdequacy.lean     Phases 4–5
```

**(D3) Naming.**  Following the working rules: no abbreviations;
shape *variables* in upper-case Greek; named constants descriptive:
`groupCarrier`, `groupSignature`, `variableContext n`.

## 1. Instantiation (`GroupSignature.lean`)

One class: `Ty := Unit`, `groupCarrier := listCarrier Unit`.  The
three entries (declaration *shapes* — `binary` is not `m`; `m` is a
slot of the signature carrying the `binary` shape):

```
nullary := Entry.mk [] ()                    -- variables, and the shape of u
unary   := Entry.mk [nullary] ()             -- the shape of i
binary  := Entry.mk [nullary, nullary] ()    -- the shape of m
```

## 2. Signature and contexts

```
groupSignature    : Arity := ⟦[nullary, binary, unary]⟧      -- slots u, m, i
variableContext n : Arity := ⟦List.replicate n nullary⟧      -- v_n
```

Small lemmas, from the smoke tests of `list-carrier.md` §5 plus
`cover`/`copair`:

- arity-`1` slots of `groupSignature ⋈ variableContext n`
  ≅ `Unit ⊕ Fin n` (the `u`-slot and the variables);
- exactly one slot of arity `variableContext 2` (namely `m`), one of
  arity `variableContext 1` (namely `i`).

## 3. The classical side (`GroupTerm.lean`)

```
inductive GroupTerm (n : ℕ)
  | var : Fin n → GroupTerm n
  | unit | mul : GroupTerm n → GroupTerm n → GroupTerm n | inv : GroupTerm n → GroupTerm n

groupSubst : (Fin n → GroupTerm m) → GroupTerm n → GroupTerm m
```

Deliberately *no* standalone lemmas about `groupSubst` (associativity
etc.): these are to be obtained *through* the adequacy iso from
`act_comp`/`act_inst_id` — that transfer is part of the point.

## 4. Adequacy: the isomorphism (`GroupAdequacy.lean`)

```
toGroupTerm : Expr (groupSignature ⋈ variableContext n) () → GroupTerm n
ofGroupTerm : GroupTerm n → Expr (groupSignature ⋈ variableContext n) ()
```

- `toGroupTerm` by recursion on `Expr` (termination: `Subterm`, as in
  `Subst.act`).  Head dispatch: classify a head of
  `groupSignature ⋈ variableContext n` into `u / m / i / var j` —
  derive a four-way case principle from `cover` at this specific
  shape (do *not* transplant any dispatch type from the retired
  references; `Subst.threeway` is the pattern to imitate, at our own
  decomposition).  Note the rank-1 simplification: a child at a slot
  of arity `1` lives in `Γ ⋈ 1 = Γ` *definitionally* (Cayley), so no
  context bookkeeping enters the recursion.
- `ofGroupTerm` by structural recursion; variables go to `Expr.η`.
- Round-trips `to ∘ of = id` and `of ∘ to = id` by the same
  inductions (state both before proving either; the second needs the
  head-dispatch case principle again).

## 5. Compositionality

The substitution comparison, at prefix `groupSignature` and depth `1`
(the `T'_S` discipline: symbols are left-case heads, hence inert):

```
σ : Subst (variableContext n) (groupSignature ⋈ variableContext m)
─────────────────────────────────────────────────────────────────
toGroupTerm (σ.act 1 e)
  = groupSubst (fun j => toGroupTerm (σ (variableSlot j))) (toGroupTerm e)
```

plus the unit comparison `toGroupTerm (Expr.η (variableSlot j)) = var j`.

Expected ingredients: `act_left` / `act_middle` / `act_right`
(`Dispatch.lean`); for the variable (middle) case, the inner
substitution has domain of arity `1`, so it should collapse via
`act_idOfη` (`Instantiation.lean`) — vacuous agreement with `η` on an
empty slot set.  **Risk item**: if the middle case does not discharge
this way, the missing prefix-general `act_η` becomes a real
dependency; it is already the flagged next raw milestone, so hitting
it here would only confirm its priority, not change the plan.

## 6. Optional extension (separate milestone)

Package the iso as an isomorphism of `Jf`-relative monads,
`ev_{(1,())} ∘ T'_{groupSignature} ∘ i  ≅  R_Σ`, realizing
`Syntax-algebras-and-Lawvere.md` §2 end-to-end.  Blocked on the
prefix-general unit laws (`act_η` at `Γ := groupSignature`); defer
until Phase 5 has settled whether that lemma is forced anyway.

## Acceptance criteria

1. `lake build` of the files (never a Mathlib source compile);
2. the adequacy equivalence with both round-trips;
3. the compositionality theorem of Phase 5;
4. as a corollary demonstration: associativity of `groupSubst`
   derived from `act_comp` through the iso, with no direct induction
   on `GroupTerm`.

## Order of work

`ListCarrier.lean` per its own plan (with §3 there `sorry`-staged) →
1 → 2 → 3 → 4 (`to`, `of`, round-trips) → 5 → discharge the
list-carrier `sorry` → acceptance run → 6.
