## The OCAML spec as suggested byt the user (do not touch, but you may copy it and make your own)

```ocaml
module type CARRIER = sig
  type shape
  type arity
  type slot  

  val (**) : shape -> arity -> shape (* extension operation *)

  type 'a slot_map = (slot * 'a) list
  (* we require that a slot map always has all slots different, so it represents a map, we speak of them as if they were maps *)
  (* the support of a slot map is the set of slots appearing in it as keys *)

  val shape_entries : shape -> arity slot_map
  val arity_entries : arity -> arity slot_map

  val shape_lookup : shape -> slot -> arity (* shape_lookup γ x = α iff (x,α) ∈ shape_entries γ *)
  val arity_lookup : arity -> slot -> arity (* arity_lookup β x = α iff (x,α) ∈ arity_entries β *)

  (* We require shape_entries (γ ** α) to be isomorphic to the join of shape_entries γ and arity_entries α.
     The following values witness the isomorphism.
  *)

  val shape_shift : shape -> arity -> slot -> slot
  (* shape_lookup γ x = shape_lookup (γ ** α) (shape_shift γ α x) *)

  val arity_shift : shape -> arity -> slot -> slot
  (* arity_lookup α x = shape_lookup (γ ** α) (arity_shift γ α x) *)

  type slot_sort = Left of slot | Right of slot

  val slot_sort : shape -> arity -> slot -> slot_sort
  (* slot_sort γ α x is defined for every x in the support of shape_entries (γ ** α).
     For every such x:
     * if  slot_sort γ α x = Left y then y is in the support of γ and shape_shift γ α y = x 
     * if  slot_sort γ α x = Right z then z is in the support of α and arity_shift γ α z = x 
  *)

  val empty_arity : arity (* an arity with no slots *)
end

module type Make(C : CARRIER) = sig
  type expr = Apply of C.slot * expr C.slot_map

  (* an expression Apply(x, args) is valid in shape γ when:
     - (x, α) ∈ shape_entries γ for a unique α
     - for each entry (y, β) ∈ arity_entries α, there is a unique expression
       e valid in shape γ ** β such that (y, e) ∈ args
  *)
  exception Invalid of string
  val validate : C.shape -> expr -> unit (* throw Invalid if the given expression is invalid *)

  (* I know we cannot define values in signatures, this is just a convenience. *)
  val (***) : C.shape -> C.arity list -> C.shape
  let rec (***) γ = function [] -> γ | (α :: lst) -> (γ ** α) *** lst

  type substitution = { 
    pre : C.shape ;
    dom : C.arity list ;
    cod : C.arity list ;
    sub : expr C.slot_map (* a slot map whose support is dom *)
    (* for each entry (x, α) ∈ pre ** dom that "comes from the dom part" (figure it out)  
     there is a unique expression e valid in (pre *** cod) ** α such that (x,e) ∈ sub. *)
  }
  val subst : substitution -> C.arity list -> expr -> expr
  (* in an application subst σ τ e we require that e is valid in (σ.pre *** σ.dom) *** τ and
     the returned expression is valid in (σ.pre *** σ.cod) *** τ. *)
end
```

# Plan: `ocaml/syntaxAction2.ml`

## Context

`ocaml/syntaxAction.ml` is the working reference; `ocaml/syntaxAction2.ml` is a refinement that simplifies the substitution record. The driving observation is that in the current OCaml's `subst`, the auxiliary call always has `dom = [head_arity]` and `sub = [new_args]` — singleton lists wrapping single-arity data. That's a hint that the *underlying primitive* substitutes a single binder-block, and the list shape was an artifact.

The interface (`CARRIER`) is unchanged. The substitution record is simplified:

```
σ = { pre : shape ; dom : arity ; cod : arity list ; sub : expr slot_map }
```

- `dom : arity` (single, not a list) — the binder-block being substituted.
- `sub : expr slot_map` (single, not a list of slot_maps) — the substitution data for `dom`'s slots, with support equal to `arity_entries σ.dom`.
- `cod : arity list` — the replacement, possibly multi-arity, possibly empty. The empty list `[]` is a *definitional* strict unit by the cons-as-snoc definition of `***`: `γ *** [] = γ` by `rfl`. So no carrier obligation about `γ ** empty_arity = γ` arises.

(We considered `cod : arity option` per your suggestion; it works for the outer call but the aux's output shape includes `τ` — which an `option` can't carry without forcing expression-level weakening or a different aux structure. `arity list` with `[]` as the strict unit accommodates `τ` directly.)

`ocaml/syntaxAction2.ml` is new. `ocaml/syntaxAction.ml` is left untouched as the previous reference.

## Clean signature

This is the user's spec, with the typos corrected, the no-op invariants discharged, and `sub` retyped to a *list of slot maps mirroring `dom`*.

```ocaml
module type CARRIER = sig
  type shape
  type arity
  type slot

  val ( ** ) : shape -> arity -> shape

  type 'a slot_map = (slot * 'a) list
  (* Invariant: every slot_map has pairwise distinct keys (we treat them as finite maps). *)

  val shape_entries : shape -> arity slot_map
  val arity_entries : arity -> arity slot_map

  val shape_lookup : shape -> slot -> arity
  val arity_lookup : arity -> slot -> arity

  val shape_shift : shape -> arity -> slot -> slot
  val arity_shift : shape -> arity -> slot -> slot

  type slot_sort = Left of slot | Right of slot
  val slot_sort : shape -> arity -> slot -> slot_sort

  val empty_arity : arity
end

module Make (C : CARRIER) : sig
  type expr = Apply of C.slot * expr C.slot_map

  exception Invalid of string
  val validate : C.shape -> expr -> unit

  val ( *** ) : C.shape -> C.arity list -> C.shape

  type substitution = {
    pre : C.shape ;
    dom : C.arity ;
    cod : C.arity list ;
    sub : expr C.slot_map ;
  }
  (* Invariants on a substitution σ:
     - the support of σ.sub equals the support of arity_entries σ.dom;
     - for each (x, e) ∈ σ.sub, with β = arity_lookup σ.dom x,
       e is valid in (σ.pre *** σ.cod) ** β. *)

  val subst : substitution -> C.arity list -> expr -> expr
  (* subst σ τ e:
     - assumes e valid in (σ.pre ** σ.dom) *** τ
     - returns an expression valid in (σ.pre *** σ.cod) *** τ. *)
end
```

## Algorithm sketch

The call `subst σ τ e` takes a substitution `σ`, an extension `τ : C.arity list`, and an expression `e` valid in `(σ.pre ** σ.dom) *** τ`. The list `τ` is cons-as-snoc: the head is the outermost extension, so `γ *** (α :: rest) = (γ *** rest) ** α`. Consing a new arity onto `τ` adds a new outermost extension, and the equation `γ ** β = (γ_base *** τ) ** β = γ_base *** (β :: τ)` holds definitionally.

Destructure `e = Apply (x, args)`, where `x : C.slot` is the head slot and `args : expr C.slot_map` is the slot map of children. Set `γ := (σ.pre ** σ.dom) *** τ` and `α := shape_lookup γ x` (the arity that `γ` assigns to the head slot).

The algorithm does three things.

1. **Recurse on children.** For every `(y, child) ∈ args`, let `β := arity_lookup α y`. Then `child` is valid in `γ ** β = (σ.pre ** σ.dom) *** (β :: τ)` definitionally. Recurse: `subst σ (β :: τ) child`. Collect into a slot map `new_args` with the same keys as `args`.

2. **Classify the head `x`.** `classify` is a structural walk: `walk_tau` over `τ` cons-by-cons, and (when `τ` is exhausted) a single `slot_sort` against `σ.dom`. The returned `loc` carries no list:

   ```ocaml
   type loc =
     | In_pre of slot   (* slot in (σ.pre *** σ.cod) *** τ, already lifted *)
     | In_tau of slot   (* same shape, already lifted *)
     | In_dom of slot   (* sub-slot of σ.dom *)
   ```

   - On `Right z` at a `τ`-layer with arity `β` and tail `rest`: return `In_tau (arity_shift ((σ.pre *** σ.cod) *** rest) β z)`.
   - On `Left y` at a `τ`-layer: recurse on `rest`; on the way back, apply `shape_shift ((σ.pre *** σ.cod) *** rest) β` to the slot inside `In_pre`/`In_tau`. `In_dom` is passed through.
   - When `τ` is exhausted: `slot_sort σ.pre σ.dom x` decides. `Right z → In_dom z`. `Left p → In_pre (shift_through σ.pre σ.cod p)` (lift `p` through `σ.cod` to land in `σ.pre *** σ.cod`).

   `shift_through : shape -> arity list -> slot -> slot` is one `List.fold_right` over a cons-convention list with accumulator `(slot, shape)`:

   ```
   fst (List.fold_right
          (fun α (sl, shape) -> (shape_shift shape α sl, shape ** α))
          lst
          (slot, base))
   ```

   No `List.rev`, no `take`/`drop`/`List.nth`.

3. **Build the result.** Dispatch on `classify`'s output:
   - `In_pre s | In_tau s`: return `Apply (s, new_args)`.
   - `In_dom z`: look up `e' := List.assoc z σ.sub` (valid in `(σ.pre *** σ.cod) ** α` where `α := shape_lookup γ x`), build the auxiliary substitution `σ' := { pre = σ.pre *** σ.cod ; dom = α ; cod = τ ; sub = new_args }`, and return `subst σ' [] e'`.

The recursion is structural on the input expression in cases 1, 3.1, and 3.2. Case 3.3 recurs on a different expression `e'` (drawn from `σ.sub`), not structurally smaller in the input.

## Instantiation: `ListCarrier`

The list-based representation that matches `syntax.ml`:

  - `type arity = Ar of arity list`
  - `type shape = Sh of arity list`  (distinct tag from `Ar`, so a value declares its role)
  - `type slot = int`  (de Bruijn index from the *right*: the last entry of the list has slot 0)
  - `( ** ) (Sh gs) (Ar a) = Sh (gs @ a)`
  - `shape_entries (Sh xs)`: pair each element with its de-Bruijn-from-right slot, i.e. element at list position `i` in a list of length `n` gets slot `n - 1 - i`. `arity_entries (Ar xs)` is the same recipe applied to an arity's binder list.
  - `shape_lookup (Sh xs) x` and `arity_lookup (Ar xs) x` both reduce to `List.nth xs (List.length xs - 1 - x)`.
  - `shape_shift γ (Ar a) x = x + List.length a`
  - `arity_shift γ α z = z`  (`α`'s slots already use the same de-Bruijn-from-right convention that `γ ** α` uses for them).
  - `slot_sort γ (Ar a) x = if x < List.length a then Right x else Left (x - List.length a)`
  - `empty_arity = Ar []`

In this carrier `Sh gs ** Ar [] = Sh gs` definitionally (list-append-empty is identity). With the new design we never rely on this — `aux.cod = τ : arity list` and `γ *** [] = γ` is the only "unit" we use, which is by the cons-as-snoc definition of `***`, not by any property of `empty_arity`.

## Instantiation: `TreeCarrier`

A second carrier with binary-tree-structured shapes and arities, to confirm the algorithm doesn't need explicit re-associations beyond what the carrier already exposes.

  - `type 'a tree = Empty | Slot of 'a | Oplus of 'a tree * 'a tree`
  - `type arity = Arity of arity tree`
  - `type shape = Shape of arity tree`
  - `type slot = Here | L of slot | R of slot` (a path through a tree)
  - `( ** ) (Shape t) (Arity a) = Shape (Oplus (t, a))` — *naive* `Oplus`, no smart collapsing.
  - `shape_entries (Shape t)` and `arity_entries (Arity t)` walk the tree, collecting `(path, arity)` pairs (prepend `L`/`R` per step).
  - `shape_shift γ α x = L x` — slots of `γ` sit in the left subtree of `γ ** α`.
  - `arity_shift γ α z = R z` — slots of `α` sit in the right subtree.
  - `slot_sort γ α (L p) = Left p`, `slot_sort γ α (R p) = Right p`. `Here` is impossible at a `γ ** α` (that's an `Oplus`, not a `Slot`).
  - `empty_arity = Arity Empty`

In this carrier `Shape t ** Arity Empty = Shape (Oplus (t, Empty)) ≠ Shape t`. That doesn't matter for the algorithm: `***` over an arity list still satisfies `γ *** [] = γ` by `rfl`, which is the only unit the algorithm needs. If the algorithm worked here without re-associations, it confirms the design is portable.

## Examples

Three carried over from `syntax.ml`, plus their analogues on `TreeCarrier`:

  - `e1 = succ (succ zero)`, `e2 = plus zero x`, in the eight-symbol `γ`.
  - `ExampleSubst1`: `pre = Sh[λ]`, `dom = Ar[Ar[]]` (the binder for `x`), `cod = [Ar[Ar[]; Ar[]; Ar[]]]` (the binder for `y, z, w`), substitute `λ _. x` → `λ _. y`.
  - `ExampleSubst2`: same `σ`, substitute `λ _. λ _. x` → `λ _. λ _. y`.

These run inside `ocaml/syntaxAction2.ml` with `let () = …` so `ocaml -stdin < ocaml/syntaxAction2.ml` prints OK/FAIL lines. Both `ListCarrier` and `TreeCarrier` get the same suite.

## Verification

```
ocaml -stdin < ocaml/syntaxAction2.ml
```

Expected output: an OK line per example (validation of each input and of each substitution result), and the printed results matching `syntax.ml`'s `After: …` lines (modulo notation). Both carriers should produce the same `After:` shapes modulo their slot-representation (integers in `ListCarrier`, paths in `TreeCarrier`).

## Termination

`subst` is not structurally recursive on any single argument: the children branch shrinks the expression but keeps `σ.dom` fixed, while the `In_dom` aux branch jumps to a fresh `e := List.assoc z σ.sub` (unrelated to the input expression) but shrinks `σ.dom` to `head_arity`, a strict sub-arity of `σ.dom`.

Lex measure `(σ.dom.rank, e.rank)` decreases on every recursive call:

  - **Children.** `σ.dom` unchanged; `child` is a structural sub-expression of the input `Apply (x, args)`. Second component strictly smaller.
  - **Aux (`In_dom z`).** `aux_sigma.dom = head_arity = arity_lookup σ.dom z`. By the inductive structure of arities (`arity = Ar of arity list` etc.), the arity at a slot of `σ.dom` is a strict sub-arity of `σ.dom`. First component strictly smaller, second irrelevant.

`σ.cod`, `σ.sub`, and `τ` don't enter the measure.

This is the same shape as Ivan's `(γ.rank, E.rank)` lex measure in `HigherRankSyntax/HigherRankSyntax/SyntaxRelMon.lean` (around `RelModExpr_unit_right`). Ivan's `γ` corresponds to our `σ.dom` — both are "the input-side shape that the substitution is actively consuming". Note: the full input shape `(σ.pre ** σ.dom) *** τ` is *not* a good measure since `σ.pre *** σ.cod` (after the aux call replaces `σ.dom`) can be larger than `σ.pre ** σ.dom`; what matters is the still-to-be-substituted part.

In Lean: `termination_by (σ.dom.rank, e.rank)` with `Prod.Lex` well-founded relation; no Bove-Capretta, no graph-of-the-function detour.

## Findings from the `TreeCarrier` exercise

  - The algorithm itself needs **no re-associations**: the cons-as-snoc `***` and the four CARRIER laws are enough; both carriers run the same `Make` functor unchanged. Specifically, nothing in `subst`/`classify`/`shift_through` examines or reshapes the inner tree of a shape; everything goes through `slot_sort`, `shape_shift`, `arity_shift`, `shape_lookup`, `arity_lookup`. So the algorithm is genuinely carrier-polymorphic.

  - The `TreeCarrier`'s `**` with the empty arity does **not** collapse (`Shape t ** Arity TEmpty = Shape (TOplus (t, TEmpty))`), but this **doesn't bite the algorithm** because we never rely on `γ ** empty_arity = γ`. The relevant unit is `γ *** [] = γ`, which is `rfl` from the cons-as-snoc definition of `***`.

  - The non-collapse **is visible to the user when constructing examples**: under a binder of an "empty arity" (a var-like arity), the original shape's slots get an extra `L`-wrap. This is a faithful exposure of what the algorithm "sees" — exactly the visibility we wanted. In `ListCarrier` the same effect is invisible because `Sh xs ++ []` reduces to `Sh xs` definitionally; that's a property of the list representation, not of the algorithm.

  - This suggests the Lean design should follow the `TreeCarrier` pattern (naive `**`, no smart unit), with the empty arity exposed as a distinct shape via `**`. The algorithm continues to work; the user's expressions just carry the extra `L`-paths that record the descent under empty binders, and any law about "empty binders don't actually change anything" lives as a transport at the *expression* level (a renaming), not in the carrier algebra.

## Findings: porting to Lean

The end goal in Lean is exhibiting expressions as a *relative monad* on the variable functor.  The OCaml implementation suggests the following design choices for that port.

### 1. `slot_map` is a dependent function in Lean

In OCaml, `'a slot_map = (slot * 'a) list` carries the invariant "all keys distinct" *outside* the type system, plus implicit invariants about which slots are valid for which shape.  In Lean both invariants become part of the type.

The canonical replacement is a *dependent function over a shape-indexed slot type*:

```lean
-- In Lean:
def Slots : Shape → Type       -- the slots of a shape are a type indexed by that shape
def ArSlots : Arity → Type     -- the slots of an arity are a type indexed by that arity
def shapeArity (γ : Shape) : Slots γ → Arity
def arityArity (α : Arity) : ArSlots α → Arity
```

`shape_entries γ : arity slot_map` becomes `shapeArity γ : Slots γ → Arity` (the support is `Slots γ` itself; distinctness is automatic).  The children of an `Apply` head with arity `α` become a *dependent function* `(y : ArSlots α) → Expr (γ ** arityArity α y)`.

### 2. The shift/sort triple collapses to one equivalence

In OCaml the carrier has `shape_shift`, `arity_shift`, `slot_sort` plus axiomatic laws (image, disjoint cover, two cancellations).  In Lean all of this is a single equivalence:

```lean
slotsExtIso (γ : Shape) (α : Arity) : Slots (γ ** α) ≃ Slots γ ⊕ ArSlots α
```

`shape_shift` is `(slotsExtIso γ α).symm ∘ Sum.inl`; `arity_shift` is `(slotsExtIso γ α).symm ∘ Sum.inr`; `slot_sort` is `slotsExtIso γ α`.  The four OCaml laws become the inverse properties of an `Equiv` (free from `Mathlib.Logic.Equiv.Basic`).  Two compatibility laws remain — `shapeArity` of an image equals the corresponding arity-side lookup:

```lean
shapeArity (γ ** α) ((slotsExtIso γ α).symm (Sum.inl s)) = shapeArity γ s
shapeArity (γ ** α) ((slotsExtIso γ α).symm (Sum.inr y)) = arityArity α y
```

### 3. The cons-as-snoc list convention pays off in Lean

`(***)` is defined cons-as-snoc precisely so that

```
γ *** (α :: rest) = (γ *** rest) ** α
```

holds *definitionally* in Lean.  The consequence: when `subst` descends under a binder `β` and consing on `τ`, the child's shape is

```
γ_base *** τ ** β = γ_base *** (β :: τ)
```

by `rfl` — no transport between the child's expected shape and its actual shape, no rho-style associator/unitor sandwich.

### 4. The substitution data is a dependent function (Kleisli morphism)

`σ.sub : expr slot_map list` (mirroring `σ.dom`) is the OCaml encoding of what in Lean is a single dependent function:

```lean
structure Substitution where
  pre : Shape
  dom : List Arity
  cod : List Arity
  sub : (x : Slots (pre *** dom)) → Expr ((pre *** cod) ** shapeArity _ x)
```

This is the standard *relative-monad* form — a section of a dependent type, indexed by an input slot and producing an expression of matching arity in the output shape.  The OCaml list-mirroring-list shape is the same data after unrolling `Slots (pre *** dom) ≃ Slots pre ⊕ ⋯` via repeated `slotsExtIso`.

The "identity on `pre`" requirement — that `sub x` for `x` lifted from `pre` is the variable-as-expression image of `x` in `pre *** cod` — is a separable equation, enforceable by construction.

### 5. The expression type is shape-indexed

```lean
inductive Expr : Shape → Type where
  | apply (γ : Shape) (x : Slots γ)
          (args : (y : ArSlots (shapeArity γ x)) →
                  Expr (γ ** arityArity _ y))
        : Expr γ
```

Strictly positive (the recursive use is under a dependent function whose domain doesn't mention `Expr`); Lean will accept this directly.  Validity checking disappears — every `Expr γ` is well-formed by construction.

### 6. Path to the relative monad

The two layers from Ivan's branch already exist in mathlib-on-LeanHoG and on `ivan/relative-monad`:

- generic relative-monad / Kleisli-triple / relative-adjunction in `HigherRankSyntax/HigherRankSyntax/RelativeMonads/*.lean` (`0` `sorry`s);
- the syntax instance `SyntaxRelMon.lean` (5 `sorry`s, all in transport equations for `unit_right`/`unit_left`/`comp_lift`).

Our carrier-based `Expr` should plug into the first layer in the same way Ivan's `RelModExpr` does, but with the cons-as-snoc convention making most of his transport sorries definitional.  The two remaining substantive proofs are `unit_left` and `comp_lift`.

### 7. Termination — still open

The OCaml `subst` is *not* structural on the input expression: the `In_dom` branch recurses on `e'`, drawn from `σ.sub`, which is unrelated.  Lean needs a well-founded measure.  Two candidates:

- (a) `(γ.rank, e.rank)` lexicographic — `γ.rank` is the depth of the shape's binder tree, `e.rank` the expression's recursion depth.  Ivan uses this for `RelModExpr_unit_right`.
- (b) Bove–Capretta-style domain predicate plus a separate totality proof.

(a) is lighter; (b) buys cleaner reduction equations at the cost of bureaucracy.  The OCaml exploration is silent on this — OCaml doesn't check termination.

### 8. Lean experiments I'd like to run (for approval)

Two small experiments would tell us whether this design scales.  Each is one new Lean file under `HigherRankSyntax/HigherRankSyntax/`, no edits to existing files.

- **Experiment A — Carrier and `Expr`.**  Define `class Carrier` with the dependent-`Slots`/`ArSlots`/`slotsExtIso` interface; instantiate it with a `List`-based analogue of `ListCarrier`; define the `Expr` inductive.  No `subst`, no laws.  Goal: confirm Lean accepts the inductive and the carrier-typeclass, and that the `slotsExtIso` discharges what OCaml encoded as four axioms.

- **Experiment B — `subst` (after A succeeds).**  Define `subst` with the cons-as-snoc convention and termination via Ivan's lex measure.  No relative-monad laws yet.  Goal: confirm `subst` elaborates and that the cons-as-snoc reductions kick in `rfl`-wise.

I will not begin either experiment without your explicit go.

### Guidance regarding Lean formalization

You should use dependent types to their full advantage. One obvious place where this is relevant is in the Lean version of `slot_map`. This cannot be a list representing a map, it will be more abstract. Perhaps something like this:

```lean
-- I am introducing these as variables for convenience, but we'd really want a proper structure for the Carrier, etc.
variable (shape : Type)
variable (arity : Type)
variable (shape_slots : shape -> Type) -- each shape has a type of slots, we may have to additionally require
                                       -- that shape_slots γ has additional functionaly, such as it is finite, but
                                       -- we should try to work with as few asumptions as possible
variable (arity_slots : shaope -> Type)

def slot_entries (γ : slot) := shape_slots γ -> arity
def arity_entries (α : arity) := arity_slots α -> arity
```
