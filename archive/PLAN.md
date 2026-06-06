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

# Plan: `ocaml/syntaxAction.ml`

## Context

We replace `syntax.ml` / `syntaxTree.ml` with a functor `Make (C : CARRIER) : …` that runs the higher-rank substitution algorithm uniformly over any shape-and-arity representation that satisfies a small interface. The interface is the user's spec above, lightly cleaned. The view is a *right action of arities on shapes*: `γ ** α` extends `γ`, and there is no shape-shape binary operation.

`ocaml/syntaxAction.ml` is new. `syntax.ml` and `syntaxTree.ml` are left untouched.

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
    dom : C.arity list ;
    cod : C.arity list ;
    sub : expr C.slot_map list ;
  }
  (* Invariants on a substitution σ:
     - List.length σ.sub = List.length σ.dom
     - for each index i, letting αᵢ = List.nth σ.dom i and σᵢ = List.nth σ.sub i:
         * the support of σᵢ equals the support of arity_entries αᵢ;
         * for each (x, e) ∈ σᵢ, with β = arity_lookup αᵢ x,
           e is valid in (σ.pre *** σ.cod) ** β. *)

  val subst : substitution -> C.arity list -> expr -> expr
  (* subst σ τ e:
     - assumes e valid in (σ.pre *** σ.dom) *** τ
     - returns an expression valid in (σ.pre *** σ.cod) *** τ. *)
end
```

## Algorithm sketch

The call `subst σ τ e` takes a substitution `σ`, an extension `τ : C.arity list`, and an expression `e` valid in `(σ.pre *** σ.dom) *** τ`. The lists `σ.dom`, `σ.cod`, and `τ` are *cons-as-snoc*: the head of the list is the *outermost* extension applied, so `γ *** (α :: rest) = (γ *** rest) ** α`. Consequently, consing a new arity onto a list adds a new outermost extension, and the equation `γ ** β = (γ_base *** τ) ** β = γ_base *** (β :: τ)` holds definitionally.

Destructure `e = Apply (x, args)`, where `x : C.slot` is the *head slot* of `e` and `args : expr C.slot_map` is the slot map of its *children*. Set `γ := (σ.pre *** σ.dom) *** τ` (the current shape) and `α := shape_lookup γ x` (the arity that `γ` assigns to the head slot).

The algorithm does three things.

1. **Recurse on children.** For every entry `(y, child) ∈ args` — where `y : C.slot` is the child's key and `child : expr` is the child expression — let `β := arity_lookup α y` (the binder arity that `α` assigns to `y`). Then `child` is valid in `γ ** β`, which equals `(σ.pre *** σ.dom) *** (β :: τ)` definitionally. Recurse: `subst σ (β :: τ) child`. Collect the results into a slot map `new_args` with the same keys as `args`.

2. **Classify the head `x`.** `classify` is a pair of mutually-recursive structural walks: `walk_tau` over `τ` cons-by-cons, and (when `τ` is exhausted) `walk_dom` over `σ.dom` zipped with `σ.sub`. The walks lift the result-slot through each peeled layer themselves, so the returned `loc` carries no list at all:

   ```ocaml
   type loc =
     | In_pre of slot                     (* slot in (σ.pre *** σ.cod) *** τ, already lifted *)
     | In_tau of slot                     (* same shape, already lifted *)
     | In_dom of expr slot_map * slot     (* matched σ.sub-entry and the sub-slot of its arity *)
   ```

   - On `Right z` at a `τ`-layer with arity `β` and tail `rest`: return `In_tau (arity_shift ((σ.pre *** σ.cod) *** rest) β z)`.
   - On `Left y` at a `τ`-layer: recurse on `rest`; on the way back, apply `shape_shift ((σ.pre *** σ.cod) *** rest) β` to the slot inside `In_pre`/`In_tau`. `In_dom` is passed through untouched (its lifting happens via the auxiliary substitution in step 3).
   - When `τ` is exhausted, `walk_dom` walks `σ.dom` and `σ.sub` together. On `Right z` it returns `In_dom (sm, z)` where `sm` is the head of `σ.sub` at the match site. On `Left y` it continues to the tails of both lists (dom-layers do not appear in the output, so no shifting on the way back). On `[]` it returns `In_pre (shift_through σ.pre σ.cod x)`.

   `shift_through : shape -> arity list -> slot -> slot` is the single helper, defined as one `List.fold_right` over a cons-convention list with accumulator `(slot, shape)`:

   ```
   fst (List.fold_right
          (fun α (sl, shape) -> (shape_shift shape α sl, shape ** α))
          lst
          (slot, base))
   ```

   `fold_right` visits the innermost extension first on a cons-convention list — exactly the direction `shape_shift` wants. No `List.rev`, no `take`/`drop`/`List.nth` anywhere.

3. **Build the result.** Dispatch on `classify`'s output:
   - `In_pre s | In_tau s`: return `Apply (s, new_args)`.
   - `In_dom (sm, z)`: look up `e' := List.assoc z sm` (valid in `(σ.pre *** σ.cod) ** α` where `α := shape_lookup γ x`), build the auxiliary substitution `σ'` with `pre = σ.pre *** σ.cod`, `dom = [α]`, `cod = τ`, `sub = [new_args]`, and return `subst σ' [] e'`.

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

In this carrier `Sh gs ** Ar [] = Sh gs` definitionally (list-append-empty is identity), so the user's caveat about `γ ** empty_arity ≠ γ` is *vacuous here*; a future tree- or named-carrier where `** empty_arity` reorganises structure will not enjoy this and rho-style transports will resurface there.

## Examples

Three carried over from `syntax.ml`:

  - `e1 = succ (succ zero)`, `e2 = plus zero x`, in the eight-symbol `γ`.
  - `ExampleSubst1`: `pre = [λ]`, `dom = [x]`, `cod = [y;z;w]`, substitute `λ _. x` → `λ _. y`.
  - `ExampleSubst2`: `pre = [λ]`, `dom = [x]`, `cod = [y;z;w]`, substitute `λ _. λ _. x` → `λ _. λ _. y`.

These run inside `ocaml/syntaxAction.ml` with `let () = …` so `ocaml -stdin < ocaml/syntaxAction.ml` prints OK/FAIL lines.

## Verification

```
ocaml -stdin < ocaml/syntaxAction.ml
```

Expected output: an OK line per example (validation of each input and of each substitution result), and the printed results matching `syntax.ml`'s `After: …` lines (modulo notation).

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
slotsExtIso (γ : Shape) (α : Arity) : Slots (γ ** α) ≃ Slots γ ++ ArSlots α
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

This is the standard *relative-monad* form — a section of a dependent type, indexed by an input slot and producing an expression of matching arity in the output shape.  The OCaml list-mirroring-list shape is the same data after unrolling `Slots (pre *** dom) ≃ Slots pre ++ ⋯` via repeated `slotsExtIso`.

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
