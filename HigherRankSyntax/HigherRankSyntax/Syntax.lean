

inductive Arity where
| Ar : (List Arity) →  Arity

inductive Shape  where
| Sh : (List Arity) → Shape

def Arity.toShape : Arity → Shape
| Ar l => .Sh l

def Shape.concat : Shape → Shape → Shape
| Sh l, Sh l' => Sh (List.append l l')

def mixed_concat : Shape  → Arity → Shape
| γ, α   => Shape.concat γ (α.toShape)


/- inductive Shape where
  /-- the empty shape -/
| empty : Shape
  /-- the shape containing precisely one item -/
| slot : Shape → Shape
  /-- shape extension -/
| oplus : Shape → Shape → Shape
deriving Repr -/
-- TODO: implement better Repr instance for shapes


def var_in  : Arity → Shape →  Type
| α, Sh l => List.find? (fun β => β = α) l


@[inherit_doc]
notation "𝟘" => Shape.empty

@[inherit_doc]
notation (priority := default+1) γ:31 " ⊕ " δ:31 => Shape.oplus γ δ

/-- A synonym for a shape, used when we think of a shape as specifying
    the arity of a variable. -/
abbrev Arity := Shape

/-- The rank of a shape is the level of nesting of the slots -/
@[reducible]
def Shape.rank : Shape → Nat
| 𝟘 => 0
| .slot γ  => 1 + rank γ
| γ ⊕ δ => max (rank γ) (rank δ)

/-- Variables of given arity in a given shape -/
/- inductive var_in  : Arity → Shape → Type where
| varHere : ∀ {α : Shape}, var_in α α.slot
| varLeft : ∀ {γ δ} {{α}}, var_in α γ → var_in α (γ ⊕ δ)
| varRight : ∀ {γ δ} {{α}}, var_in α δ → var_in α (γ ⊕ δ) -/

infix:50 " ∈ " => var_in

/-- Fold on all variables in a given shape -/
def Shape.fold.{u} (γ : Shape) {A : Type u} (a : A) (f : A → ∀ ⦃α⦄, var_in α γ → A) : A :=
  match γ with
  | 𝟘 => a
  | .slot _ => f a .varHere
  | γ₁ ⊕ γ₂ => γ₂.fold (γ₁.fold a (fun b _ x => f b x.varLeft)) (fun b _ x => f b x.varRight)

theorem rank_Var_lt {α γ} (x : var_in α γ) : α.rank < γ.rank := by
  induction x
  case varHere => simp
  case varLeft δ β α _ _ =>
    simp [Shape.rank]
    calc
      α.rank < δ.rank := by assumption
           _ ≤ max δ.rank β.rank := by exact Nat.le_max_left δ.rank β.rank
  case varRight δ β α _ _ =>
    simp [Shape.rank]
    calc
      α.rank < β.rank := by assumption
           _ ≤ max δ.rank β.rank := by exact Nat.le_max_right δ.rank β.rank

/-- Expressions over a given shape -/
inductive Expr : Shape → Type where
/-- Apply a variable to arguments -/
| apply  : ∀ {γ α}, α ∈ γ → (∀ ⦃β⦄, β ∈ α → Expr (γ ⊕ β)) →  Expr γ

@[inherit_doc]
infix:80 " ◃ " => Expr.apply

@[reducible]
def Expr.sizeOf {γ} : Expr γ → Nat
| @Expr.apply _ α _ ts => 1 + α.fold 0 (fun n _ y => n + (ts y).sizeOf)

instance {γ} : SizeOf (Expr γ) where sizeOf := Expr.sizeOf

theorem Expr.sizeOfArg {γ α} (x : α ∈ γ) (ts : ∀ ⦃β⦄, β ∈ α → Expr (γ ⊕ β)) {θ} (y : θ ∈ α) :
  (ts y).sizeOf < (x ◃ ts).sizeOf := sorry
