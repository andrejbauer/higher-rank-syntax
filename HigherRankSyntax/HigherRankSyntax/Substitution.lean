
import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ ⦃α⦄, α ∈ γ → Expr (δ ⊕ α)
infix:25 " →ˢ " => Substitution

namespace Substitution

/-- The identity substutition -/
def id {γ} : γ →ˢ γ :=
  fun {α} x => .varLeft x ◃ (fun {β} (y : β ∈ α) => (⟦ .varRight ʳ⇑ β ⟧ʳ (id y)))
termination_by γ.rank
decreasing_by apply rank_Var_lt ; assumption

@[inherit_doc]
notation " 𝟙ˢ " => Substitution.id

/-- Lift a renaming to a substitution -/
def lift {γ δ} (f : γ →ʳ δ) : γ →ˢ δ :=
  fun {_} x => 𝟙ˢ (f x)

-- /-- Extend a substutution on the right. This is generally used when
--     a substitution needs to be used under a binder. -/
-- def extend {γ δ} (u : γ →ˢ δ) η : γ ⊕ η →ˢ δ ⊕ η
-- | _, .varLeft x =>  ⟦.varLeft ⟧ʳ (u x)
-- | _, .varRight y => 𝟙ˢ y.varRight

-- @[inherit_doc]
-- infixl:95 " ⇑ˢ " => Substitution.extend

/-- Compose a renaming and a substutition. -/
def renaming_comp {α β γ} (f : β →ʳ γ) (u : α →ˢ β) : α →ˢ γ :=
  fun ⦃δ⦄ x => ⟦ f ʳ⇑ δ ⟧ʳ u x

@[inherit_doc]
infixr:95 " ʳ∘ˢ " => Substitution.renaming_comp

/-- Compose a substitution and a renaming -/
def comp_renaming {α β γ} (u : β →ˢ γ) (f : α →ʳ β) : α →ˢ γ :=
  fun ⦃_⦄ x => u (f x)

@[inherit_doc]
infixr:95 " ˢ∘ʳ " => Substitution.comp_renaming

/-- Sum of substitutions -/
def sum {α β γ} (u : α →ˢ γ) (v : β →ˢ γ) : α ⊕ β →ˢ γ
| _, .varLeft x => u x
| _, .varRight y => v y

@[inherit_doc]
infix:30 " ⊕ˢ " => Substitution.sum

-- def act_middle {α β γ δ : Shape} (u : β →ˢ α ⊕ γ) : Expr ((α ⊕ β) ⊕ δ) → Expr ((α ⊕ γ) ⊕ δ)
--   | .varLeft (.varLeft x) ◃ ts => .varLeft (.varLeft x) ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act_middle u (⟦ .assocRight ⟧ʳ ts y))
--   | .varLeft (.varRight x) ◃ ts => act_right (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act_middle u (⟦ .assocRight ⟧ʳ ts y)) (u x)
--   | .varRight x ◃ ts => .varRight x ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act_middle u (⟦ .assocRight ⟧ʳ ts y))
-- termination_by e => (β.rank, Expr.sizeOf e)
-- decreasing_by
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
--   · apply Prod.Lex.left ; apply rank_Var_lt x
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

-- def act_left {α β γ} (u : α →ˢ β): Expr (α ⊕ γ) → Expr (β ⊕ γ)
--   | .varLeft x ◃ ts => act_right (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act_left u (⟦ .assocRight ⟧ʳ ts y)) (u x)
--   | .varRight x ◃ ts => .varRight x ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ act_left u (⟦ .assocRight ⟧ʳ ts y))
-- termination_by e => (α.rank, Expr.sizeOf e)
-- decreasing_by
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

-- def act_right {α β γ} (u : β →ˢ α ⊕ γ) : Expr (α ⊕ β) → Expr (α ⊕ γ)
--   | .varLeft x ◃ ts => .varLeft x ◃ (fun ⦃_⦄ y => act_middle u (ts y))
--   | .varRight x ◃ ts => inst (fun ⦃_⦄ y => act_middle u (ts y)) (u x)
-- termination_by e => (β.rank, Expr.sizeOf e)
-- decreasing_by
--   · apply Prod.Lex.right ; apply Expr.sizeOfArg
--   · apply Prod.Lex.right ; apply Expr.sizeOfArg
--   · apply Prod.Lex.left ; apply rank_Var_lt x


/- To do : Adapt the instanciation functions, as they are needed to define act.-/

-- def inst_left {α β γ} (u : β →ˢ α) : Expr ((α ⊕ β) ⊕ γ) → Expr (α ⊕ γ)
--   | .varLeft (.varLeft x) ◃ ts => .varLeft x ◃ (fun ⦃δ⦄ y => ⟦ .assocLeft ⟧ʳ inst_left u (⟦ .assocRight ⟧ʳ ts y))
--   | .varLeft (.varRight x) ◃ ts => act_right (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ inst_left u (⟦ .assocRight ⟧ʳ ts y)) (u x)
--   | .varRight x ◃ ts => .varRight x ◃ (fun ⦃_⦄ y => ⟦ .assocLeft ⟧ʳ inst_left u (⟦ .assocRight ⟧ʳ ts y))
-- termination_by e => (β.rank, Expr.sizeOf e)
-- decreasing_by
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg
--   · apply Prod.Lex.left ; apply rank_Var_lt x
--   · apply Prod.Lex.right ; rw [Renaming.eq_size] ; apply Expr.sizeOfArg

-- def inst {α β} (u : β →ˢ α) : Expr (α ⊕ β) → Expr α
--   | .varLeft x ◃ ts => x ◃ (fun ⦃_⦄ y => inst_left u (ts y))
--   | .varRight x ◃ ts => inst (fun ⦃_⦄ y => inst_left u (ts y)) (u x)
-- termination_by e => (β.rank, Expr.sizeOf e)
-- decreasing_by
--   · apply Prod.Lex.right ; apply Expr.sizeOfArg
--   · apply Prod.Lex.right ; apply Expr.sizeOfArg
--   · apply Prod.Lex.left ; apply rank_Var_lt x

def extendL {α γ' β γ} {θ} (f : γ →ʳ α ⊕ γ' ⊕ β) : γ ⊕ θ →ʳ α ⊕ γ' ⊕ (β ⊕ θ)
| _, .varLeft x => (_ ⇑ʳ (_ ⇑ʳ .varLeft) ) (f x)
| _, .varRight x => .varRight (.varRight (.varRight x))

def extendR {α δ' β δ} {θ} (g : α ⊕ δ' ⊕ β →ʳ δ) : α ⊕ δ' ⊕ (β ⊕ θ) →ʳ δ ⊕ θ
| _, .varLeft x => .varLeft (g (.varLeft x))
| _, .varRight (.varLeft x) => .varLeft (g (.varRight (.varLeft x)))
| _, .varRight (.varRight (.varLeft x)) => .varLeft (g (.varRight (.varRight x)))
| _, .varRight (.varRight (.varRight x)) => .varRight x

-- def viewR {α β γ δ} : α ⊕ β ⊕ γ ⊕ δ →ʳ (α ⊕ β ⊕ γ) ⊕ δ
-- | _, .varLeft x => .varLeft (.varLeft x)
-- | _, .varRight (.varLeft x) => .varLeft (.varRight (.varLeft x))
-- | _, .varRight (.varRight (.varLeft x)) => .varLeft (.varRight (.varRight x))
-- | _, .varRight (.varRight (.varRight x)) => .varRight x

mutual

@[reducible]
def act' {α γ' δ' β} {γ δ} (f : γ →ʳ α ⊕ γ' ⊕ β) (u : γ' →ˢ δ') (g : α ⊕ δ' ⊕ β →ʳ δ) : Expr γ → Expr δ
| x ◃ ts =>
  match f x with
  | .varLeft y => g (.varLeft y) ◃ (fun ⦃β⦄ i => act' (extendL f) u (extendR g) (ts i))
  | .varRight (.varLeft (α := χ) y) => ⟦ g ⟧ʳ _
  | .varRight (.varRight y) => g (.varRight (.varRight y)) ◃ (fun ⦃θ⦄ i => act' (extendL f) u (extendR g) (ts i))

def inst' {α γ' β} {γ δ} (f : γ →ʳ (α ⊕ γ') ⊕ β) (u : γ' →ˢ α) (g : α ⊕ β →ʳ δ) : Expr γ → Expr δ
| x ◃ ts =>
  match f x with
  | .varLeft (.varLeft y) => sorry
  | .varLeft (.varRight y) => sorry
  | .varRight y => sorry

end

-- mutual

--   def act {γ δ} (u : γ →ˢ δ) : Expr γ → Expr δ
--   | x ◃ ts => inst (comp ts u) (u x)

--   def inst {δ α} (u : α →ˢ δ) : Expr (δ ⊕ α) → Expr δ
--   | .varLeft x ◃ ts => _
--   | .varRight x ◃ ts => _

--   /-- Composition of substitutions -/
--   def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
--   | _, x => act _ (u x)

-- end

@[inherit_doc]
notation:60 " ⟦" u "⟧ˢ " e:61 => Substitution.act u e


@[inherit_doc]
notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

-- /-- The extension of identity is identity -/
-- def extend_id (γ δ) : @id γ ⇑ˢ δ = 𝟙ˢ := by
--   funext α x
--   cases x
--   case varRight => simp!
--   case varLeft x =>
--     dsimp! ; unfold id ; simp!
--     funext β y
--     rw [← Renaming.act_comp]
--     congr
--     funext δ z
--     cases z <;> simp! [Renaming.comp]

end Substitution
