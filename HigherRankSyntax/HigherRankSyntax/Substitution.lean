
import HigherRankSyntax.Syntax
import HigherRankSyntax.Renaming

def Substitution γ δ := ∀ {{α}}, Var α γ → Expr δ α
infix:25 " →ˢ " => Substitution

namespace Substitution

/-- The identity substutition -/
def id {γ} : γ →ˢ γ :=
  fun {α} x => x ◃ (fun {β} (y : Var β α) => (id (.varRight y)))
termination_by γ.rank
decreasing_by apply rank_Var_lt ; sorry

@[inherit_doc]
notation " 𝟙ˢ " => Substitution.id

/-- Lift a renaming to a substitution -/
def lift {γ δ} (f : γ →ʳ δ) : γ →ˢ δ :=
  fun {_} x => 𝟙ˢ (f x)

/-- Extend a substutution on the right. This is generally used when
    a substitution needs to be used under a binder. -/
def extend {γ δ} (u : γ →ˢ δ) η : γ ⊕ η →ˢ δ ⊕ η
| _, .varLeft x =>  ⟦.varLeft ⟧ʳ (u x)
| _, .varRight y => 𝟙ˢ y.varRight

@[inherit_doc]
infixl:95 " ⇑ˢ " => Substitution.extend

/-- Compose a renaming and a substutition. -/
def renaming_comp {α β γ} (f : β →ʳ γ) (u : α →ˢ β) : α →ˢ γ :=
  fun ⦃δ⦄ x => ⟦ f ⟧ʳ u x

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

/- The following definitions are obsolete because the definition of Expr was changed,
`act_left` and `act_right` had essencially the same role as
`actFree` and `actBound` (which are now the ones in use). -/

mutual

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



/-- The action of a substutition on an expression -/
def act {α β δ} (u : α →ˢ β) : (Expr α δ) → (Expr β δ)
| x ◃ ts => sorry
  -- inst (fun ⦃_⦄ y => act_left u (ts y)) (u x)
| x ◂ ts => sorry


end -- mutual

@[inherit_doc]
notation:60 " ⟦" u "⟧ˢ " e:61 => Substitution.act u e

/-- Composition of substitutions -/
def comp {γ δ θ} (u : γ →ˢ δ) (v : δ →ˢ θ) : γ →ˢ θ
| _, x => act v (u x)

@[inherit_doc]
notation:90 g:90 " ∘ˢ " f:91 => Substitution.comp f g

/-- The extension of identity is identity -/
def extend_id (γ δ) : @id γ ⇑ˢ δ = 𝟙ˢ := by
  funext α x
  cases x
  case varRight => simp!
  case varLeft x =>
    dsimp! ; unfold id ; simp!
    funext β y
    rw [← Renaming.act_comp]
    congr
    funext δ z
    cases z <;> simp! [Renaming.comp]

end Substitution
