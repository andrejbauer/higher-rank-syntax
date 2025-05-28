import HigherRankSyntax.Syntax
import Mathlib.CategoryTheory.Category.Basic

def Renaming (γ δ : Shape) := ∀ {{α}}, var_in α γ → var_in α δ
infix:25 " →ʳ " => Renaming

namespace Renaming

@[reducible]
def id {γ} : γ →ʳ γ := fun {{_}} x => x

notation "𝟙ʳ" => Renaming.id

def comp {γ δ η} (f : γ →ʳ δ) (g : δ →ʳ η) : γ →ʳ η :=
  fun {{_}} x => g (f x)

notation:90 g:90 " ∘ʳ " f:90 => Renaming.comp f g

@[reducible]
def sum {γ δ θ} (f : γ →ʳ θ) (g : δ →ʳ θ) : γ ⊕ δ →ʳ θ
| _, .varLeft x => f x
| _, .varRight x => g x

infix:30 " ⊕ʳ " => Renaming.sum

@[reducible]
def assocLeft {γ δ θ} : γ ⊕ (δ ⊕ θ) →ʳ (γ ⊕ δ) ⊕ θ :=
  (.varLeft ∘ʳ .varLeft) ⊕ʳ ((.varLeft ∘ʳ .varRight) ⊕ʳ .varRight)

@[reducible]
def assocRight {γ δ θ} : (γ ⊕ δ) ⊕ θ →ʳ γ ⊕ (δ ⊕ θ) :=
  (.varLeft ⊕ʳ (.varRight ∘ʳ .varLeft)) ⊕ʳ (.varRight ∘ʳ .varRight)

@[reducible]
def insertZeroRight {γ} : γ →ʳ γ ⊕ 𝟘 := .varLeft

@[reducible]
def cancelZeroRight {γ} : γ ⊕ 𝟘 →ʳ γ
| _, .varLeft x => x

@[reducible]
def insertZeroLeft {γ} : γ →ʳ 𝟘 ⊕ γ := .varRight

@[reducible]
def cancelZeroLeft {γ} : 𝟘 ⊕ γ →ʳ γ
| _, .varRight x => x

def extendRight {γ δ} (f : γ →ʳ δ) (η) : γ ⊕ η →ʳ δ ⊕ η
| _, .varLeft x => .varLeft (f x)
| _, .varRight y => .varRight y

infixl:95 " ʳ⇑ " => Renaming.extendRight

def extendLeft {γ δ} (η) (f : γ →ʳ δ) : η ⊕ γ →ʳ η ⊕ δ
| _, .varLeft x => .varLeft x
| _, .varRight y => .varRight (f y)

infixl:95 " ⇑ʳ " => Renaming.extendLeft

def extend_id {γ η} : 𝟙ʳ ʳ⇑ η = @id (γ ⊕ η) := by
  funext α x
  rcases x with ⟨x, y⟩ <;> rfl

def extendRight_comp {γ δ η θ} {g : δ →ʳ η} {f : γ →ʳ δ}:
  (g ∘ʳ f) ʳ⇑ θ = (g ʳ⇑ θ) ∘ʳ (f ʳ⇑ θ) := by
  funext _ x
  cases x <;> rfl

def extendLeft_comp {γ δ₁ δ₂ δ₃} {g : δ₂ →ʳ δ₃} {f : δ₁ →ʳ δ₂}:
  γ ⇑ʳ (g ∘ʳ f) = (γ ⇑ʳ g) ∘ʳ (γ ⇑ʳ f) := by
  funext _ x
  cases x <;> rfl

def act {γ δ} (f : γ →ʳ δ) : Expr γ → Expr δ
  | x ◃ ts => f x ◃ (fun ⦃_⦄ y => act (f ʳ⇑ _) (ts y))

notation:60 " ⟦" f "⟧ʳ " e:61 => Renaming.act f e

theorem extend_comp {γ γ' δ δ'} (f : γ →ʳ γ') (g : δ →ʳ δ') :
  (γ' ⇑ʳ g) ∘ʳ (f ʳ⇑ δ)  = (f ʳ⇑ δ') ∘ʳ (γ ⇑ʳ g) := by
  funext α x
  cases x <;> simp [comp, extendLeft, extendRight]

/-- `actFree` distributes over composition -/
theorem actFree.map_comp {γ} {e : Expr γ} :
  ∀ {δ η} {f : γ →ʳ δ} {g : δ →ʳ η}, ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e) := by
  induction e
  case apply ih =>
    intros _ _ f g
    simp [act, comp, extendRight_comp]
    funext
    apply ih

theorem comp_assoc {γ δ η θ} {f : γ →ʳ δ} {g : δ →ʳ η} {h : η →ʳ θ} :
  (h ∘ʳ g) ∘ʳ f = h ∘ʳ (g ∘ʳ f) := by rfl

theorem eq_size {γ δ} (f : γ →ʳ δ) (e : Expr γ) : (⟦ f ⟧ʳ e).sizeOf = e.sizeOf := by
  induction e
  case apply ih =>
    sorry

/-- Extending the identity renaming on the left gives the identity renaming. -/
theorem extendLeft.id {γ δ} : γ ⇑ʳ @id δ = 𝟙ʳ := by
  funext α x
  cases x <;> simp [extendLeft]

/-- Extending the identity renaming on the right gives the identity renaming. -/
theorem extendRight.id {γ δ} : @id γ ʳ⇑ δ = 𝟙ʳ := by
  funext α x
  cases x <;> simp [extendRight]

/-- `act` acts trivially with the identity renaming -/
theorem act.map_id {γ} (e : Expr γ) : 𝟙ʳ.act e = e := by
  induction e
  case apply γ α x ts ih =>
    simp [act]
    funext α x
    rw [extendRight.id]
    apply ih

end Renaming

/-- The category of shapes and renamings -/
instance ShapeCat : CategoryTheory.Category Shape where
  Hom := Renaming
  id := @Renaming.id
  comp := Renaming.comp
