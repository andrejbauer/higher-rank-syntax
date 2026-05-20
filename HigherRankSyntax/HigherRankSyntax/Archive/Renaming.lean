import HigherRankSyntax.Archive.Syntax
import Mathlib.CategoryTheory.Category.Basic


namespace Archive

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

def actFree {γ γ' δ} (f : γ →ʳ γ') : Expr γ δ → Expr γ' δ
  | x ◃ ts => f x ◃ (fun ⦃_⦄ y => actFree (f ʳ⇑ _) (ts y))
  | x ◂ ts => x ◂ (fun ⦃_⦄ y => actFree (f ʳ⇑ _) (ts y))

def actBound {γ δ δ'} (f : δ →ʳ δ') : Expr γ δ → Expr γ δ'
  | x ◃ ts => x ◃ (fun ⦃_⦄ y => actFree (_ ⇑ʳ f) (ts y))
  | x ◂ ts => f x ◂ (fun ⦃_⦄ y => actFree (_ ⇑ʳ f) (ts y))

notation:60 " ⟦" f "⟧ʳ " e:61 => Renaming.actFree f e

theorem extend_comp {γ γ' δ δ'} (f : γ →ʳ γ') (g : δ →ʳ δ') :
  (γ' ⇑ʳ g) ∘ʳ (f ʳ⇑ δ)  = (f ʳ⇑ δ') ∘ʳ (γ ⇑ʳ g) := by
  funext α x
  cases x <;> simp [comp, extendLeft, extendRight]

/-- `actFree` distributes over composition -/
theorem actFree.map_comp {γ δ} {e : Expr γ δ} :
  ∀ {δ η} {f : γ →ʳ δ} {g : δ →ʳ η}, ⟦ g ∘ʳ f ⟧ʳ e = ⟦ g ⟧ʳ (⟦ f ⟧ʳ e) := by
  induction e
  case applyFree ih =>
    intros _ _ f g
    simp [actFree, comp, extendRight_comp]
    funext
    apply ih
  case applyBound ih =>
    intros _ _ f g
    simp [actFree, comp, extendRight_comp]
    funext
    apply ih

theorem comp_assoc {γ δ η θ} {f : γ →ʳ δ} {g : δ →ʳ η} {h : η →ʳ θ} :
  (h ∘ʳ g) ∘ʳ f = h ∘ʳ (g ∘ʳ f) := by rfl

theorem eq_size {γ γ' δ} (f : γ →ʳ γ') (e : Expr γ δ) : (⟦ f ⟧ʳ e).sizeOf = e.sizeOf := by
  induction e
  case applyFree ih =>
    sorry
  case applyBound ih =>
    sorry

/-- Extending the identity renaming on the left gives the identity renaming. -/
theorem extendLeft.id {γ δ} : γ ⇑ʳ @id δ = 𝟙ʳ := by
  funext α x
  cases x <;> simp [extendLeft]

/-- Extending the identity renaming on the right gives the identity renaming. -/
theorem extendRight.id {γ δ} : @id γ ʳ⇑ δ = 𝟙ʳ := by
  funext α x
  cases x <;> simp [extendRight]

/-- `actFree` acts trivially with the identity morphism -/
theorem actFree.map_id {γ δ} (e : Expr γ δ) : 𝟙ʳ.actFree e = e := by
  induction e
  case applyFree γ δ α x ts ih =>
    simp [actFree]
    funext α x
    rw [extendRight.id]
    apply ih
  case applyBound γ δ α x ts ih =>
    simp [actFree]
    funext α x
    rw [extendRight.id]
    apply ih

/-- `actBound` acts trivially with the identity morphism -/
theorem actBound.map_id {γ δ} (e : Expr γ δ) : 𝟙ʳ.actBound e = e := by
  cases e
  case applyFree α x ts =>
    simp [actBound]
    funext
    rw [extendLeft.id]
    apply actFree.map_id
  case applyBound α x ts =>
    simp [actBound]
    funext
    rw [extendLeft.id]
    apply actFree.map_id

/-- `actBound` distributes over composition -/
theorem actBound.map_comp {γ δ₁} {e : Expr γ δ₁} :
  ∀ {δ₂ δ₃} {f : δ₁ →ʳ δ₂} {g : δ₂ →ʳ δ₃}, (g ∘ʳ f).actBound e = g.actBound (f.actBound e) := by
    cases e
    case applyFree α x ts =>
      intros δ₂ δ₃ f g
      simp [actBound]
      funext θ y
      rw [extendLeft_comp]
      apply actFree.map_comp
    case applyBound α x ts =>
      intros δ₂ δ₃ f g
      simp [actBound]
      constructor
      · rfl
      · funext β y
        rw [extendLeft_comp]
        apply actFree.map_comp

/-- `actFree` and `actBound` commute. -/
theorem actFree_actBound {γ γ' δ δ'} (f : γ →ʳ γ') (g : δ →ʳ δ') (e : Expr γ δ) :
  f.actFree (g.actBound e) = g.actBound (f.actFree e) := by
  cases e
  case applyFree α x ts =>
    simp [actFree, actBound]
    funext β y
    rw [←actFree.map_comp, ←actFree.map_comp]
    congr
    symm ; apply extend_comp
  case applyBound α x ts =>
    simp [actFree, actBound]
    funext β y
    rw [←actFree.map_comp, ←actFree.map_comp]
    congr
    symm ; apply extend_comp

end Renaming

/-- The category of shapes and renamings -/
instance ShapeCat : CategoryTheory.Category Shape where
  Hom := Renaming
  id := @Renaming.id
  comp := Renaming.comp

end Archive
