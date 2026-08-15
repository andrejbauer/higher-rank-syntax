import HigherRankSyntax.Equations.QuotientMonad
import HigherRankSyntax.Typing.DecoratedTelescopeMonoid

/-!
# Decorations modulo equations

An equation presentation identifies the raw expressions used as classifiers in
a decoration.  Two classifiers are equal when they are both unclassified, or
when their expression-valued classifiers are derivably equal.  Two decorations
of the same raw telescope shape are equal when this holds at every immediate
and nested slot.

The raw arity is deliberately not quotiented.  A quotient decorated telescope
is therefore a raw shape together with an equivalence class of decorations of
exactly that shape.  Substitution descends because derivable equality is stable
simultaneously in the classifier expression and in all substitution fillers.
No well-formedness or typing judgment is introduced here.
-/

open CategoryTheory

variable {A : Type} {C : Carrier A} {S : C.Arity}

namespace Equations

private def classifierQuotient (E : EquationPresentation C S)
    (Ω : C.Arity) : Option C.Ty → Type
  | none => PUnit
  | some τ => Quotient (DerivEq.setoid E Ω τ)

private def classifierClass (E : EquationPresentation C S)
    (Ω : C.Arity) : (o : Option C.Ty) →
      (match o with | none => PUnit | some τ => Expr Ω τ) →
      classifierQuotient E Ω o
  | none, _ => PUnit.unit
  | some _, a => Quotient.mk _ a

/-- Equality of classifiers induced by a fixed equation presentation. -/
def ClassifierEq (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) {Ω : C.Arity} {τ : C.Ty} :
    ClassifierAt bd Ω τ → ClassifierAt bd Ω τ → Prop :=
  fun a b => classifierClass E Ω (bd τ) a = classifierClass E Ω (bd τ) b

namespace ClassifierEq

variable {E : EquationPresentation C S} {bd : C.Ty → Option C.Ty}

theorem refl {Ω : C.Arity} {τ : C.Ty} (a : ClassifierAt bd Ω τ) :
    ClassifierEq E bd a a := rfl

theorem of_eq {Ω : C.Arity} {τ : C.Ty} {a b : ClassifierAt bd Ω τ}
    (h : a = b) : ClassifierEq E bd a b := by
  subst b
  exact refl a

theorem symm {Ω : C.Arity} {τ : C.Ty} {a b : ClassifierAt bd Ω τ}
    (h : ClassifierEq E bd a b) : ClassifierEq E bd b a := by
  exact Eq.symm h

theorem trans {Ω : C.Arity} {τ : C.Ty} {a b c : ClassifierAt bd Ω τ}
    (h : ClassifierEq E bd a b) (k : ClassifierEq E bd b c) :
    ClassifierEq E bd a c := by
  exact Eq.trans h k

theorem cast {Γ Δ : C.Arity} (h : Γ = Δ) {τ : C.Ty}
    {a b : ClassifierAt bd Γ τ} (hab : ClassifierEq E bd a b) :
    ClassifierEq E bd (ClassifierAt.cast h a) (ClassifierAt.cast h b) := by
  subst Δ
  exact hab

theorem substitute {Γ Δ Φ : C.Arity} (σ θ : Subst Γ (S ⋈ Δ))
    (hσ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
      DerivEq E (σ x) (θ x))
    {τ : C.Ty} {a b : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ}
    (hab : ClassifierEq E bd a b) :
    ClassifierEq E bd (ClassifierAt.substitute σ a)
      (ClassifierAt.substitute θ b) := by
  unfold ClassifierEq at hab ⊢
  unfold ClassifierAt at a b
  unfold ClassifierAt.substitute
  generalize bd τ = o at a b hab ⊢
  cases o with
  | none => rfl
  | some υ =>
      apply Quotient.sound
      apply DerivEq.substitute σ θ
      · exact Quotient.exact hab
      · exact hσ

end ClassifierEq

/-- Pointwise equation equality of decorations of one fixed raw shape. -/
def DecorationEq [Precedence C] (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) {Ω Δ : C.Arity}
    (D F : Decoration bd Ω Δ) : Prop :=
  ∀ ⦃Φ Λ : C.Arity⦄ ⦃τ : C.Ty⦄
      (p : DecorationPath (C := C) Δ Φ Λ τ),
    ClassifierEq E bd (D p) (F p)

namespace DecorationEq

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

theorem refl {Ω Δ : C.Arity} (D : Decoration bd Ω Δ) :
    DecorationEq E bd D D := by
  intro Φ Λ τ p
  exact ClassifierEq.refl (D p)

theorem of_eq {Ω Δ : C.Arity} {D F : Decoration bd Ω Δ}
    (h : D = F) : DecorationEq E bd D F := by
  subst F
  exact refl D

theorem symm {Ω Δ : C.Arity} {D F : Decoration bd Ω Δ}
    (h : DecorationEq E bd D F) : DecorationEq E bd F D := by
  intro Φ Λ τ p
  exact ClassifierEq.symm (h p)

theorem trans {Ω Δ : C.Arity} {D F G : Decoration bd Ω Δ}
    (h : DecorationEq E bd D F) (k : DecorationEq E bd F G) :
    DecorationEq E bd D G := by
  intro Φ Λ τ p
  exact ClassifierEq.trans (h p) (k p)

/-- The setoid of decorations of a fixed raw shape. -/
def setoid (E : EquationPresentation C S) (bd : C.Ty → Option C.Ty)
    (Ω Δ : C.Arity) : Setoid (Decoration bd Ω Δ) where
  r := DecorationEq E bd
  iseqv := ⟨refl, symm, trans⟩

theorem substitute {Γ Δ Φ Ξ : C.Arity}
    (σ θ : Subst Γ (S ⋈ Δ))
    (hσ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
      DerivEq E (σ x) (θ x))
    {D F : Decoration bd (S ⋈ Γ ⋈ Φ) Ξ}
    (hD : DecorationEq E bd D F) :
    DecorationEq E bd (Decoration.substitute σ D)
      (Decoration.substitute θ F) := by
  intro Ω Λ τ p
  apply ClassifierEq.substitute
  · exact hσ
  · exact hD p

theorem empty (bd : C.Ty → Option C.Ty) (Ω : C.Arity) :
    DecorationEq E bd (Decoration.empty bd Ω) (Decoration.empty bd Ω) :=
  refl _

theorem concatenate {Ω Γ Δ : C.Arity}
    {D D' : Decoration bd Ω Γ}
    {F F' : Decoration bd (Ω ⋈ Γ) Δ}
    (hD : DecorationEq E bd D D') (hF : DecorationEq E bd F F') :
    DecorationEq E bd (Decoration.concatenate D F)
      (Decoration.concatenate D' F') := by
  intro Φ Λ τ p
  cases p with
  | here x =>
      rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [Decoration.concatenate_here_inl,
          Decoration.concatenate_here_inl]
        apply ClassifierEq.cast
        exact hD (.here y)
      · rw [Decoration.concatenate_here_inr,
          Decoration.concatenate_here_inr]
        apply ClassifierEq.cast
        exact hF (.here y)
  | nested x p =>
      rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [Decoration.concatenate_nested_inl,
          Decoration.concatenate_nested_inl]
        apply ClassifierEq.cast
        exact hD (.nested y p)
      · rw [Decoration.concatenate_nested_inr,
          Decoration.concatenate_nested_inr]
        apply ClassifierEq.cast
        exact hF (.nested y p)

end DecorationEq

/-- Decorations of a fixed raw telescope shape modulo classifier equations. -/
def QDecoration [Precedence C] (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) (Ω Δ : C.Arity) :=
  Quotient (DecorationEq.setoid E bd Ω Δ)

namespace QDecoration

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

def mk {Ω Δ : C.Arity} (D : Decoration bd Ω Δ) :
    QDecoration E bd Ω Δ :=
  Quotient.mk _ D

theorem sound {Ω Δ : C.Arity} {D F : Decoration bd Ω Δ}
    (h : DecorationEq E bd D F) :
    mk (E := E) D = mk (E := E) F :=
  Quotient.sound h

theorem exact {Ω Δ : C.Arity} {D F : Decoration bd Ω Δ}
    (h : mk D = (mk F : QDecoration E bd Ω Δ)) :
    DecorationEq E bd D F :=
  Quotient.exact h

end QDecoration

/-- Rooted raw decorated telescopes for a protected signature prefix. -/
abbrev PrefixedDecoratedTelescope [Precedence C] (S : C.Arity)
    (bd : C.Ty → Option C.Ty) (Γ : C.Arity) :=
  DecoratedTelescope bd (S ⋈ Γ)

/-- A quotient decorated telescope retains a literal raw shape and quotients
only the decorations of that shape. -/
def QDTel [Precedence C] (E : EquationPresentation C S)
    (bd : C.Ty → Option C.Ty) (Γ : C.Arity) :=
  Σ Δ : C.Arity, QDecoration E bd (S ⋈ Γ) Δ

namespace PrefixedDecoratedTelescope

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

/-- Reindex a rooted decoration by a substitution below its signature. -/
def act {Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    PrefixedDecoratedTelescope S bd Δ where
  arity := Ξ.arity
  decoration := Decoration.substitute (Φ := 1) σ Ξ.decoration

theorem act_id_decoration (Γ Θ : C.Arity)
    (D : Decoration bd (S ⋈ Γ) Θ) :
    (act (fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr x))
      (⟨Θ, D⟩ : PrefixedDecoratedTelescope S bd Γ)).decoration = D := by
  unfold act
  funext Φ Λ τ p
  apply ClassifierAt.substitute_idOfη

theorem act_id (Γ : C.Arity)
    (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    act (fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr x)) Ξ = Ξ := by
  rcases Ξ with ⟨Ω, D⟩
  rw [DecoratedTelescope.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    apply act_id_decoration

theorem act_comp_decoration {Γ Δ Ξ Θ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (D : Decoration bd (S ⋈ Γ) Θ) :
    (act (Subst.comp σ θ)
      (⟨Θ, D⟩ : PrefixedDecoratedTelescope S bd Γ)).decoration =
      (act θ (act σ
        (⟨Θ, D⟩ : PrefixedDecoratedTelescope S bd Γ))).decoration := by
  unfold act
  funext Φ Λ τ p
  apply ClassifierAt.substitute_comp

theorem act_comp {Γ Δ Ξ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (Ω : PrefixedDecoratedTelescope S bd Γ) :
    act (Subst.comp σ θ) Ω = act θ (act σ Ω) := by
  rcases Ω with ⟨Θ, D⟩
  rw [DecoratedTelescope.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    apply act_comp_decoration

theorem act_related {Γ Δ Θ : C.Arity}
    (σ θ : Subst Γ (S ⋈ Δ))
    (hσ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
      DerivEq E (σ x) (θ x))
    {D F : Decoration bd (S ⋈ Γ) Θ}
    (hD : DecorationEq E bd D F) :
    DecorationEq E bd
      (act σ (⟨Θ, D⟩ : PrefixedDecoratedTelescope S bd Γ)).decoration
      (act θ (⟨Θ, F⟩ : PrefixedDecoratedTelescope S bd Γ)).decoration := by
  intro Φ Λ τ p
  apply ClassifierEq.substitute
  · exact hσ
  · exact hD p

end PrefixedDecoratedTelescope

/-- Raw rooted decorated telescopes form a module over fixed-prefix syntax. -/
def PrefixedDTel [Precedence C] (S : C.Arity)
    (bd : C.Ty → Option C.Ty) :
    RelativeMonad.LeftModule (PrefixedSyntaxMonad C S) Type where
  obj Γ := PrefixedDecoratedTelescope S bd Γ
  map σ := ↾(PrefixedDecoratedTelescope.act σ)
  map_id Γ := by
    ext Ξ
    apply PrefixedDecoratedTelescope.act_id
  map_comp σ θ := by
    ext Ξ
    apply PrefixedDecoratedTelescope.act_comp

namespace QDTel

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

/-- The quotient class of a raw rooted decorated telescope. -/
def mk {Γ : C.Arity} (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    QDTel E bd Γ :=
  ⟨Ξ.arity, QDecoration.mk Ξ.decoration⟩

@[simp]
theorem mk_arity {Γ : C.Arity} (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    (mk (E := E) Ξ).1 = Ξ.arity := rfl

noncomputable section

/-- Apply a quotient-valued substitution to a quotient decorated telescope. -/
def act {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ) :
    QDTel E bd Γ → QDTel E bd Δ
  | ⟨Ξ, D⟩ => ⟨Ξ, Quotient.map
      (fun F => (PrefixedDecoratedTelescope.act
        (QExpr.representatives E σ) ⟨Ξ, F⟩).decoration)
      (fun _ _ h => PrefixedDecoratedTelescope.act_related
        (QExpr.representatives E σ) (QExpr.representatives E σ)
        (fun _ => DerivEq.refl _) h) D⟩

@[simp]
theorem act_mk {Γ Δ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    act σ (mk Ξ) =
      mk (PrefixedDecoratedTelescope.act
        (QExpr.representatives E σ) Ξ) := by
  apply Sigma.ext
  · rfl
  · rfl

theorem act_congr {Γ Δ : C.Arity}
    (σ θ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (h : σ = θ) (Ξ : QDTel E bd Γ) : act σ Ξ = act θ Ξ := by
  subst θ
  rfl

theorem act_id (Γ : C.Arity) (Ξ : QDTel E bd Γ) :
    act (𝟙 (RelativeMonad.Kleisli.of E.quotientMonad Γ)) Ξ = Ξ := by
  rcases Ξ with ⟨Θ, D⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Quotient.sound
        let σ : Subst Γ (S ⋈ Γ) :=
          fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr x)
        have hσ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
            DerivEq E
              (QExpr.representatives E
                (𝟙 (RelativeMonad.Kleisli.of E.quotientMonad Γ)) x)
              (σ x) := by
          intro Λ υ x
          apply QExpr.representative_related_raw
          rfl
        have hD := PrefixedDecoratedTelescope.act_related
          (QExpr.representatives E
            (𝟙 (RelativeMonad.Kleisli.of E.quotientMonad Γ)))
          σ hσ (DecorationEq.refl D)
        dsimp [σ] at hD
        rw [PrefixedDecoratedTelescope.act_id_decoration] at hD
        exact hD

theorem act_comp {Γ Δ Ξ : C.Arity}
    (σ : RelativeMonad.Kleisli.of E.quotientMonad Γ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Δ)
    (θ : RelativeMonad.Kleisli.of E.quotientMonad Δ ⟶
      RelativeMonad.Kleisli.of E.quotientMonad Ξ)
    (Ω : QDTel E bd Γ) :
    act (σ ≫ θ) Ω = act θ (act σ Ω) := by
  rcases Ω with ⟨Θ, D⟩
  induction D using Quotient.inductionOn with
  | _ D =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Quotient.sound
        let κ : Subst Γ (S ⋈ Ξ) :=
          Subst.comp (QExpr.representatives E σ)
            (QExpr.representatives E θ)
        let κ' := fun Λ υ (x : Γ ∋[υ] Λ) => QExpr.act E θ (σ Λ υ x)
        have hκ : ∀ {Λ : C.Arity} {υ : C.Ty} (x : Γ ∋[υ] Λ),
            DerivEq E (QExpr.representatives E κ' x) (κ x) := by
          intro Λ υ x
          apply QExpr.exact
          calc
            QExpr.mk E (QExpr.representatives E κ' x) =
                κ' Λ υ x := QExpr.mk_representatives E _ x
            _ = QExpr.act E θ (σ Λ υ x) := rfl
            _ = QExpr.act E θ
                (QExpr.mk E (QExpr.representatives E σ x)) :=
              congrArg (QExpr.act E θ) (QExpr.mk_representatives E σ x).symm
            _ = QExpr.mk E
                (Subst.act (Γ := S) (QExpr.representatives E θ) Λ
                  (QExpr.representatives E σ x)) :=
              QExpr.act_mk E θ _
            _ = QExpr.mk E (κ x) := rfl
        have hD := PrefixedDecoratedTelescope.act_related
          (QExpr.representatives E κ') κ hκ
          (DecorationEq.refl D)
        dsimp [κ] at hD
        rw [PrefixedDecoratedTelescope.act_comp_decoration] at hD
        have hκ' : κ' = σ ≫ θ := rfl
        rw [hκ'] at hD
        exact hD

end

end QDTel

/-- Quotient decorated telescopes form a module over quotient syntax. -/
noncomputable def QDTelModule [Precedence C]
    (E : EquationPresentation C S) (bd : C.Ty → Option C.Ty) :
    RelativeMonad.LeftModule E.quotientMonad Type where
  obj Γ := QDTel E bd Γ
  map σ := ↾(QDTel.act σ)
  map_id Γ := by
    ext Ξ
    apply QDTel.act_id
  map_comp σ θ := by
    ext Ξ
    apply QDTel.act_comp

namespace QDTel

variable [Precedence C] {E : EquationPresentation C S}
  {bd : C.Ty → Option C.Ty}

noncomputable section

/-- Quotienting after raw rooted substitution equals quotient substitution. -/
theorem mk_act {Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : PrefixedDecoratedTelescope S bd Γ) :
    mk (PrefixedDecoratedTelescope.act σ Ξ) =
      act (fun _ _ x => QExpr.mk E (σ x)) (mk Ξ) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Quotient.sound
    apply DecorationEq.symm
    apply PrefixedDecoratedTelescope.act_related
    · intro Λ υ x
      apply QExpr.representative_related_raw
      rfl
    · apply DecorationEq.refl

/-- The raw-to-quotient map as a natural transformation of rooted telescope
modules along the quotient Kleisli functor. -/
def quotientNat :
    PrefixedDTel S bd ⟶
      E.quotientKleisliFunctor ⋙ QDTelModule E bd where
  app _ := ↾mk
  naturality {Γ Δ} σ := by
    apply ConcreteCategory.hom_ext
    intro Ξ
    exact mk_act σ Ξ

end

end QDTel

end Equations
