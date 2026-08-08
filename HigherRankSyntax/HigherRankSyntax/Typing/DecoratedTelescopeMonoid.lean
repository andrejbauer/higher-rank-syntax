import HigherRankSyntax.Typing.DecorationModule
import HigherRankSyntax.Typing.TelescopeTensor

/-!
# Decorated telescopes as an internal monoid

The functor `DTel bd` remembers how raw classifier expressions change under
substitution.  This file adds the algebra of telescope formation.  There is an
empty decorated telescope, and two consecutive decorated telescopes concatenate
dependently: the second is already decorated over the base extended by the raw
shape of the first.

These operations are precisely a unit and multiplication for the
context-extension tensor on `ArityMod (SyntaxMonad C)`.  Their unit and
associativity laws therefore package decorated telescopes as the internal monoid
`DTelMon bd`.  For the running telescope `A : Type, x : A`, multiplication joins
the segment `A : Type` to the segment `x : A`; the tensor has already placed the
second segment over the base containing `A`, so its classifier may refer to that
earlier slot.  Rebracketing three segments changes only where we place the cuts,
not the resulting decorated telescope.

All classifiers here are still raw expressions.  The monoid records stable
dependent telescope structure, but contains no evidence that `A` is a type,
that `x` has type `A`, or that either expression is well formed.
-/

variable {A : Type} {C : Carrier A}

open CategoryTheory



namespace Decoration

variable [P : Precedence C] {bd : C.Ty → Option C.Ty}

private abbrev PackedPath (Δ Λ : C.Arity) (τ : C.Ty) :=
  Σ Φ, DecorationPath (C := C) Δ Φ Λ τ

private def classifierSite {Ω Δ Λ : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (p : PackedPath Δ Λ τ) :
    Σ Φ, ClassifierAt bd (Ω ⋈ Φ ⋈ Λ) τ :=
  ⟨p.1, D p.2⟩

private theorem path_empty {Φ α : C.Arity} {τ : C.Ty} :
    DecorationPath (C := C) 1 Φ α τ → False
  | .here x => C.unit_is_empty x
  | .nested x _ => C.unit_is_empty x

/-- The unique decoration of the empty arity. -/
def empty (bd : C.Ty → Option C.Ty) (Ω : C.Arity) : Decoration bd Ω 1 :=
  fun ⦃_⦄ ⦃_⦄ ⦃_⦄ p => False.elim (path_empty p)

theorem substitute_empty {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    substitute (Φ := Φ) σ (empty bd (S ⋈ Γ ⋈ Φ)) =
      empty bd (S ⋈ Δ ⋈ Φ) := by
  funext Ω α τ p
  exact False.elim (path_empty p)

private def classifierFromSite {τ : C.Ty} (F : C.Arity → C.Arity)
    (site : Σ Λ, ClassifierAt bd (F Λ) τ) (target : C.Arity)
    (h : site.1 = target) : ClassifierAt bd (F target) τ :=
  ClassifierAt.cast (congrArg F h) site.2

omit P in
private theorem classifierFromSite_congr {τ : C.Ty} (F : C.Arity → C.Arity)
    {site targetSite : Σ Λ, ClassifierAt bd (F Λ) τ} {target : C.Arity}
    (hsite : site = targetSite) (h : site.1 = target)
    (k : targetSite.1 = target) :
      classifierFromSite F site target h =
      classifierFromSite F targetSite target k := by
  subst targetSite
  have hk : h = k := Subsingleton.elim _ _
  subst k
  rfl

/-- Concatenate a decoration over `Ω` with one over its extension. -/
def concatenate {Ω Γ Δ : C.Arity}
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ) :
    Decoration bd Ω (Γ ⋈ Δ)
  | _, α, _, .here x => by
      let site := C.copair Γ Δ
        (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ Λ ⋈ α) _)
        (fun y => ⟨P.before y, D (.here y)⟩)
        (fun y => ⟨Γ ⋈ P.before y, E (.here y)⟩) x
      have hsite : site.1 = P.before x := by
        rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · simp [site, Carrier.inl]
          exact (P.before_inl y).symm
        · simp [site, Carrier.inr]
          exact (P.before_inr y).symm
      exact classifierFromSite (fun Λ => Ω ⋈ Λ ⋈ α) site (P.before x) hsite
  | _, α, _, .nested x p => by
      let site := C.copair Γ Δ
        (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ (Λ ⋈ _) ⋈ α) _)
        (fun y => ⟨P.before y, D (.nested y p)⟩)
        (fun y => ⟨Γ ⋈ P.before y, E (.nested y p)⟩) x
      have hsite : site.1 = P.before x := by
        rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · simp [site, Carrier.inl]
          exact (P.before_inl y).symm
        · simp [site, Carrier.inr]
          exact (P.before_inr y).symm
      exact classifierFromSite (fun Λ => Ω ⋈ (Λ ⋈ _) ⋈ α)
        site (P.before x) hsite

theorem concatenate_here_inl {Ω Γ Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ)
    (x : Γ ∋[τ] α) :
    concatenate D E (.here (C.inl x : Γ ⋈ Δ ∋[τ] α)) =
      ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (P.before_inl x).symm)
        (D (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ Λ ⋈ α) τ)
    (fun y => ⟨P.before y, D (.here y)⟩)
    (fun y => ⟨Γ ⋈ P.before y, E (.here y)⟩) (C.inl x)
  have hsite : site = ⟨P.before x, D (.here x)⟩ :=
    C.copair_apply_inl Γ Δ _ _ _ x
  exact classifierFromSite_congr (fun Λ => Ω ⋈ Λ ⋈ α) hsite _
    (P.before_inl x).symm

theorem concatenate_here_inr {Ω Γ Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ)
    (x : Δ ∋[τ] α) :
    concatenate D E (.here (C.inr x : Γ ⋈ Δ ∋[τ] α)) =
      ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (P.before_inr x).symm)
        (E (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ Λ ⋈ α) τ)
    (fun y => ⟨P.before y, D (.here y)⟩)
    (fun y => ⟨Γ ⋈ P.before y, E (.here y)⟩) (C.inr x)
  have hsite : site = ⟨Γ ⋈ P.before x, E (.here x)⟩ :=
    C.copair_apply_inr Γ Δ _ _ _ x
  exact classifierFromSite_congr (fun Λ => Ω ⋈ Λ ⋈ α) hsite _
    (P.before_inr x).symm

theorem concatenate_nested_inl {Ω Γ Δ α β Φ : C.Arity} {τ υ : C.Ty}
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ)
    (x : Γ ∋[υ] β) (p : DecorationPath β Φ α τ) :
    concatenate D E (.nested (C.inl x : Γ ⋈ Δ ∋[υ] β) p) =
      ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (P.before_inl x).symm)
        (D (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ (Λ ⋈ Φ) ⋈ α) τ)
    (fun y => ⟨P.before y, D (.nested y p)⟩)
    (fun y => ⟨Γ ⋈ P.before y, E (.nested y p)⟩) (C.inl x)
  have hsite : site = ⟨P.before x, D (.nested x p)⟩ :=
    C.copair_apply_inl Γ Δ _ _ _ x
  exact classifierFromSite_congr (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) hsite _
    (P.before_inl x).symm

theorem concatenate_nested_inr {Ω Γ Δ α β Φ : C.Arity} {τ υ : C.Ty}
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ)
    (x : Δ ∋[υ] β) (p : DecorationPath β Φ α τ) :
    concatenate D E (.nested (C.inr x : Γ ⋈ Δ ∋[υ] β) p) =
      ClassifierAt.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (P.before_inr x).symm)
        (E (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, ClassifierAt bd (Ω ⋈ (Λ ⋈ Φ) ⋈ α) τ)
    (fun y => ⟨P.before y, D (.nested y p)⟩)
    (fun y => ⟨Γ ⋈ P.before y, E (.nested y p)⟩) (C.inr x)
  have hsite : site = ⟨Γ ⋈ P.before x, E (.nested x p)⟩ :=
    C.copair_apply_inr Γ Δ _ _ _ x
  exact classifierFromSite_congr (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) hsite _
    (P.before_inr x).symm

theorem substitute_concatenate {S Γ Δ Φ Ω Ξ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (D : Decoration bd (S ⋈ Γ ⋈ Φ) Ω)
    (E : Decoration bd (S ⋈ Γ ⋈ Φ ⋈ Ω) Ξ) :
    substitute σ (concatenate D E) =
      concatenate (substitute σ D) (substitute (Φ := Φ ⋈ Ω) σ E) := by
  funext Λ α τ p
  cases p with
  | here x =>
      simp only [substitute]
      rcases C.cover Ω Ξ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_here_inl, concatenate_here_inl]
        exact ClassifierAt.substitute_cast_local σ
          (P.before_inl (Δ := Ξ) y).symm (D (.here y))
      · rw [concatenate_here_inr, concatenate_here_inr]
        exact ClassifierAt.substitute_cast_local σ
          (P.before_inr (Γ := Ω) y).symm (E (.here y))
  | nested x p =>
      simp only [substitute]
      rcases C.cover Ω Ξ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_nested_inl, concatenate_nested_inl]
        exact ClassifierAt.substitute_cast_local σ
          (congrArg (fun Θ => Θ ⋈ _) (P.before_inl (Δ := Ξ) y).symm)
          (D (.nested y p))
      · rw [concatenate_nested_inr, concatenate_nested_inr]
        exact ClassifierAt.substitute_cast_local σ
          (congrArg (fun Θ => Θ ⋈ _) (P.before_inr (Γ := Ω) y).symm)
          (E (.nested y p))

theorem act_concatenate {Γ Δ Ω Ξ : C.Arity} (σ : Subst Γ Δ)
    (D : Decoration bd Γ Ω) (E : Decoration bd (Γ ⋈ Ω) Ξ) :
    act σ (concatenate D E) =
      concatenate (act σ D) (act (Subst.lift σ Ω) E) := by
  rw [Decoration.act_lift]
  unfold act
  apply substitute_concatenate

end Decoration

namespace DecoratedTelescope

variable [P : Precedence C] {bd : C.Ty → Option C.Ty} {Ω : C.Arity}

/-- Transport a decorated telescope along an equality of external bases. -/
def castBase {Γ Δ : C.Arity} (h : Γ = Δ) :
    DecoratedTelescope bd Γ → DecoratedTelescope bd Δ :=
  h ▸ fun Ξ => Ξ

/-- The empty decorated telescope. -/
def empty (bd : C.Ty → Option C.Ty) (Ω : C.Arity) :
    DecoratedTelescope bd Ω where
  arity := 1
  decoration := Decoration.empty bd Ω

theorem substitute_empty {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    substitute (Φ := Φ) σ (empty bd (S ⋈ Γ ⋈ Φ)) =
      empty bd (S ⋈ Δ ⋈ Φ) := by
  simp [substitute, empty, Decoration.substitute_empty]

theorem act_empty {Γ Δ : C.Arity} (σ : Subst Γ Δ) :
    act σ (empty bd Γ) = empty bd Δ := by
  apply substitute_empty

/-- Concatenation of decorated telescopes. -/
def concatenate (Γ : DecoratedTelescope bd Ω)
    (Δ : DecoratedTelescope bd (Ω ⋈ Γ.arity)) :
    DecoratedTelescope bd Ω where
  arity := Γ.arity ⋈ Δ.arity
  decoration := Decoration.concatenate Γ.decoration Δ.decoration

theorem substitute_concatenate {S Γ Δ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (Ξ : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ))
    (Ω : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ ⋈ Ξ.arity)) :
    substitute σ (concatenate Ξ Ω) =
      concatenate (substitute σ Ξ)
        (substitute (Φ := Φ ⋈ Ξ.arity) σ Ω) := by
  cases Ξ
  cases Ω
  simp [substitute, concatenate, Decoration.substitute_concatenate]

theorem act_concatenate {Γ Δ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : DecoratedTelescope bd Γ)
    (Ω : DecoratedTelescope bd (Γ ⋈ Ξ.arity)) :
    act σ (concatenate Ξ Ω) =
      concatenate (act σ Ξ) (act (Subst.lift σ Ξ.arity) Ω) := by
  rcases Ξ with ⟨Λ, D⟩
  rcases Ω with ⟨Θ, E⟩
  unfold act concatenate
  rw [DecoratedTelescope.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    apply Decoration.act_concatenate

theorem concatenate_empty_left (Δ : DecoratedTelescope bd Ω) :
    concatenate (empty bd Ω) (castBase (mul_one Ω).symm Δ) = Δ := by
  rcases Δ with ⟨Γ, D⟩
  simp [concatenate, empty, castBase]
  apply heq_of_eq
  funext Φ Λ τ p
  cases p with
  | here x =>
      rcases C.cover 1 Γ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact False.elim (C.unit_is_empty y)
      · rw [hy, Decoration.concatenate_here_inr]
        have hpath := congrArg
          (fun z : Γ ∋[τ] Λ =>
            (⟨P.before z, DecorationPath.here z⟩ :
              Decoration.PackedPath Γ Λ τ))
          (C.unit_left Γ y)
        have hsite := congrArg (Decoration.classifierSite D) hpath
        exact Decoration.classifierFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (P.before_inr (Γ := 1) y).symm rfl
  | nested x p =>
      rcases C.cover 1 Γ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact False.elim (C.unit_is_empty y)
      · rw [hy, Decoration.concatenate_nested_inr]
        have hpath := congrArg
          (fun z =>
            (⟨P.before z ⋈ _, DecorationPath.nested z p⟩ :
              Decoration.PackedPath Γ Λ τ))
          (C.unit_left Γ y)
        have hsite := congrArg (Decoration.classifierSite D) hpath
        exact Decoration.classifierFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (congrArg (fun Φ => Φ ⋈ _)
            (P.before_inr (Γ := 1) y).symm) rfl

theorem concatenate_empty_right (Γ : DecoratedTelescope bd Ω) :
    concatenate Γ (empty bd (Ω ⋈ Γ.arity)) = Γ := by
  rcases Γ with ⟨Δ, D⟩
  simp [concatenate, empty]
  apply heq_of_eq
  funext Φ Λ τ p
  cases p with
  | here x =>
      rcases C.cover Δ 1 x with ⟨y, hy⟩ | ⟨y, hy⟩
      · rw [hy, Decoration.concatenate_here_inl]
        have hpath := congrArg
          (fun z : Δ ∋[τ] Λ =>
            (⟨P.before z, DecorationPath.here z⟩ :
              Decoration.PackedPath Δ Λ τ))
          (C.unit_right Δ y)
        have hsite := congrArg (Decoration.classifierSite D) hpath
        exact Decoration.classifierFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (P.before_inl (Δ := 1) y).symm rfl
      · exact False.elim (C.unit_is_empty y)
  | nested x p =>
      rcases C.cover Δ 1 x with ⟨y, hy⟩ | ⟨y, hy⟩
      · rw [hy, Decoration.concatenate_nested_inl]
        have hpath := congrArg
          (fun z =>
            (⟨P.before z ⋈ _, DecorationPath.nested z p⟩ :
              Decoration.PackedPath Δ Λ τ))
          (C.unit_right Δ y)
        have hsite := congrArg (Decoration.classifierSite D) hpath
        exact Decoration.classifierFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (congrArg (fun Φ => Φ ⋈ _)
            (P.before_inl (Δ := 1) y).symm) rfl
      · exact False.elim (C.unit_is_empty y)

theorem concatenate_assoc (Γ : DecoratedTelescope bd Ω)
    (Δ : DecoratedTelescope bd (Ω ⋈ Γ.arity))
    (Ξ : DecoratedTelescope bd ((Ω ⋈ Γ.arity) ⋈ Δ.arity)) :
    concatenate (concatenate Γ Δ)
        (castBase (mul_assoc Ω Γ.arity Δ.arity) Ξ) =
      concatenate Γ (concatenate Δ Ξ) := by
  rcases Γ with ⟨Γ, D⟩
  rcases Δ with ⟨Δ, E⟩
  rcases Ξ with ⟨Ξ, F⟩
  simp [concatenate, castBase]
  constructor
  · apply mul_assoc
  · apply heq_of_eq
    funext Φ Λ τ p
    cases p with
    | here x =>
        rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨z, hx⟩ | ⟨z, hx⟩
        · rcases C.cover Γ Δ z with ⟨y, hz⟩ | ⟨y, hz⟩
          · rw [hx, hz, Decoration.concatenate_here_inl,
              Decoration.concatenate_here_inl]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inl_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋[τ] Λ =>
                (⟨P.before w, DecorationPath.here w⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
            have hsite := congrArg (Decoration.classifierSite G) hpath
            have hvalue := Decoration.classifierFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg P.before hslot) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.classifierFromSite,
              Decoration.classifierSite, G]
            rw [Decoration.concatenate_here_inl]
            rw [ClassifierAt.cast_comp, ClassifierAt.cast_comp]
            apply ClassifierAt.cast_proof_irrel
          · rw [hx, hz, Decoration.concatenate_here_inl,
              Decoration.concatenate_here_inr]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inr_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋[τ] Λ =>
                (⟨P.before w, DecorationPath.here w⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
            have hsite := congrArg (Decoration.classifierSite G) hpath
            have hvalue := Decoration.classifierFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg P.before hslot) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.classifierFromSite,
              Decoration.classifierSite, G]
            rw [Decoration.concatenate_here_inr,
              Decoration.concatenate_here_inl]
            repeat rw [ClassifierAt.cast_comp]
            apply ClassifierAt.cast_eq_cast_comp
        · rw [hx, Decoration.concatenate_here_inr]
          let G := Decoration.concatenate D (Decoration.concatenate E F)
          have hslot := C.inr_inr Γ Δ Ξ z
          have hpath := congrArg
            (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋[τ] Λ =>
              (⟨P.before w, DecorationPath.here w⟩ :
                Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
          have hsite := congrArg (Decoration.classifierSite G) hpath
          have hvalue := Decoration.classifierFromSite_congr
            (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
            (congrArg P.before hslot) rfl
          apply Eq.trans ?_ hvalue
          simp only [Decoration.classifierFromSite,
            Decoration.classifierSite, G]
          rw [Decoration.concatenate_here_inr,
            Decoration.concatenate_here_inr]
          repeat rw [ClassifierAt.cast_comp]
          apply ClassifierAt.cast_eq_cast_comp
    | nested x p =>
        rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨z, hx⟩ | ⟨z, hx⟩
        · rcases C.cover Γ Δ z with ⟨y, hz⟩ | ⟨y, hz⟩
          · rw [hx, hz, Decoration.concatenate_nested_inl,
              Decoration.concatenate_nested_inl]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inl_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w =>
                (⟨P.before w ⋈ _, DecorationPath.nested w p⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
            have hsite := congrArg (Decoration.classifierSite G) hpath
            have hvalue := Decoration.classifierFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg (fun Φ => Φ ⋈ _)
                (congrArg P.before hslot)) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.classifierFromSite,
              Decoration.classifierSite, G]
            rw [Decoration.concatenate_nested_inl]
            repeat rw [ClassifierAt.cast_comp]
            apply ClassifierAt.cast_proof_irrel
          · rw [hx, hz, Decoration.concatenate_nested_inl,
              Decoration.concatenate_nested_inr]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inr_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w =>
                (⟨P.before w ⋈ _, DecorationPath.nested w p⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
            have hsite := congrArg (Decoration.classifierSite G) hpath
            have hvalue := Decoration.classifierFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg (fun Φ => Φ ⋈ _)
                (congrArg P.before hslot)) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.classifierFromSite,
              Decoration.classifierSite, G]
            rw [Decoration.concatenate_nested_inr,
              Decoration.concatenate_nested_inl]
            repeat rw [ClassifierAt.cast_comp]
            apply ClassifierAt.cast_eq_cast_comp
        · rw [hx, Decoration.concatenate_nested_inr]
          let G := Decoration.concatenate D (Decoration.concatenate E F)
          have hslot := C.inr_inr Γ Δ Ξ z
          have hpath := congrArg
            (fun w =>
              (⟨P.before w ⋈ _, DecorationPath.nested w p⟩ :
                Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ τ)) hslot
          have hsite := congrArg (Decoration.classifierSite G) hpath
          have hvalue := Decoration.classifierFromSite_congr
            (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
            (congrArg (fun Φ => Φ ⋈ _)
              (congrArg P.before hslot)) rfl
          apply Eq.trans ?_ hvalue
          simp only [Decoration.classifierFromSite,
            Decoration.classifierSite, G]
          rw [Decoration.concatenate_nested_inr,
            Decoration.concatenate_nested_inr]
          repeat rw [ClassifierAt.cast_comp]
          apply ClassifierAt.cast_eq_cast_comp

end DecoratedTelescope

open MonoidalCategory

namespace ArityMod

variable [Precedence C] (bd : C.Ty → Option C.Ty)

private def dtelShape :
    DTel (C := C) bd ⟶ arityConst (SyntaxMonad C) where
  app _ := ↾DecoratedTelescope.arity
  naturality := by
    intros
    rfl

/-- Decorated telescopes, equipped with their substitution-invariant raw
shape, as an arity-shaped module over raw syntax. -/
def DTelArityMod : ArityMod (SyntaxMonad C) := Over.mk (dtelShape bd)

@[simp]
theorem DTelArityMod_module : module (DTelArityMod bd) = DTel bd := rfl

@[simp]
theorem DTelArityMod_shape {Ω : C.Arity}
    (Γ : DecoratedTelescope bd Ω) :
    shape (DTelArityMod bd) Γ = Γ.arity := rfl

private def dtelUnitNat :
    module (tensorUnit (C := C) (T := SyntaxMonad C)) ⟶
      module (DTelArityMod bd) where
  app Ω := ↾fun _ => DecoratedTelescope.empty bd Ω
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    simp only [ConcreteCategory.comp_apply]
    change DecoratedTelescope.empty bd Ξ =
      DecoratedTelescope.act σ (DecoratedTelescope.empty bd Ω)
    exact (DecoratedTelescope.act_empty σ).symm

/-- The empty decorated telescope as a shape-preserving morphism. -/
def DTelOne :
    tensorUnit (C := C) (T := SyntaxMonad C) ⟶ DTelArityMod bd :=
  Over.homMk (dtelUnitNat bd) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

private def dtelMulNat :
    module (tensorObj (DTelArityMod bd) (DTelArityMod bd)) ⟶
      module (DTelArityMod bd) where
  app _ := ↾fun ⟨Γ, Δ⟩ => DecoratedTelescope.concatenate Γ Δ
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    simp only [ConcreteCategory.comp_apply]
    change
      DecoratedTelescope.concatenate
          (DecoratedTelescope.act σ Γ)
          (DecoratedTelescope.act (Subst.lift σ Γ.arity) Δ) =
        DecoratedTelescope.act σ
          (DecoratedTelescope.concatenate Γ Δ)
    exact (DecoratedTelescope.act_concatenate σ Γ Δ).symm

/-- Dependent concatenation as a shape-preserving morphism. -/
def DTelMul :
    tensorObj (DTelArityMod bd) (DTelArityMod bd) ⟶ DTelArityMod bd :=
  Over.homMk (dtelMulNat bd) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    rfl)

private theorem dtel_one_mul :
    tensorMap (DTelOne bd) (𝟙 (DTelArityMod bd)) ≫ DTelMul bd =
      (tensorLeftUnitor (DTelArityMod bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨u, Γ⟩
  cases u
  simp [DTelOne, DTelMul, dtelUnitNat, dtelMulNat, tensorMap,
    tensorLeftUnitor]
  exact DecoratedTelescope.concatenate_empty_left _

private theorem dtel_mul_one :
    tensorMap (𝟙 (DTelArityMod bd)) (DTelOne bd) ≫ DTelMul bd =
      (tensorRightUnitor (DTelArityMod bd)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, u⟩
  cases u
  simp [DTelOne, DTelMul, dtelUnitNat, dtelMulNat, tensorMap,
    tensorRightUnitor]
  apply DecoratedTelescope.concatenate_empty_right

private theorem dtel_mul_assoc :
    tensorMap (DTelMul bd) (𝟙 (DTelArityMod bd)) ≫ DTelMul bd =
      (tensorAssociator (DTelArityMod bd) (DTelArityMod bd)
          (DTelArityMod bd)).hom ≫
        tensorMap (𝟙 (DTelArityMod bd)) (DTelMul bd) ≫ DTelMul bd := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
  simp [DTelMul, dtelMulNat, tensorMap, tensorAssociator]
  apply DecoratedTelescope.concatenate_assoc

instance : MonObj (DTelArityMod bd) where
  one := DTelOne bd
  mul := DTelMul bd
  one_mul := dtel_one_mul bd
  mul_one := dtel_mul_one bd
  mul_assoc := dtel_mul_assoc bd

/-- Decorated telescopes form a monoid object in the monoidal category of
arity-shaped raw-syntax modules. -/
def DTelMon : CategoryTheory.Mon (ArityMod (SyntaxMonad C)) :=
  CategoryTheory.Mon.mk (DTelArityMod bd)

@[simp]
theorem DTelMon_one :
    MonObj.one (X := (DTelMon bd).X) = DTelOne bd := rfl

@[simp]
theorem DTelMon_mul :
    MonObj.mul (X := (DTelMon bd).X) = DTelMul bd := rfl

end ArityMod
