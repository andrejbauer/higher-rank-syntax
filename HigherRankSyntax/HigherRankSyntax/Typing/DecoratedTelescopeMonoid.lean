import HigherRankSyntax.Typing.DecorationModule
import HigherRankSyntax.RelativeMonad.ArityModuleTensor

/-!
# Decorated telescopes as an internal monoid

The functor `dTelModule C` remembers how raw classifier expressions change under
substitution.  This file adds the algebra of telescope formation.  There is an
empty decorated telescope, and two consecutive decorated telescopes concatenate
dependently: the second is already decorated over the base extended by the raw
shape of the first.

These operations are precisely a unit and multiplication for the
context-extension tensor on `ArityMod (SyntaxMonad C)`.  Their unit and
associativity laws therefore package decorated telescopes as the internal monoid
`dTelMon C`.  For the running telescope `A : Type, x : A`, multiplication joins
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



/-- Close an equality between iterated transports of one boundary.  The
transports need not agree in number, and their intermediate arities need only be
definitionally equal, so `cast_comp` does not apply. -/
macro "transport_ext" : tactic =>
  `(tactic| (apply eq_of_heq
             repeat apply HEq.trans (Bd.cast_heq _ _)
             apply HEq.symm
             repeat apply HEq.trans (Bd.cast_heq _ _)
             exact HEq.rfl))

namespace Decoration



private abbrev PackedPath (Δ Λ : C.Arity) :=
  Σ Φ, SlotPath (C := C) Δ Φ Λ

private def boundarySite {Ω Δ Λ : C.Arity}
    (D : Decoration Ω Δ) (p : PackedPath Δ Λ) :
    Σ Φ, Bd (Ω ⋈ Φ ⋈ Λ) :=
  ⟨p.1, D p.2⟩

/-- The unique decoration of the empty arity. -/
def empty (Ω : C.Arity) : Decoration Ω 1 :=
  fun ⦃_⦄ ⦃_⦄ p => False.elim (SlotPath.unit_elim p)

theorem substitute_empty {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    substitute (Φ := Φ) σ (empty (S ⋈ Γ ⋈ Φ)) =
      empty (S ⋈ Δ ⋈ Φ) := by
  funext Ω α p
  exact False.elim (SlotPath.unit_elim p)

private def boundaryFromSite (F : C.Arity → C.Arity)
    (site : Σ Λ, Bd (F Λ)) (target : C.Arity)
    (h : site.1 = target) : Bd (F target) :=
  Bd.cast (congrArg F h) site.2

private theorem boundaryFromSite_congr (F : C.Arity → C.Arity)
    {site targetSite : Σ Λ, Bd (F Λ)} {target : C.Arity}
    (hsite : site = targetSite) (h : site.1 = target)
    (k : targetSite.1 = target) :
      boundaryFromSite F site target h =
      boundaryFromSite F targetSite target k := by
  subst targetSite
  have hk : h = k := Subsingleton.elim _ _
  subst k
  rfl

/-- Concatenate a decoration over `Ω` with one over its extension. -/
def concatenate {Ω Γ Δ : C.Arity}
    (D : Decoration Ω Γ) (E : Decoration (Ω ⋈ Γ) Δ) :
    Decoration Ω (Γ ⋈ Δ)
  | _, α, .here x => by
      let site := C.copair Γ Δ
        (Σ Λ : C.Arity, Bd (Ω ⋈ Λ ⋈ α))
        (fun y => ⟨C.before y, D (.here y)⟩)
        (fun y => ⟨Γ ⋈ C.before y, E (.here y)⟩) x
      have hsite : site.1 = C.before x := by
        rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · simp [site, Carrier.inl]
          exact (C.before_inl y).symm
        · simp [site, Carrier.inr]
          exact (C.before_inr y).symm
      exact boundaryFromSite (fun Λ => Ω ⋈ Λ ⋈ α) site (C.before x) hsite
  | _, α, .nested x p => by
      let site := C.copair Γ Δ
        (Σ Λ : C.Arity, Bd (Ω ⋈ (Λ ⋈ _) ⋈ α))
        (fun y => ⟨C.before y, D (.nested y p)⟩)
        (fun y => ⟨Γ ⋈ C.before y, E (.nested y p)⟩) x
      have hsite : site.1 = C.before x := by
        rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · simp [site, Carrier.inl]
          exact (C.before_inl y).symm
        · simp [site, Carrier.inr]
          exact (C.before_inr y).symm
      exact boundaryFromSite (fun Λ => Ω ⋈ (Λ ⋈ _) ⋈ α)
        site (C.before x) hsite

theorem concatenate_here_inl {Ω Γ Δ α : C.Arity} 
    (D : Decoration Ω Γ) (E : Decoration (Ω ⋈ Γ) Δ)
    (x : Γ ∋ α) :
    concatenate D E (.here (C.inl x : Γ ⋈ Δ ∋ α)) =
      Bd.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (C.before_inl x).symm)
        (D (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Bd (Ω ⋈ Λ ⋈ α))
    (fun y => ⟨C.before y, D (.here y)⟩)
    (fun y => ⟨Γ ⋈ C.before y, E (.here y)⟩) (C.inl x)
  have hsite : site = ⟨C.before x, D (.here x)⟩ :=
    C.copair_apply_inl Γ Δ _ _ _ x
  exact boundaryFromSite_congr (fun Λ => Ω ⋈ Λ ⋈ α) hsite _
    (C.before_inl x).symm

theorem concatenate_here_inr {Ω Γ Δ α : C.Arity} 
    (D : Decoration Ω Γ) (E : Decoration (Ω ⋈ Γ) Δ)
    (x : Δ ∋ α) :
    concatenate D E (.here (C.inr x : Γ ⋈ Δ ∋ α)) =
      Bd.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (C.before_inr x).symm)
        (E (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Bd (Ω ⋈ Λ ⋈ α))
    (fun y => ⟨C.before y, D (.here y)⟩)
    (fun y => ⟨Γ ⋈ C.before y, E (.here y)⟩) (C.inr x)
  have hsite : site = ⟨Γ ⋈ C.before x, E (.here x)⟩ :=
    C.copair_apply_inr Γ Δ _ _ _ x
  exact boundaryFromSite_congr (fun Λ => Ω ⋈ Λ ⋈ α) hsite _
    (C.before_inr x).symm

theorem concatenate_nested_inl {Ω Γ Δ α β Φ : C.Arity} 
    (D : Decoration Ω Γ) (E : Decoration (Ω ⋈ Γ) Δ)
    (x : Γ ∋ β) (p : SlotPath β Φ α) :
    concatenate D E (.nested (C.inl x : Γ ⋈ Δ ∋ β) p) =
      Bd.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (C.before_inl x).symm)
        (D (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Bd (Ω ⋈ (Λ ⋈ Φ) ⋈ α))
    (fun y => ⟨C.before y, D (.nested y p)⟩)
    (fun y => ⟨Γ ⋈ C.before y, E (.nested y p)⟩) (C.inl x)
  have hsite : site = ⟨C.before x, D (.nested x p)⟩ :=
    C.copair_apply_inl Γ Δ _ _ _ x
  exact boundaryFromSite_congr (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) hsite _
    (C.before_inl x).symm

theorem concatenate_nested_inr {Ω Γ Δ α β Φ : C.Arity} 
    (D : Decoration Ω Γ) (E : Decoration (Ω ⋈ Γ) Δ)
    (x : Δ ∋ β) (p : SlotPath β Φ α) :
    concatenate D E (.nested (C.inr x : Γ ⋈ Δ ∋ β) p) =
      Bd.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (C.before_inr x).symm)
        (E (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Bd (Ω ⋈ (Λ ⋈ Φ) ⋈ α))
    (fun y => ⟨C.before y, D (.nested y p)⟩)
    (fun y => ⟨Γ ⋈ C.before y, E (.nested y p)⟩) (C.inr x)
  have hsite : site = ⟨Γ ⋈ C.before x, E (.nested x p)⟩ :=
    C.copair_apply_inr Γ Δ _ _ _ x
  exact boundaryFromSite_congr (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) hsite _
    (C.before_inr x).symm

theorem substitute_concatenate {S Γ Δ Φ Ω Ξ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (D : Decoration (S ⋈ Γ ⋈ Φ) Ω)
    (E : Decoration (S ⋈ Γ ⋈ Φ ⋈ Ω) Ξ) :
    substitute σ (concatenate D E) =
      concatenate (substitute σ D) (substitute (Φ := Φ ⋈ Ω) σ E) := by
  funext Λ α p
  cases p with
  | here x =>
      simp only [substitute]
      rcases C.cover Ω Ξ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_here_inl, concatenate_here_inl]
        exact Bd.act_cast_local σ
          (C.before_inl (Δ := Ξ) y).symm (D (.here y))
      · rw [concatenate_here_inr, concatenate_here_inr]
        exact Bd.act_cast_local σ
          (C.before_inr (Γ := Ω) y).symm (E (.here y))
  | nested x p =>
      simp only [substitute]
      rcases C.cover Ω Ξ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_nested_inl, concatenate_nested_inl]
        exact Bd.act_cast_local σ
          (congrArg (fun Θ => Θ ⋈ _) (C.before_inl (Δ := Ξ) y).symm)
          (D (.nested y p))
      · rw [concatenate_nested_inr, concatenate_nested_inr]
        exact Bd.act_cast_local σ
          (congrArg (fun Θ => Θ ⋈ _) (C.before_inr (Γ := Ω) y).symm)
          (E (.nested y p))

theorem act_concatenate {Γ Δ Ω Ξ : C.Arity} (σ : Subst Γ Δ)
    (D : Decoration Γ Ω) (E : Decoration (Γ ⋈ Ω) Ξ) :
    act σ (concatenate D E) =
      concatenate (act σ D) (act (Subst.lift σ Ω) E) := by
  rw [Decoration.act_lift]
  unfold act
  apply substitute_concatenate

end Decoration

namespace dTel

variable {Ω : C.Arity}

/-- Transport a decorated telescope along an equality of external bases. -/
def castBase {Γ Δ : C.Arity} (h : Γ = Δ) :
    dTel Γ → dTel Δ :=
  h ▸ fun Ξ => Ξ

/-- The empty decorated telescope. -/
def empty (Ω : C.Arity) :
    dTel Ω where
  arity := 1
  decoration := Decoration.empty Ω

theorem substitute_empty {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    substitute (Φ := Φ) σ (empty (S ⋈ Γ ⋈ Φ)) =
      empty (S ⋈ Δ ⋈ Φ) := by
  simp [substitute, empty, Decoration.substitute_empty]

theorem act_empty {Γ Δ : C.Arity} (σ : Subst Γ Δ) :
    act σ (empty Γ) = empty Δ := by
  apply substitute_empty

/-- Concatenation of decorated telescopes. -/
def concatenate (Γ : dTel Ω)
    (Δ : dTel (Ω ⋈ Γ.arity)) :
    dTel Ω where
  arity := Γ.arity ⋈ Δ.arity
  decoration := Decoration.concatenate Γ.decoration Δ.decoration

/-- Extend an ambient by a telescope over it. -/
def _root_.Ambient.extend (Ξ : Ambient C) (Θ : dTel Ξ.arity) : Ambient C :=
  concatenate Ξ Θ

@[simp] theorem _root_.Ambient.arity_extend (Ξ : Ambient C) (Θ : dTel Ξ.arity) :
  (Ξ.extend Θ).arity = Ξ.arity ⋈ Θ.arity := rfl

theorem substitute_concatenate {S Γ Δ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (Ξ : dTel (S ⋈ Γ ⋈ Φ))
    (Ω : dTel (S ⋈ Γ ⋈ Φ ⋈ Ξ.arity)) :
    substitute σ (concatenate Ξ Ω) =
      concatenate (substitute σ Ξ)
        (substitute (Φ := Φ ⋈ Ξ.arity) σ Ω) := by
  cases Ξ
  cases Ω
  simp [substitute, concatenate, Decoration.substitute_concatenate]

theorem act_concatenate {Γ Δ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : dTel Γ)
    (Ω : dTel (Γ ⋈ Ξ.arity)) :
    act σ (concatenate Ξ Ω) =
      concatenate (act σ Ξ) (act (Subst.lift σ Ξ.arity) Ω) := by
  rcases Ξ with ⟨Λ, D⟩
  rcases Ω with ⟨Θ, E⟩
  unfold act concatenate
  rw [dTel.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    apply Decoration.act_concatenate

theorem concatenate_empty_left (Δ : dTel Ω) :
    concatenate (empty Ω) (castBase (mul_one Ω).symm Δ) = Δ := by
  rcases Δ with ⟨Γ, D⟩
  simp [concatenate, empty, castBase]
  apply heq_of_eq
  funext Φ Λ p
  cases p with
  | here x =>
      rcases C.cover 1 Γ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact False.elim (C.unit_is_empty y)
      · rw [hy, Decoration.concatenate_here_inr]
        have hpath := congrArg
          (fun z : Γ ∋ Λ =>
            (⟨C.before z, SlotPath.here z⟩ :
              Decoration.PackedPath Γ Λ))
          (C.unit_left Γ y)
        have hsite := congrArg (Decoration.boundarySite D) hpath
        exact Decoration.boundaryFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (C.before_inr (Γ := 1) y).symm rfl
  | nested x p =>
      rcases C.cover 1 Γ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact False.elim (C.unit_is_empty y)
      · rw [hy, Decoration.concatenate_nested_inr]
        have hpath := congrArg
          (fun z =>
            (⟨C.before z ⋈ _, SlotPath.nested z p⟩ :
              Decoration.PackedPath Γ Λ))
          (C.unit_left Γ y)
        have hsite := congrArg (Decoration.boundarySite D) hpath
        exact Decoration.boundaryFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (congrArg (fun Φ => Φ ⋈ _)
            (C.before_inr (Γ := 1) y).symm) rfl

theorem concatenate_empty_right (Γ : dTel Ω) :
    concatenate Γ (empty (Ω ⋈ Γ.arity)) = Γ := by
  rcases Γ with ⟨Δ, D⟩
  simp [concatenate, empty]
  apply heq_of_eq
  funext Φ Λ p
  cases p with
  | here x =>
      rcases C.cover Δ 1 x with ⟨y, hy⟩ | ⟨y, hy⟩
      · rw [hy, Decoration.concatenate_here_inl]
        have hpath := congrArg
          (fun z : Δ ∋ Λ =>
            (⟨C.before z, SlotPath.here z⟩ :
              Decoration.PackedPath Δ Λ))
          (C.unit_right Δ y)
        have hsite := congrArg (Decoration.boundarySite D) hpath
        exact Decoration.boundaryFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (C.before_inl (Δ := 1) y).symm rfl
      · exact False.elim (C.unit_is_empty y)
  | nested x p =>
      rcases C.cover Δ 1 x with ⟨y, hy⟩ | ⟨y, hy⟩
      · rw [hy, Decoration.concatenate_nested_inl]
        have hpath := congrArg
          (fun z =>
            (⟨C.before z ⋈ _, SlotPath.nested z p⟩ :
              Decoration.PackedPath Δ Λ))
          (C.unit_right Δ y)
        have hsite := congrArg (Decoration.boundarySite D) hpath
        exact Decoration.boundaryFromSite_congr
          (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite.symm
          (congrArg (fun Φ => Φ ⋈ _)
            (C.before_inl (Δ := 1) y).symm) rfl
      · exact False.elim (C.unit_is_empty y)

theorem concatenate_assoc (Γ : dTel Ω)
    (Δ : dTel (Ω ⋈ Γ.arity))
    (Ξ : dTel ((Ω ⋈ Γ.arity) ⋈ Δ.arity)) :
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
    funext Φ Λ p
    cases p with
    | here x =>
        rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨z, hx⟩ | ⟨z, hx⟩
        · rcases C.cover Γ Δ z with ⟨y, hz⟩ | ⟨y, hz⟩
          · rw [hx, hz, Decoration.concatenate_here_inl,
              Decoration.concatenate_here_inl]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inl_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋ Λ =>
                (⟨C.before w, SlotPath.here w⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
            have hsite := congrArg (Decoration.boundarySite G) hpath
            have hvalue := Decoration.boundaryFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg C.before hslot) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.boundaryFromSite,
              Decoration.boundarySite, G]
            rw [Decoration.concatenate_here_inl]
            exact eq_of_heq (Bd.cast_congr_heq _ _
              (Bd.cast_congr_heq _ _ HEq.rfl))
          · rw [hx, hz, Decoration.concatenate_here_inl,
              Decoration.concatenate_here_inr]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inr_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋ Λ =>
                (⟨C.before w, SlotPath.here w⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
            have hsite := congrArg (Decoration.boundarySite G) hpath
            have hvalue := Decoration.boundaryFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg C.before hslot) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.boundaryFromSite,
              Decoration.boundarySite, G]
            rw [Decoration.concatenate_here_inr,
              Decoration.concatenate_here_inl]
            transport_ext
        · rw [hx, Decoration.concatenate_here_inr]
          let G := Decoration.concatenate D (Decoration.concatenate E F)
          have hslot := C.inr_inr Γ Δ Ξ z
          have hpath := congrArg
            (fun w : Γ ⋈ (Δ ⋈ Ξ) ∋ Λ =>
              (⟨C.before w, SlotPath.here w⟩ :
                Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
          have hsite := congrArg (Decoration.boundarySite G) hpath
          have hvalue := Decoration.boundaryFromSite_congr
            (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
            (congrArg C.before hslot) rfl
          apply Eq.trans ?_ hvalue
          simp only [Decoration.boundaryFromSite,
            Decoration.boundarySite, G]
          rw [Decoration.concatenate_here_inr,
            Decoration.concatenate_here_inr]
          transport_ext
    | nested x p =>
        rcases C.cover (Γ ⋈ Δ) Ξ x with ⟨z, hx⟩ | ⟨z, hx⟩
        · rcases C.cover Γ Δ z with ⟨y, hz⟩ | ⟨y, hz⟩
          · rw [hx, hz, Decoration.concatenate_nested_inl,
              Decoration.concatenate_nested_inl]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inl_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w =>
                (⟨C.before w ⋈ _, SlotPath.nested w p⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
            have hsite := congrArg (Decoration.boundarySite G) hpath
            have hvalue := Decoration.boundaryFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg (fun Φ => Φ ⋈ _)
                (congrArg C.before hslot)) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.boundaryFromSite,
              Decoration.boundarySite, G]
            rw [Decoration.concatenate_nested_inl]
            transport_ext
          · rw [hx, hz, Decoration.concatenate_nested_inl,
              Decoration.concatenate_nested_inr]
            let G := Decoration.concatenate D (Decoration.concatenate E F)
            have hslot := C.inr_inl Γ Δ Ξ y
            have hpath := congrArg
              (fun w =>
                (⟨C.before w ⋈ _, SlotPath.nested w p⟩ :
                  Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
            have hsite := congrArg (Decoration.boundarySite G) hpath
            have hvalue := Decoration.boundaryFromSite_congr
              (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
              (congrArg (fun Φ => Φ ⋈ _)
                (congrArg C.before hslot)) rfl
            apply Eq.trans ?_ hvalue
            simp only [Decoration.boundaryFromSite,
              Decoration.boundarySite, G]
            rw [Decoration.concatenate_nested_inr,
              Decoration.concatenate_nested_inl]
            transport_ext
        · rw [hx, Decoration.concatenate_nested_inr]
          let G := Decoration.concatenate D (Decoration.concatenate E F)
          have hslot := C.inr_inr Γ Δ Ξ z
          have hpath := congrArg
            (fun w =>
              (⟨C.before w ⋈ _, SlotPath.nested w p⟩ :
                Decoration.PackedPath (Γ ⋈ (Δ ⋈ Ξ)) Λ)) hslot
          have hsite := congrArg (Decoration.boundarySite G) hpath
          have hvalue := Decoration.boundaryFromSite_congr
            (fun Φ => Ω ⋈ Φ ⋈ Λ) hsite
            (congrArg (fun Φ => Φ ⋈ _)
              (congrArg C.before hslot)) rfl
          apply Eq.trans ?_ hvalue
          simp only [Decoration.boundaryFromSite,
            Decoration.boundarySite, G]
          rw [Decoration.concatenate_nested_inr,
            Decoration.concatenate_nested_inr]
          transport_ext

end dTel

open MonoidalCategory

namespace ArityMod

private def dTelShape (C : Carrier A) :
    dTelModule C ⟶ arityConst (SyntaxMonad C) where
  app _ := ↾dTel.arity
  naturality := by
    intros
    rfl

/-- Decorated telescopes, equipped with their substitution-invariant raw
shape, as an arity-shaped module over raw syntax. -/
def dTelArityMod (C : Carrier A) : ArityMod (SyntaxMonad C) := Over.mk (dTelShape C)

@[simp]
theorem DTelArityMod_module : module (dTelArityMod C) = dTelModule C := rfl

@[simp]
theorem DTelArityMod_shape {Ω : C.Arity}
    (Γ : dTel Ω) :
    shape (dTelArityMod C) Γ = Γ.arity := rfl

private def dTelUnitNat (C : Carrier A) :
    module (tensorUnit (C := C) (T := SyntaxMonad C)) ⟶
      module (dTelArityMod C) where
  app Ω := ↾fun _ => dTel.empty Ω
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    simp only [ConcreteCategory.comp_apply]
    change dTel.empty Ξ =
      dTel.act σ (dTel.empty Ω)
    exact (dTel.act_empty σ).symm

/-- The empty decorated telescope as a shape-preserving morphism. -/
def dTelOne (C : Carrier A) :
    tensorUnit (C := C) (T := SyntaxMonad C) ⟶ dTelArityMod C :=
  Over.homMk (dTelUnitNat C) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

private def dTelMulNat (C : Carrier A) :
    module (tensorObj (dTelArityMod C) (dTelArityMod C)) ⟶
      module (dTelArityMod C) where
  app _ := ↾fun ⟨Γ, Δ⟩ => dTel.concatenate Γ Δ
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    simp only [ConcreteCategory.comp_apply]
    change
      dTel.concatenate
          (dTel.act σ Γ)
          (dTel.act (Subst.lift σ Γ.arity) Δ) =
        dTel.act σ
          (dTel.concatenate Γ Δ)
    exact (dTel.act_concatenate σ Γ Δ).symm

/-- Dependent concatenation as a shape-preserving morphism. -/
def dTelMul (C : Carrier A) :
    tensorObj (dTelArityMod C) (dTelArityMod C) ⟶ dTelArityMod C :=
  Over.homMk (dTelMulNat C) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    rfl)

private theorem dTel_one_mul (C : Carrier A) :
    tensorMap (dTelOne C) (𝟙 (dTelArityMod C)) ≫ dTelMul C =
      (tensorLeftUnitor (dTelArityMod C)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨u, Γ⟩
  cases u
  simp [dTelOne, dTelMul, dTelUnitNat, dTelMulNat, tensorMap,
    tensorLeftUnitor]
  exact dTel.concatenate_empty_left _

private theorem dTel_mul_one (C : Carrier A) :
    tensorMap (𝟙 (dTelArityMod C)) (dTelOne C) ≫ dTelMul C =
      (tensorRightUnitor (dTelArityMod C)).hom := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨Γ, u⟩
  cases u
  simp [dTelOne, dTelMul, dTelUnitNat, dTelMulNat, tensorMap,
    tensorRightUnitor]
  apply dTel.concatenate_empty_right

private theorem dTel_mul_assoc (C : Carrier A) :
    tensorMap (dTelMul C) (𝟙 (dTelArityMod C)) ≫ dTelMul C =
      (tensorAssociator (dTelArityMod C) (dTelArityMod C)
          (dTelArityMod C)).hom ≫
        tensorMap (𝟙 (dTelArityMod C)) (dTelMul C) ≫ dTelMul C := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
  simp [dTelMul, dTelMulNat, tensorMap, tensorAssociator]
  apply dTel.concatenate_assoc

instance : MonObj (dTelArityMod C) where
  one := dTelOne C
  mul := dTelMul C
  one_mul := dTel_one_mul C
  mul_one := dTel_mul_one C
  mul_assoc := dTel_mul_assoc C

/-- Decorated telescopes form a monoid object in the monoidal category of
arity-shaped raw-syntax modules. -/
def dTelMon (C : Carrier A) : CategoryTheory.Mon (ArityMod (SyntaxMonad C)) :=
  CategoryTheory.Mon.mk (dTelArityMod C)

@[simp]
theorem DTelMon_one :
    MonObj.one (X := (dTelMon C).X) = dTelOne C := rfl

@[simp]
theorem DTelMon_mul :
    MonObj.mul (X := (dTelMon C).X) = dTelMul C := rfl

end ArityMod
