import HigherRankSyntax.Typing.DecorationModule
import HigherRankSyntax.RelativeMonad.ArityModuleTensor

/-!
# Decorated telescopes as an internal monoid

The functor `DTel C` remembers how raw classifier expressions change under
substitution.  This file adds the algebra of telescope formation.  There is an
empty decorated telescope, and two consecutive decorated telescopes concatenate
dependently: the second is already decorated over the base extended by the raw
shape of the first.

These operations are precisely a unit and multiplication for the
context-extension tensor on `ArityMod (SyntaxMonad C)`.  Their unit and
associativity laws therefore package decorated telescopes as the internal monoid
`DTelMon C`.  For the running telescope `A : Type, x : A`, multiplication joins
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
             repeat apply HEq.trans (Boundary.cast_heq _ _)
             apply HEq.symm
             repeat apply HEq.trans (Boundary.cast_heq _ _)
             exact HEq.rfl))

namespace Decoration



private abbrev PackedPath (Δ Λ : C.Arity) :=
  Σ Φ, SlotPath (C := C) Δ Φ Λ

private def boundarySite {Ω Δ Λ : C.Arity}
    (D : Decoration Ω Δ) (p : PackedPath Δ Λ) :
    Σ Φ, Boundary (Ω ⋈ Φ ⋈ Λ) :=
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
    (site : Σ Λ, Boundary (F Λ)) (target : C.Arity)
    (h : site.1 = target) : Boundary (F target) :=
  Boundary.cast (congrArg F h) site.2

private theorem boundaryFromSite_congr (F : C.Arity → C.Arity)
    {site targetSite : Σ Λ, Boundary (F Λ)} {target : C.Arity}
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
        (Σ Λ : C.Arity, Boundary (Ω ⋈ Λ ⋈ α))
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
        (Σ Λ : C.Arity, Boundary (Ω ⋈ (Λ ⋈ _) ⋈ α))
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
      Boundary.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (C.before_inl x).symm)
        (D (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Boundary (Ω ⋈ Λ ⋈ α))
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
      Boundary.cast
        (congrArg (fun Λ => Ω ⋈ Λ ⋈ α) (C.before_inr x).symm)
        (E (.here x)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Boundary (Ω ⋈ Λ ⋈ α))
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
      Boundary.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (C.before_inl x).symm)
        (D (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Boundary (Ω ⋈ (Λ ⋈ Φ) ⋈ α))
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
      Boundary.cast
        (congrArg (fun Λ => Ω ⋈ (Λ ⋈ Φ) ⋈ α) (C.before_inr x).symm)
        (E (.nested x p)) := by
  simp only [concatenate]
  let site := C.copair Γ Δ
    (Σ Λ : C.Arity, Boundary (Ω ⋈ (Λ ⋈ Φ) ⋈ α))
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
        exact Boundary.act_cast_local σ
          (C.before_inl (Δ := Ξ) y).symm (D (.here y))
      · rw [concatenate_here_inr, concatenate_here_inr]
        exact Boundary.act_cast_local σ
          (C.before_inr (Γ := Ω) y).symm (E (.here y))
  | nested x p =>
      simp only [substitute]
      rcases C.cover Ω Ξ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_nested_inl, concatenate_nested_inl]
        exact Boundary.act_cast_local σ
          (congrArg (fun Θ => Θ ⋈ _) (C.before_inl (Δ := Ξ) y).symm)
          (D (.nested y p))
      · rw [concatenate_nested_inr, concatenate_nested_inr]
        exact Boundary.act_cast_local σ
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

namespace DecoratedTelescope

variable {Ω : C.Arity}

/-- Transport a decorated telescope along an equality of external bases. -/
def castBase {Γ Δ : C.Arity} (h : Γ = Δ) :
    DecoratedTelescope Γ → DecoratedTelescope Δ :=
  h ▸ fun Ξ => Ξ

/-- The empty decorated telescope. -/
def empty (Ω : C.Arity) :
    DecoratedTelescope Ω where
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
def concatenate (Γ : DecoratedTelescope Ω)
    (Δ : DecoratedTelescope (Ω ⋈ Γ.arity)) :
    DecoratedTelescope Ω where
  arity := Γ.arity ⋈ Δ.arity
  decoration := Decoration.concatenate Γ.decoration Δ.decoration

theorem substitute_concatenate {S Γ Δ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ))
    (Ξ : DecoratedTelescope (S ⋈ Γ ⋈ Φ))
    (Ω : DecoratedTelescope (S ⋈ Γ ⋈ Φ ⋈ Ξ.arity)) :
    substitute σ (concatenate Ξ Ω) =
      concatenate (substitute σ Ξ)
        (substitute (Φ := Φ ⋈ Ξ.arity) σ Ω) := by
  cases Ξ
  cases Ω
  simp [substitute, concatenate, Decoration.substitute_concatenate]

theorem act_concatenate {Γ Δ : C.Arity} (σ : Subst Γ Δ)
    (Ξ : DecoratedTelescope Γ)
    (Ω : DecoratedTelescope (Γ ⋈ Ξ.arity)) :
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

theorem concatenate_empty_left (Δ : DecoratedTelescope Ω) :
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

theorem concatenate_empty_right (Γ : DecoratedTelescope Ω) :
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

theorem concatenate_assoc (Γ : DecoratedTelescope Ω)
    (Δ : DecoratedTelescope (Ω ⋈ Γ.arity))
    (Ξ : DecoratedTelescope ((Ω ⋈ Γ.arity) ⋈ Δ.arity)) :
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
            exact eq_of_heq (Boundary.cast_congr_heq _ _
              (Boundary.cast_congr_heq _ _ HEq.rfl))
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

end DecoratedTelescope

open MonoidalCategory

namespace ArityMod

private def dtelShape (C : Carrier A) :
    DTel C ⟶ arityConst (SyntaxMonad C) where
  app _ := ↾DecoratedTelescope.arity
  naturality := by
    intros
    rfl

/-- Decorated telescopes, equipped with their substitution-invariant raw
shape, as an arity-shaped module over raw syntax. -/
def DTelArityMod (C : Carrier A) : ArityMod (SyntaxMonad C) := Over.mk (dtelShape C)

@[simp]
theorem DTelArityMod_module : module (DTelArityMod C) = DTel C := rfl

@[simp]
theorem DTelArityMod_shape {Ω : C.Arity}
    (Γ : DecoratedTelescope Ω) :
    shape (DTelArityMod C) Γ = Γ.arity := rfl

private def dtelUnitNat (C : Carrier A) :
    module (tensorUnit (C := C) (T := SyntaxMonad C)) ⟶
      module (DTelArityMod C) where
  app Ω := ↾fun _ => DecoratedTelescope.empty Ω
  naturality {Ω Ξ} σ := by
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    simp only [ConcreteCategory.comp_apply]
    change DecoratedTelescope.empty Ξ =
      DecoratedTelescope.act σ (DecoratedTelescope.empty Ω)
    exact (DecoratedTelescope.act_empty σ).symm

/-- The empty decorated telescope as a shape-preserving morphism. -/
def DTelOne (C : Carrier A) :
    tensorUnit (C := C) (T := SyntaxMonad C) ⟶ DTelArityMod C :=
  Over.homMk (dtelUnitNat C) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl)

private def dtelMulNat (C : Carrier A) :
    module (tensorObj (DTelArityMod C) (DTelArityMod C)) ⟶
      module (DTelArityMod C) where
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
def DTelMul (C : Carrier A) :
    tensorObj (DTelArityMod C) (DTelArityMod C) ⟶ DTelArityMod C :=
  Over.homMk (dtelMulNat C) (by
    apply NatTrans.ext
    funext Ω
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨Γ, Δ⟩
    rfl)

private theorem dtel_one_mul (C : Carrier A) :
    tensorMap (DTelOne C) (𝟙 (DTelArityMod C)) ≫ DTelMul C =
      (tensorLeftUnitor (DTelArityMod C)).hom := by
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

private theorem dtel_mul_one (C : Carrier A) :
    tensorMap (𝟙 (DTelArityMod C)) (DTelOne C) ≫ DTelMul C =
      (tensorRightUnitor (DTelArityMod C)).hom := by
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

private theorem dtel_mul_assoc (C : Carrier A) :
    tensorMap (DTelMul C) (𝟙 (DTelArityMod C)) ≫ DTelMul C =
      (tensorAssociator (DTelArityMod C) (DTelArityMod C)
          (DTelArityMod C)).hom ≫
        tensorMap (𝟙 (DTelArityMod C)) (DTelMul C) ≫ DTelMul C := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext Ω
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨⟨Γ, Δ⟩, Ξ⟩
  simp [DTelMul, dtelMulNat, tensorMap, tensorAssociator]
  apply DecoratedTelescope.concatenate_assoc

instance : MonObj (DTelArityMod C) where
  one := DTelOne C
  mul := DTelMul C
  one_mul := dtel_one_mul C
  mul_one := dtel_mul_one C
  mul_assoc := dtel_mul_assoc C

/-- Decorated telescopes form a monoid object in the monoidal category of
arity-shaped raw-syntax modules. -/
def DTelMon (C : Carrier A) : CategoryTheory.Mon (ArityMod (SyntaxMonad C)) :=
  CategoryTheory.Mon.mk (DTelArityMod C)

@[simp]
theorem DTelMon_one :
    MonObj.one (X := (DTelMon C).X) = DTelOne C := rfl

@[simp]
theorem DTelMon_mul :
    MonObj.mul (X := (DTelMon C).X) = DTelMul C := rfl

end ArityMod
