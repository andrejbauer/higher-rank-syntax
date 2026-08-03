import HigherRankSyntax.PrefixedSyntaxMonad

/-!
# Decorations of raw telescopes

A decoration records the dependency order of raw slots, recursively decorates
their binding arities, and attaches raw expression classifiers where requested
by a classifier policy.
-/

variable {A : Type} {C : Carrier A}

/-- A coherent choice of the part of an arity preceding each slot. -/
class Precedence (C : Carrier A) where
  before : {Δ α : C.Arity} → {τ : C.Ty} → Δ ∋[τ] α → C.Arity
  after : {Δ α : C.Arity} → {τ : C.Ty} → Δ ∋[τ] α → C.Arity
  factor : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → before x ⋈ after x = Δ
  localized : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → after x ∋[τ] α
  reinject : {Δ α : C.Arity} → {τ : C.Ty} →
    (x : Δ ∋[τ] α) → factor x ▸ C.inr (localized x) = x
  before_inl : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Γ ∋[τ] α) →
    before (C.inl x : Γ ⋈ Δ ∋[τ] α) = before x
  after_inl : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Γ ∋[τ] α) →
    after (C.inl x : Γ ⋈ Δ ∋[τ] α) = after x ⋈ Δ
  before_inr : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Δ ∋[τ] α) →
    before (C.inr x : Γ ⋈ Δ ∋[τ] α) = Γ ⋈ before x
  after_inr : {Γ Δ α : C.Arity} → {τ : C.Ty} → (x : Δ ∋[τ] α) →
    after (C.inr x : Γ ⋈ Δ ∋[τ] α) = after x

/-- The type of classifier data attached to a raw `τ`-slot over `Ω`.

The policy `bd` assigns a classifier class to each class that requires one.
If `bd τ = none`, the unique `PUnit` value records that a `τ`-slot has no
classifier; if `bd τ = some υ`, its classifier is a raw expression in
`Expr Ω υ`, where `Ω` is the current context.

For example, take classes `ty` and `tm`, with `bd ty = none` and
`bd tm = some ty`.  In the telescope `A : Type, x : A`, the `A`-slot carries
no classifier, while the `x`-slot carries the preceding type variable `A` as
an expression of class `ty`.  In a decoration, `Ω` contains exactly the
external base, preceding siblings, and local bound variables that the
classifier may mention.  No well-formedness judgment is imposed at this raw
data layer.
-/
def ClassifierAt (bd : C.Ty → Option C.Ty) (Ω : C.Arity) (τ : C.Ty) : Type :=
  match bd τ with
  | none => PUnit
  | some υ => Expr Ω υ

namespace ClassifierAt

variable {bd : C.Ty → Option C.Ty}

/-- Transport a classifier along an equality of raw contexts. -/
def cast {Γ Δ : C.Arity} (h : Γ = Δ) {τ : C.Ty} :
    ClassifierAt bd Γ τ → ClassifierAt bd Δ τ :=
  h ▸ fun a => a

private def renameAux {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
    (o : Option C.Ty) →
      (match o with | none => PUnit | some υ => Expr Γ υ) →
      (match o with | none => PUnit | some υ => Expr Δ υ)
  | none, _ => PUnit.unit
  | some _, a => Renaming.act ρ a

/-- Reindex a classifier along a renaming of its base. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) {τ : C.Ty}
    (a : ClassifierAt bd Γ τ) : ClassifierAt bd Δ τ :=
  renameAux ρ (bd τ) a

private theorem renameAux_id {Γ : C.Arity}
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some υ => Expr Γ υ) :
    renameAux (𝟙ʳ Γ) o a = a := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some υ => apply Renaming.act_id

theorem rename_id {Γ : C.Arity} {τ : C.Ty} (a : ClassifierAt bd Γ τ) :
    rename (𝟙ʳ Γ) a = a :=
  renameAux_id (bd τ) a

private theorem renameAux_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ)
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some υ => Expr Γ υ) :
    renameAux (σ ∘ʳ ρ) o a = renameAux σ o (renameAux ρ o a) := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some υ => apply Renaming.act_comp

theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ)
    {τ : C.Ty} (a : ClassifierAt bd Γ τ) :
    rename (σ ∘ʳ ρ) a = rename σ (rename ρ a) :=
  renameAux_comp ρ σ (bd τ) a

theorem rename_cast_local {Ω Ξ Λ Φ α : C.Arity} (ρ : Ω →ʳ Ξ)
    (h : Λ = Φ) {τ : C.Ty} (a : ClassifierAt bd (Ω ⋈ Λ ⋈ α) τ) :
    rename ((ρ ⇑ʳ Φ) ⇑ʳ α)
        (cast (congrArg (fun Δ => Ω ⋈ Δ ⋈ α) h) a) =
      cast (congrArg (fun Δ => Ξ ⋈ Δ ⋈ α) h)
        (rename ((ρ ⇑ʳ Λ) ⇑ʳ α) a) := by
  subst Φ
  rfl

private def substituteAux {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    (o : Option C.Ty) →
      (match o with | none => PUnit | some υ => Expr (S ⋈ Γ ⋈ Φ) υ) →
      (match o with | none => PUnit | some υ => Expr (S ⋈ Δ ⋈ Φ) υ)
  | none, _ => PUnit.unit
  | some _, a => Subst.act σ Φ a

/-- Reindex a classifier by substituting the component after a fixed prefix. -/
def substitute {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) {τ : C.Ty}
    (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ) :
    ClassifierAt bd (S ⋈ Δ ⋈ Φ) τ :=
  substituteAux σ (bd τ) a

private theorem substituteAux_comp {S Γ Δ Ξ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some υ => Expr (S ⋈ Γ ⋈ Φ) υ) :
    substituteAux (Subst.comp σ θ) o a =
      substituteAux θ o (substituteAux σ o a) := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some υ => apply act_comp

theorem substitute_comp {S Γ Δ Ξ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    {τ : C.Ty} (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ) :
    substitute (Subst.comp σ θ) a = substitute θ (substitute σ a) :=
  substituteAux_comp σ θ (bd τ) a

theorem substitute_cast_local {S Γ Δ Φ Λ Ξ α : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (h : Λ = Ξ) {τ : C.Ty}
    (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ ⋈ Λ ⋈ α) τ) :
    substitute (Φ := Φ ⋈ Ξ ⋈ α) σ
        (cast (congrArg (fun Ω => S ⋈ Γ ⋈ Φ ⋈ Ω ⋈ α) h) a) =
      cast (congrArg (fun Ω => S ⋈ Δ ⋈ Φ ⋈ Ω ⋈ α) h)
        (substitute (Φ := Φ ⋈ Λ ⋈ α) σ a) := by
  subst Ξ
  rfl

end ClassifierAt

namespace Subst

/-- The identity substitution after a fixed prefix. -/
def prefixedId (S Γ : C.Arity) : Subst Γ (S ⋈ Γ) :=
  fun ⦃_⦄ ⦃_⦄ x => Expr.η (C.inr x)

theorem prefixedId_comp {S Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    Subst.comp (prefixedId S Γ) σ = σ := by
  funext α τ x
  apply act_η_prefixed

theorem comp_prefixedId {S Γ Δ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    Subst.comp σ (prefixedId S Δ) = σ := by
  funext α τ x
  apply act_idOfη
  intro β υ y
  rfl

end Subst

namespace ClassifierAt

variable {bd : C.Ty → Option C.Ty}

private theorem substituteAux_prefixedId {S Γ Φ : C.Arity}
    (o : Option C.Ty)
    (a : match o with | none => PUnit | some υ => Expr (S ⋈ Γ ⋈ Φ) υ) :
    substituteAux (Subst.prefixedId S Γ) o a = a := by
  cases o with
  | none => exact Subsingleton.elim _ _
  | some υ =>
      apply act_idOfη
      intro β ν x
      rfl

theorem substitute_prefixedId {S Γ Φ : C.Arity} {τ : C.Ty}
    (a : ClassifierAt bd (S ⋈ Γ ⋈ Φ) τ) :
    substitute (Subst.prefixedId S Γ) a = a :=
  substituteAux_prefixedId (bd τ) a

end ClassifierAt

/-- A typed address into the recursively nested slots of a telescope.

`here x` selects an immediate slot `x`; `nested x p` first enters the binding
arity of an outer slot `x` and then follows the inner path `p`.  The indices
record the selected slot's class and binding arity, together with the
accumulated prefix in which its classifier may live.  A `Decoration` assigns
classifier data to every such address; the path itself carries no classifier.
-/
inductive DecorationPath [P : Precedence C] :
    C.Arity → C.Arity → C.Arity → C.Ty → Type where
  | here {Δ α : C.Arity} {τ : C.Ty} (x : Δ ∋[τ] α) :
      DecorationPath Δ (P.before x) α τ
  | nested {Δ α β Φ : C.Arity} {τ υ : C.Ty}
      (x : Δ ∋[υ] β) (p : DecorationPath β Φ α τ) :
      DecorationPath Δ (P.before x ⋈ Φ) α τ

/-- A decoration assigns a classifier to every recursively nested slot. -/
abbrev Decoration [Precedence C] (bd : C.Ty → Option C.Ty)
    (Ω Δ : C.Arity) : Type :=
  ∀ ⦃Φ α : C.Arity⦄ ⦃τ : C.Ty⦄,
    DecorationPath (C := C) Δ Φ α τ → ClassifierAt bd (Ω ⋈ Φ ⋈ α) τ

namespace Decoration

variable [P : Precedence C] {bd : C.Ty → Option C.Ty}

/-- The classifier attached to an immediate slot. -/
def classifier {Ω Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (x : Δ ∋[τ] α) :
    ClassifierAt bd (Ω ⋈ P.before x ⋈ α) τ :=
  D (.here x)

/-- The decoration of a slot's binding arity. -/
def nested {Ω Δ α : C.Arity} {τ : C.Ty}
    (D : Decoration bd Ω Δ) (x : Δ ∋[τ] α) :
    Decoration bd (Ω ⋈ P.before x) α :=
  fun ⦃_⦄ ⦃_⦄ ⦃_⦄ p => D (.nested x p)

/-- Reindex the external base of a decoration along a renaming. -/
def rename {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) :
    Decoration bd Γ Ξ → Decoration bd Δ Ξ :=
  fun D ⦃Φ⦄ ⦃α⦄ ⦃_⦄ p =>
    ClassifierAt.rename ((ρ ⇑ʳ Φ) ⇑ʳ α) (D p)

theorem rename_id {Γ Ξ : C.Arity} (D : Decoration bd Γ Ξ) :
    rename (𝟙ʳ Γ) D = D := by
  funext Φ α τ p
  rw [rename, Renaming.extend_id, Renaming.extend_id]
  apply ClassifierAt.rename_id

theorem rename_comp {Γ Δ Ξ Ω : C.Arity} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ)
    (D : Decoration bd Γ Ω) :
    rename (σ ∘ʳ ρ) D = rename σ (rename ρ D) := by
  funext Φ α τ p
  rw [rename, Renaming.extend_comp, Renaming.extend_comp]
  apply ClassifierAt.rename_comp

/-- Reindex the context component of a decoration after the fixed prefix `S`. -/
def substitute {S Γ Δ Φ Ξ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    Decoration bd (S ⋈ Γ ⋈ Φ) Ξ → Decoration bd (S ⋈ Δ ⋈ Φ) Ξ :=
  fun D ⦃Ω⦄ ⦃α⦄ ⦃_⦄ p =>
    ClassifierAt.substitute (Φ := Φ ⋈ Ω ⋈ α) σ (D p)

theorem substitute_prefixedId {S Γ Φ Ξ : C.Arity}
    (D : Decoration bd (S ⋈ Γ ⋈ Φ) Ξ) :
    substitute (Subst.prefixedId S Γ) D = D := by
  funext Ω α τ p
  apply ClassifierAt.substitute_prefixedId

theorem substitute_comp {S Γ Δ Ξ Φ Ω : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (D : Decoration bd (S ⋈ Γ ⋈ Φ) Ω) :
    substitute (Subst.comp σ θ) D = substitute θ (substitute σ D) := by
  funext Λ α τ p
  apply ClassifierAt.substitute_comp

private theorem path_empty {Φ α : C.Arity} {τ : C.Ty} :
    DecorationPath (C := C) 1 Φ α τ → False
  | .here x => C.unit_is_empty x
  | .nested x _ => C.unit_is_empty x

/-- The unique decoration of the empty arity. -/
def empty (bd : C.Ty → Option C.Ty) (Ω : C.Arity) : Decoration bd Ω 1 :=
  fun ⦃_⦄ ⦃_⦄ ⦃_⦄ p => False.elim (path_empty p)

theorem rename_empty {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
    rename ρ (empty bd Γ) = empty bd Δ := by
  funext Φ α τ p
  exact False.elim (path_empty p)

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

theorem rename_concatenate {Ω Ξ Γ Δ : C.Arity} (ρ : Ω →ʳ Ξ)
    (D : Decoration bd Ω Γ) (E : Decoration bd (Ω ⋈ Γ) Δ) :
    rename ρ (concatenate D E) =
      concatenate (rename ρ D) (rename (ρ ⇑ʳ Γ) E) := by
  funext Φ α τ p
  cases p with
  | here x =>
      simp only [rename]
      rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_here_inl, concatenate_here_inl]
        exact ClassifierAt.rename_cast_local ρ
          (P.before_inl (Δ := Δ) y).symm (D (.here y))
      · rw [concatenate_here_inr, concatenate_here_inr]
        simpa only [Renaming.extend_assoc] using
          ClassifierAt.rename_cast_local ρ
            (P.before_inr (Γ := Γ) y).symm (E (.here y))
  | nested x p =>
      simp only [rename]
      rcases C.cover Γ Δ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [concatenate_nested_inl, concatenate_nested_inl]
        exact ClassifierAt.rename_cast_local ρ
          (congrArg (fun Λ => Λ ⋈ _) (P.before_inl (Δ := Δ) y).symm)
          (D (.nested y p))
      · rw [concatenate_nested_inr, concatenate_nested_inr]
        simp only [rename]
        simpa only [Renaming.extend_assoc] using
          ClassifierAt.rename_cast_local ρ
            (congrArg (fun Λ => Λ ⋈ _) (P.before_inr (Γ := Γ) y).symm)
            (E (.nested y p))

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

end Decoration

/-- A raw signature equipped with a decoration over the empty base. -/
structure DecoratedSignature [Precedence C] (bd : C.Ty → Option C.Ty) where
  arity : C.Arity
  decoration : Decoration bd 1 arity

namespace DecoratedSignature

/-- Erase a decorated signature to its raw arity. -/
abbrev erase [Precedence C] {bd : C.Ty → Option C.Ty}
    (S : DecoratedSignature (C := C) bd) : C.Arity :=
  S.arity

end DecoratedSignature

/-- A raw telescope equipped with a decoration over `Ω`. -/
structure DecoratedTelescope [Precedence C] (bd : C.Ty → Option C.Ty)
    (Ω : C.Arity) where
  arity : C.Arity
  decoration : Decoration bd Ω arity

namespace DecoratedTelescope

variable [Precedence C] {bd : C.Ty → Option C.Ty} {Ω : C.Arity}

/-- Erase a decorated telescope to its raw arity. -/
abbrev erase (Δ : DecoratedTelescope bd Ω) : C.Arity := Δ.arity

/-- Reindex the base of a decorated telescope along a renaming. -/
def rename {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope bd Γ) : DecoratedTelescope bd Δ where
  arity := Ξ.arity
  decoration := Decoration.rename ρ Ξ.decoration

theorem rename_id {Γ : C.Arity} (Δ : DecoratedTelescope bd Γ) :
    rename (𝟙ʳ Γ) Δ = Δ := by
  cases Δ
  simp [rename, Decoration.rename_id]

theorem rename_comp {Γ Δ Ξ : C.Arity} (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ)
    (Ω : DecoratedTelescope bd Γ) :
    rename (σ ∘ʳ ρ) Ω = rename σ (rename ρ Ω) := by
  cases Ω
  simp [rename, Decoration.rename_comp]

/-- Reindex the context component of a decorated telescope by substitution. -/
def substitute {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ))
    (Ξ : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ)) :
    DecoratedTelescope bd (S ⋈ Δ ⋈ Φ) where
  arity := Ξ.arity
  decoration := Decoration.substitute σ Ξ.decoration

theorem substitute_prefixedId {S Γ Φ : C.Arity}
    (Δ : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ)) :
    substitute (Subst.prefixedId S Γ) Δ = Δ := by
  cases Δ
  simp [substitute, Decoration.substitute_prefixedId]

theorem substitute_comp {S Γ Δ Ξ Φ : C.Arity}
    (σ : Subst Γ (S ⋈ Δ)) (θ : Subst Δ (S ⋈ Ξ))
    (Ω : DecoratedTelescope bd (S ⋈ Γ ⋈ Φ)) :
    substitute (Subst.comp σ θ) Ω = substitute θ (substitute σ Ω) := by
  cases Ω
  simp [substitute, Decoration.substitute_comp]

/-- The empty decorated telescope. -/
def empty (bd : C.Ty → Option C.Ty) (Ω : C.Arity) : DecoratedTelescope bd Ω where
  arity := 1
  decoration := Decoration.empty bd Ω

theorem rename_empty {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ) :
    rename ρ (empty bd Γ) = empty bd Δ := by
  simp [rename, empty, Decoration.rename_empty]

theorem substitute_empty {S Γ Δ Φ : C.Arity} (σ : Subst Γ (S ⋈ Δ)) :
    substitute (Φ := Φ) σ (empty bd (S ⋈ Γ ⋈ Φ)) =
      empty bd (S ⋈ Δ ⋈ Φ) := by
  simp [substitute, empty, Decoration.substitute_empty]

/-- Concatenation of decorated telescopes. -/
def concatenate (Γ : DecoratedTelescope bd Ω)
    (Δ : DecoratedTelescope bd (Ω ⋈ Γ.arity)) : DecoratedTelescope bd Ω where
  arity := Γ.arity ⋈ Δ.arity
  decoration := Decoration.concatenate Γ.decoration Δ.decoration

theorem rename_concatenate {Γ Δ : C.Arity} (ρ : Γ →ʳ Δ)
    (Ξ : DecoratedTelescope bd Γ)
    (Ω : DecoratedTelescope bd (Γ ⋈ Ξ.arity)) :
    rename ρ (concatenate Ξ Ω) =
      concatenate (rename ρ Ξ) (rename (ρ ⇑ʳ Ξ.arity) Ω) := by
  cases Ξ
  cases Ω
  simp [rename, concatenate, Decoration.rename_concatenate]

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

/-- Extend a decorated telescope by a telescope over its resulting base. -/
abbrev extend (Γ : DecoratedTelescope bd Ω)
    (Δ : DecoratedTelescope bd (Ω ⋈ Γ.arity)) : DecoratedTelescope bd Ω :=
  concatenate Γ Δ

end DecoratedTelescope
