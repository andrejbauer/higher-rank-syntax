import HigherRankSyntax.Typing.Equivalence

/-!
# Contexts

A context is an arity together with a well-formed ambient over it.  `Ctx.Tele Γ`
is the well-formed telescopes over `Γ`, `Ctx.Subst Γ Θ` the fillings of `Θ`, and
`Ctx.Hom Γ Δ` the fillings of `Δ` weakened into `Γ`, with `Hom.id` and `Hom.comp`
satisfying the category laws.  Nothing here is quotiented.
-/

/-- An arity with a well-formed ambient over it. -/
structure Ctx where
  /-- The arity whose slots the ambient declares. -/
  arity : C.Arity
  /-- The ambient. -/
  ambient : Ambient arity
  /-- The ambient is well formed. -/
  wf : Ambient.Wf ambient

namespace Ctx

/-- A well-formed telescope over a context, with its arity. -/
def Tele (Γ : Ctx) : Type :=
  Σ Ω : C.Arity, { Θ : dTel Γ.arity Ω // Wf_t Γ.ambient Θ }

/-- The arity a telescope declares. -/
def Tele.arity {Γ : Ctx} (Θ : Γ.Tele) : C.Arity := Θ.1

/-- The underlying telescope. -/
def Tele.telescope {Γ : Ctx} (Θ : Γ.Tele) : dTel Γ.arity Θ.arity := Θ.2.1

/-- The telescope is well formed. -/
theorem Tele.wf {Γ : Ctx} (Θ : Γ.Tele) : Wf_t Γ.ambient Θ.telescope := Θ.2.2

/-- 8(8): a context as a telescope over another context. -/
def weaken (Δ Γ : Ctx) : Γ.Tele :=
  ⟨Δ.arity, _, Δ.wf.weaken Γ.ambient⟩

/-- 9.1: a well-formed filling of a telescope. -/
def Subst (Γ : Ctx) (Θ : Γ.Tele) : Type :=
  { σ : _root_.Subst Θ.arity Γ.arity // Wf_s Γ.ambient Θ.telescope σ }

/-- 9.3: a morphism of contexts is a filling of the target weakened into the
source. -/
def Hom (Γ Δ : Ctx) : Type := Γ.Subst (Δ.weaken Γ)

/-- The identity morphism. -/
def Hom.id (Γ : Ctx) : Γ.Hom Γ :=
  ⟨_root_.Subst.id Γ.arity, (Wf_sub.id Γ.wf).toFilling⟩

/-- Composition of morphisms. -/
def Hom.comp {Γ Δ Ξ : Ctx} (f : Γ.Hom Δ) (g : Δ.Hom Ξ) : Γ.Hom Ξ :=
  ⟨_root_.Subst.comp (Γ := 1) g.1 f.1, (g.2.toWf_sub.comp f.2.toWf_sub).toFilling⟩

/-- The identity is a left unit for composition. -/
theorem Hom.id_comp {Γ Δ : Ctx} (f : Γ.Hom Δ) : Hom.comp (Hom.id Γ) f = f := by
  refine Subtype.ext ?_
  funext Λ i
  exact act_id Γ.arity Λ (f.1 i)

/-- The identity is a right unit for composition. -/
theorem Hom.comp_id {Γ Δ : Ctx} (f : Γ.Hom Δ) : Hom.comp f (Hom.id Δ) = f := by
  refine Subtype.ext ?_
  funext Λ i
  exact act_η f.1 Λ i

/-- Composition is associative. -/
theorem Hom.comp_assoc {Γ Δ Ξ Ψ : Ctx} (f : Γ.Hom Δ) (g : Δ.Hom Ξ) (h : Ξ.Hom Ψ) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  refine Subtype.ext ?_
  funext Λ i
  exact act_comp (Γ := 1) g.1 f.1 Λ (h.1 i)

end Ctx
