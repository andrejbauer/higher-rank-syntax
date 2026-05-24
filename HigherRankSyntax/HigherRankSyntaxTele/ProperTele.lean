import HigherRankSyntaxTele.Renaming

/-!
# Proper Telescopes (`ProperTele`)

A type class on `Tele C.Arity` providing the structural ops needed to
dispatch slots of `Γ ⋈* t` between t-side and Γ-side:

* `weaken Γ` — embeds Γ into `Γ ⋈* t`.
* `embed Γ`  — embeds t into `Γ ⋈* t`.
* `classify Γ` — CPS dispatch of a `(Γ ⋈* t)`-slot to either side.
* `classify_embed`, `classify_weaken` — reflection lemmas.

Two instances are declared:

* `Tele.id` — trivial (no t-slots).
* `Tele.cons a ∘ᵗ t` from `[ProperTele t]` — extend by one binder.

Tele equality is unchanged by the class — instances live in the
instance slot, not in Tele's data, so the strict-monoid laws on Tele
(`id_comp`, `comp_id`, `comp_assoc`) keep their `rfl` proofs.
-/


/-- A `ProperTele` instance equips a telescope with classifier and
weaken/embed renamings so that a slot of `Γ ⋈* t` dispatches uniformly
between t-slots and Γ-slots. -/
class ProperTele {C : Carrier} (t : Tele C.Arity) : Type 1 where
  /-- Weakening: embed the base shape into the extended shape. -/
  weaken : (Γ : Shape C) → Γ →ʳ Γ ⋈* t
  /-- Embedding: embed the telescope's own shape into the extended shape. -/
  embed : (Γ : Shape C) → t →ʳ Γ ⋈* t
  /-- Classifier (CPS): dispatch a slot of `Γ ⋈* t` into either a t-slot
  or a Γ-slot. -/
  classify : (Γ : Shape C) → {α : C.Arity} → (X : Type) →
             ((Γ ⋈* t) ∋ α) →
             ((t ∋ α) → X) → ((Γ ∋ α) → X) → X
  /-- Reflection: classifying an embedded t-slot fires the t-continuation. -/
  classify_embed : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (q_τ : t ∋ α)
                   (k_shape : (t ∋ α) → X) (k_Γ : (Γ ∋ α) → X),
                   classify Γ X (embed Γ q_τ) k_shape k_Γ = k_shape q_τ
  /-- Reflection: classifying a weakened Γ-slot fires the Γ-continuation. -/
  classify_weaken : ∀ (Γ : Shape C) (X : Type) {α : C.Arity} (q_Γ : Γ ∋ α)
                    (k_shape : (t ∋ α) → X) (k_Γ : (Γ ∋ α) → X),
                    classify Γ X (weaken Γ q_Γ) k_shape k_Γ = k_Γ q_Γ

namespace ProperTele

/-- The identity telescope: empty, classifier returns everything to Γ. -/
instance instId {C : Carrier} : ProperTele (Tele.id : Tele C.Arity) where
  weaken := fun Γ => Renaming.id Γ
  embed := fun _Γ => ⟨fun {_} p => nomatch p⟩
  classify := fun _Γ _α _X p _k_shape k_Γ => k_Γ p
  classify_embed := fun _Γ _X _α q_τ _k_shape _k_Γ => nomatch q_τ
  classify_weaken := fun _Γ _X _α _q_Γ _k_shape _k_Γ => rfl

/-- Extend a `ProperTele` by one arity at the top. -/
instance instCons {C : Carrier} (a : C.Arity) (t : Tele C.Arity) [ProperTele t] :
    ProperTele (Tele.cons a ∘ᵗ t) where
  weaken := fun Γ => ⟨fun {_} p => .there ((ProperTele.weaken (t := t) Γ).apply p)⟩
  embed := fun Γ => ⟨fun {_} p =>
    match p with
    | .here i  => .here i
    | .there q => .there ((ProperTele.embed (t := t) Γ).apply q)⟩
  classify := fun Γ _α X p k_shape k_Γ =>
    match p with
    | .here i   => k_shape (.here i)
    | .there p' => ProperTele.classify (t := t) Γ X p'
                     (fun q_t => k_shape (.there q_t)) k_Γ
  classify_embed := fun Γ X _α q_τ k_shape k_Γ => by
    cases q_τ with
    | here _i  => rfl
    | there q' =>
      exact ProperTele.classify_embed (t := t) Γ X q'
              (fun q_t => k_shape (.there q_t)) k_Γ
  classify_weaken := fun Γ X _α q_Γ k_shape k_Γ' => by
    exact ProperTele.classify_weaken (t := t) Γ X q_Γ
            (fun q_t => k_shape (.there q_t)) k_Γ'

end ProperTele
