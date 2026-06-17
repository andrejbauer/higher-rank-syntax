import HigherRankSyntax.ProperTele

/-!
# Scoped expressions with telescope-indexed local stacks

`ScopedExpr Γ τ` separates free variables from local binders.  The free
context `Γ` is stable, while the local context `τ` changes as we descend under
binders.  Unlike the earlier list-indexed prototype, local stacks are now
ordinary `Shape`s, and passive prefixes are decomposed by explicit
`ProperSpine` witnesses.

The key representation invariant for one-binder local substitution is:

* `υ` is the older local tail;
* `α` is the active binder being substituted;
* `χ` is the newer passive prefix;
* the source local context is `(υ ∷ α) ⧺ χ`;
* the target local context is `υ ⧺ χ`.

This orientation makes argument descent definitional:
`((υ ∷ α) ⧺ χ) ∷ β = (υ ∷ α) ⧺ (χ ∷ β)`.
-/

/-- A scoped application head.  A head is either free, from the ambient
context, or local, from the current local telescope. -/
inductive ScopedHead {C : Carrier} (Γ τ : Shape C) : C.Arity → Type where
  | free {α : C.Arity} : Γ ∋ α → ScopedHead Γ τ α
  | local {α : C.Arity} : τ ∋ α → ScopedHead Γ τ α

/-- Scoped expressions over free context `Γ` and local binder telescope `τ`. -/
inductive ScopedExpr {C : Carrier} (Γ : Shape C) : Shape C → Type where
  | ap : {τ : Shape C} → {α : C.Arity} →
      ScopedHead Γ τ α →
      ((i : C.Binder α) → ScopedExpr Γ (τ ∷ i.arity)) →
      ScopedExpr Γ τ

namespace ScopedHead

/-- Rename free variables in a head; local heads are untouched. -/
def renameFree {C : Carrier} {Γ Δ τ : Shape C}
    (ρ : Γ →ʳ Δ) : {α : C.Arity} → ScopedHead Γ τ α → ScopedHead Δ τ α
  | _, .free x => .free (ρ x)
  | _, .local x => .local x

/-- Rename local variables in a head; free heads are untouched. -/
def renameLocal {C : Carrier} {Γ τ ν : Shape C}
    (ρ : τ →ʳ ν) : {α : C.Arity} → ScopedHead Γ τ α → ScopedHead Γ ν α
  | _, .free x => .free x
  | _, .local x => .local (ρ x)

/-- Weaken a head under one fresh local binder. -/
def weakenLocal {C : Carrier} {Γ τ : Shape C}
    (β : C.Arity) : {α : C.Arity} → ScopedHead Γ τ α →
      ScopedHead Γ (τ ∷ β) α
  | _, .free x => .free x
  | _, .local x => .local (.there x)

end ScopedHead

namespace ScopedExpr

theorem ap_args_congr {C : Carrier} {Γ τ : Shape C} {α : C.Arity}
    (head : ScopedHead Γ τ α)
    {args args' : (i : C.Binder α) → ScopedExpr Γ (τ ∷ i.arity)}
    (hargs : ∀ i, args i = args' i) :
    ScopedExpr.ap head args = ScopedExpr.ap head args' := by
  congr
  funext i
  exact hargs i

/-- Direct subterm relation for recursion through application arguments. -/
inductive Subterm {C : Carrier} {Γ : Shape C} :
    (Σ τ : Shape C, ScopedExpr Γ τ) →
      (Σ τ : Shape C, ScopedExpr Γ τ) → Prop where
  | of_arg {τ : Shape C} {α : C.Arity}
      (head : ScopedHead Γ τ α)
      (args : (i : C.Binder α) → ScopedExpr Γ (τ ∷ i.arity))
      (j : C.Binder α) :
      Subterm ⟨τ ∷ j.arity, args j⟩ ⟨τ, ScopedExpr.ap head args⟩

/-- Argument descent through a passive-prefix decomposition. -/
theorem Subterm.of_arg_ext {C : Carrier} {Γ : Shape C}
    {τ χ : Shape C} {α : C.Arity}
    (head : ScopedHead Γ (τ ⧺ χ) α)
    (args : (i : C.Binder α) → ScopedExpr Γ ((τ ⧺ χ) ∷ i.arity))
    (j : C.Binder α) :
    Subterm ⟨τ ⧺ (χ ∷ j.arity), args j⟩
      ⟨τ ⧺ χ, ScopedExpr.ap head args⟩ :=
  Subterm.of_arg head args j

/-- Structural recursion on scoped expressions is well-founded. -/
theorem Subterm.wf {C : Carrier} {Γ : Shape C} :
    WellFounded (Subterm (Γ := Γ)) := by
  refine ⟨fun ⟨τ, e⟩ => ?_⟩
  induction e with
  | ap head args ih =>
      refine Acc.intro _ ?_
      rintro ⟨_, _⟩ h
      cases h
      exact ih _

private instance {C : Carrier} {Γ : Shape C} :
    WellFoundedRelation (Σ τ : Shape C, ScopedExpr Γ τ) where
  rel := Subterm
  wf := Subterm.wf

/-- Rename free variables throughout a scoped expression. -/
def renameFree {C : Carrier} {Γ Δ : Shape C}
    (ρ : Γ →ʳ Δ) : {τ : Shape C} → ScopedExpr Γ τ → ScopedExpr Δ τ
  | _, .ap head args =>
      .ap (head.renameFree ρ) (fun i => renameFree ρ (args i))

/-- Extend a local renaming under one fresh local binder. -/
def localCons {C : Carrier} {τ ν : Shape C}
    (ρ : τ →ʳ ν) (β : C.Arity) : τ ∷ β →ʳ ν ∷ β :=
  ρ ⇑ʳ β

/-- Rename local variables throughout a scoped expression. -/
def renameLocal {C : Carrier} {Γ τ ν : Shape C}
    (ρ : τ →ʳ ν) : ScopedExpr Γ τ → ScopedExpr Γ ν
  | .ap head args =>
      .ap (head.renameLocal ρ) (fun i =>
        renameLocal (localCons ρ i.arity) (args i))

/-! ## Renaming laws

These are deliberately stated for the scoped syntax rather than for flattened
telescopes.  The recursive cases say exactly what is happening: a renaming
acts on the current head and is extended under each freshly opened binder.
-/

theorem renameFree_id {C : Carrier} {Γ τ : Shape C}
    (e : ScopedExpr Γ τ) :
    renameFree (𝟙ʳ : Γ →ʳ Γ) e = e := by
  induction e with
  | ap head args ih =>
      cases head <;> simp [renameFree, ScopedHead.renameFree]
      all_goals
        funext i
        exact ih i

theorem renameFree_comp {C : Carrier} {Γ Δ Ξ τ : Shape C}
    (ρ : Γ →ʳ Δ) (σ : Δ →ʳ Ξ) (e : ScopedExpr Γ τ) :
    renameFree (σ ∘ʳʳ ρ) e = renameFree σ (renameFree ρ e) := by
  induction e generalizing Δ Ξ with
  | ap head args ih =>
      cases head <;> simp [renameFree, ScopedHead.renameFree]
      · constructor
        · rfl
        · funext i
          exact ih i ρ σ
      · funext i
        exact ih i ρ σ

theorem renameLocal_id {C : Carrier} {Γ τ : Shape C}
    (e : ScopedExpr Γ τ) :
    renameLocal (𝟙ʳ : τ →ʳ τ) e = e := by
  induction e with
  | ap head args ih =>
      cases head <;> simp [renameLocal, ScopedHead.renameLocal, localCons,
        Renaming.extend_id]
      all_goals
        funext i
        exact ih i

theorem renameLocal_comp {C : Carrier} {Γ τ ν ξ : Shape C}
    (ρ : τ →ʳ ν) (σ : ν →ʳ ξ) (e : ScopedExpr Γ τ) :
    renameLocal (σ ∘ʳʳ ρ) e =
      renameLocal σ (renameLocal ρ e) := by
  induction e generalizing ν ξ with
  | ap head args ih =>
      cases head <;> simp [renameLocal, ScopedHead.renameLocal, localCons,
        Renaming.extend_comp]
      · funext i
        exact ih i (localCons ρ i.arity) (localCons σ i.arity)
      · constructor
        · rfl
        · funext i
          exact ih i (localCons ρ i.arity) (localCons σ i.arity)

/-- η-expansion of an arbitrary head. -/
def etaHead {C : Carrier} {Γ τ : Shape C} :
    {α : C.Arity} → ScopedHead Γ τ α → ScopedExpr Γ (τ ∷ α)
  | α, head =>
      .ap (head.weakenLocal α)
        (fun i => etaHead (τ := τ ∷ α) (.local (.here i)))
termination_by α _ => α
decreasing_by exact ⟨i, rfl⟩

/-- Relative-monad unit: η-expansion of a free variable. -/
def eta {C : Carrier} {Γ : Shape C} {α : C.Arity}
    (x : Γ ∋ α) : ScopedExpr Γ ⌊α⌋ :=
  etaHead (τ := Shape.nil) (.free x)

/-- Inject a passive-prefix slot into `υ ⧺ χ`. -/
def localPrefix {C : Carrier} {χ : Shape C}
    (pχ : ProperSpine χ) (υ : Shape C) : χ →ʳ υ ⧺ χ :=
  ProperSpine.inr pχ υ

/-- Inject an older-tail slot into `υ ⧺ χ`. -/
def localTail {C : Carrier} {χ : Shape C}
    (pχ : ProperSpine χ) (υ : Shape C) : υ →ʳ υ ⧺ χ :=
  ProperSpine.inl pχ υ

/-- Rename the older tail under a fixed passive prefix. -/
def localMapTail {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν) : υ ⧺ χ →ʳ ν ⧺ χ :=
  ⟨fun x =>
    ProperSpine.classify pχ υ _ x
      (fun xχ => localPrefix pχ ν xχ)
      (fun xυ => localTail pχ ν (ρ xυ))⟩

@[simp] theorem localMapTail_nil {C : Carrier} {υ ν : Shape C}
    (ρ : υ →ʳ ν) :
    localMapTail .nil ρ = ρ := rfl

theorem localMapTail_prefix {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν)
    {α : C.Arity} (x : χ ∋ α) :
    localMapTail pχ ρ (localPrefix pχ υ x) =
      localPrefix pχ ν x := by
  unfold localMapTail localPrefix localTail
  change
    ProperSpine.classify pχ υ _
        ((ProperSpine.inr pχ υ) x)
        (fun xχ => (ProperSpine.inr pχ ν) xχ)
        (fun xυ => (ProperSpine.inl pχ ν) (ρ xυ)) =
      (ProperSpine.inr pχ ν) x
  rw [ProperSpine.classify_inr]

theorem localMapTail_tail {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν)
    {α : C.Arity} (x : υ ∋ α) :
    localMapTail pχ ρ (localTail pχ υ x) =
      localTail pχ ν (ρ x) := by
  unfold localMapTail localPrefix localTail
  change
    ProperSpine.classify pχ υ _
        ((ProperSpine.inl pχ υ) x)
        (fun xχ => (ProperSpine.inr pχ ν) xχ)
        (fun xυ => (ProperSpine.inl pχ ν) (ρ xυ)) =
      (ProperSpine.inl pχ ν) (ρ x)
  rw [ProperSpine.classify_inl]

@[simp] theorem localMapTail_cons {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν) (β : C.Arity) :
    localMapTail (.cons pχ β) ρ =
      localCons (localMapTail pχ ρ) β := by
  ext α x
  cases x with
  | here i => rfl
  | there x =>
      unfold localMapTail localCons localPrefix localTail
      change
        ProperSpine.classify (.cons pχ β) υ _ (.there x)
            (fun xχ => (ProperSpine.inr (.cons pχ β) ν) xχ)
            (fun xυ => (ProperSpine.inl (.cons pχ β) ν) (ρ xυ)) =
          ListSlotAt.there
            (ProperSpine.classify pχ υ _
              x
              (fun xχ => (ProperSpine.inr pχ ν) xχ)
              (fun xυ => (ProperSpine.inl pχ ν) (ρ xυ)))
      rw [ProperSpine.classify_cons_there]
      simp only [ProperSpine.inr_cons_there, ProperSpine.inl_cons]
      change
        ProperSpine.classify pχ υ ((ν ⧺ χ) ∷ β ∋ α) x
            (fun xχ => .there ((ProperSpine.inr pχ ν) xχ))
            (fun xυ => .there ((ProperSpine.inl pχ ν) (ρ xυ))) =
          .there
            (ProperSpine.classify pχ υ (ν ⧺ χ ∋ α) x
              (fun xχ => (ProperSpine.inr pχ ν) xχ)
              (fun xυ => (ProperSpine.inl pχ ν) (ρ xυ)))
      rw [ProperSpine.classify_weaken]

/-- The three origins of a local head while substituting one active binder. -/
inductive LocalSite {C : Carrier} (χ υ : Shape C) (α : C.Arity) :
    C.Arity → Type where
  | pre {β : C.Arity} (x : χ ∋ β) : LocalSite χ υ α β
  | active (i : C.Binder α) : LocalSite χ υ α i.arity
  | tail {β : C.Arity} (x : υ ∋ β) : LocalSite χ υ α β

namespace LocalSite

/-- Rename only the older-tail component of a classified local site. -/
def renameTail {C : Carrier} {χ υ ν : Shape C} {α β : C.Arity}
    (ρ : υ →ʳ ν) : LocalSite χ υ α β → LocalSite χ ν α β
  | .pre x => .pre x
  | .active i => .active i
  | .tail x => .tail (ρ x)

/-- Embed a classified local site back into `(υ ∷ α) ⧺ χ`. -/
def embedSource {C : Carrier} {χ υ : Shape C} (pχ : ProperSpine χ)
    {α β : C.Arity} : LocalSite χ υ α β → (υ ∷ α) ⧺ χ ∋ β
  | .pre x => localPrefix pχ (υ ∷ α) x
  | .active i => localTail pχ (υ ∷ α) (.here i)
  | .tail x => localTail pχ (υ ∷ α) (.there x)

/-- Classify a local slot of `(υ ∷ α) ⧺ χ`. -/
def classify {C : Carrier} {χ : Shape C} (pχ : ProperSpine χ)
    (υ : Shape C) (α : C.Arity) {β : C.Arity}
    (x : (υ ∷ α) ⧺ χ ∋ β) : LocalSite χ υ α β :=
  ProperSpine.classify pχ (υ ∷ α) _ x
    (fun xχ => .pre xχ)
    (fun
      | .here i => .active i
      | .there xυ => .tail xυ)

theorem cover {C : Carrier} {χ υ : Shape C}
    (pχ : ProperSpine χ) (α : C.Arity) {β : C.Arity}
    (x : (υ ∷ α) ⧺ χ ∋ β) :
    ∃ site : LocalSite χ υ α β, x = embedSource pχ site := by
  rcases ProperSpine.coverEq pχ (υ ∷ α) x with ⟨xχ, h⟩ | ⟨y, h⟩
  · exact ⟨.pre xχ, h⟩
  · cases y with
    | here i => exact ⟨.active i, h⟩
    | there xυ => exact ⟨.tail xυ, h⟩

theorem classify_pre {C : Carrier} {χ υ : Shape C}
    (pχ : ProperSpine χ) (α : C.Arity) {β : C.Arity}
    (x : χ ∋ β) :
    classify pχ υ α (localPrefix pχ (υ ∷ α) x) = LocalSite.pre x := by
  exact ProperSpine.classify_inr pχ (υ ∷ α) _ x _ _

theorem classify_active {C : Carrier} {χ υ : Shape C}
    (pχ : ProperSpine χ) (α : C.Arity) (i : C.Binder α) :
    classify pχ υ α (localTail pχ (υ ∷ α) (.here i)) = LocalSite.active i := by
  exact ProperSpine.classify_inl pχ (υ ∷ α) _ (.here i) _ _

theorem classify_tail {C : Carrier} {χ υ : Shape C}
    (pχ : ProperSpine χ) (α : C.Arity) {β : C.Arity}
    (x : υ ∋ β) :
    classify pχ υ α (localTail pχ (υ ∷ α) (.there x)) = LocalSite.tail x := by
  exact ProperSpine.classify_inl pχ (υ ∷ α) _ (.there x) _ _

/-- Classifying after a tail-only renaming is the same as classifying first and
renaming only the tail case. -/
theorem classify_mapTail {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν) (α : C.Arity)
    {β : C.Arity} (x : (υ ∷ α) ⧺ χ ∋ β) :
    classify pχ ν α (localMapTail pχ (localCons ρ α) x) =
      renameTail ρ (classify pχ υ α x) := by
  rcases ProperSpine.coverEq pχ (υ ∷ α) x with ⟨xχ, rfl⟩ | ⟨y, rfl⟩
  · have hmap :
        localMapTail pχ (localCons ρ α)
            ((ProperSpine.inr pχ (υ ∷ α)) xχ) =
          (ProperSpine.inr pχ (ν ∷ α)) xχ := by
        change
          ProperSpine.classify pχ (υ ∷ α) _
              ((ProperSpine.inr pχ (υ ∷ α)) xχ)
              (fun xχ => (ProperSpine.inr pχ (ν ∷ α)) xχ)
              (fun xυ => (ProperSpine.inl pχ (ν ∷ α)) ((localCons ρ α) xυ))
            =
          (ProperSpine.inr pχ (ν ∷ α)) xχ
        rw [ProperSpine.classify_inr]
    rw [hmap]
    unfold classify
    rw [ProperSpine.classify_inr, ProperSpine.classify_inr]
    rfl
  · cases y with
    | here i =>
        have hmap :
            localMapTail pχ (localCons ρ α)
                ((ProperSpine.inl pχ (υ ∷ α)) (.here i)) =
              (ProperSpine.inl pχ (ν ∷ α)) (.here i) := by
          change
            ProperSpine.classify pχ (υ ∷ α) _
                ((ProperSpine.inl pχ (υ ∷ α)) (.here i))
                (fun xχ => (ProperSpine.inr pχ (ν ∷ α)) xχ)
                (fun xυ => (ProperSpine.inl pχ (ν ∷ α)) ((localCons ρ α) xυ))
              =
            (ProperSpine.inl pχ (ν ∷ α)) (.here i)
          rw [ProperSpine.classify_inl]
          rfl
        rw [hmap]
        unfold classify
        rw [ProperSpine.classify_inl, ProperSpine.classify_inl]
        rfl
    | there xυ =>
        have hmap :
            localMapTail pχ (localCons ρ α)
                ((ProperSpine.inl pχ (υ ∷ α)) (.there xυ)) =
              (ProperSpine.inl pχ (ν ∷ α)) (.there (ρ xυ)) := by
          change
            ProperSpine.classify pχ (υ ∷ α) _
                ((ProperSpine.inl pχ (υ ∷ α)) (.there xυ))
                (fun xχ => (ProperSpine.inr pχ (ν ∷ α)) xχ)
                (fun xυ => (ProperSpine.inl pχ (ν ∷ α)) ((localCons ρ α) xυ))
              =
            (ProperSpine.inl pχ (ν ∷ α)) (.there (ρ xυ))
          rw [ProperSpine.classify_inl]
          rfl
        rw [hmap]
        unfold classify
        rw [ProperSpine.classify_inl, ProperSpine.classify_inl]
        rfl

theorem mapTail_embedSource {C : Carrier} {χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν) {α β : C.Arity}
    (site : LocalSite χ υ α β) :
    localMapTail pχ (localCons ρ α) (embedSource pχ site) =
      embedSource pχ (renameTail ρ site) := by
  cases site with
  | pre x =>
      exact localMapTail_prefix pχ (localCons ρ α) x
  | active i =>
      exact localMapTail_tail pχ (localCons ρ α) (.here i)
  | tail x =>
      exact localMapTail_tail pχ (localCons ρ α) (.there x)

end LocalSite

/-- Substitute one active local binder below a passive prefix. -/
def instOneAt {C : Carrier} {Γ : Shape C} :
    {χ : Shape C} → (pχ : ProperSpine χ) → (υ : Shape C) →
    (α : C.Arity) →
    ((i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity)) →
    ScopedExpr Γ ((υ ∷ α) ⧺ χ) → ScopedExpr Γ (υ ⧺ χ)
  | χ, pχ, υ, α, fill, .ap (α := β) head args =>
      match head with
      | .free x =>
          -- Free head: preserve the head and recurse through arguments.
          .ap (.free x)
            (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
      | .local x =>
          match LocalSite.classify pχ υ α x with
          | .pre y =>
              -- Passive-prefix head: preserve the head and recurse.
              .ap (.local (localPrefix pχ υ y))
                (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
          | .tail y =>
              -- Older-tail head: preserve the head and recurse.
              .ap (.local (localTail pχ υ y))
                (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
          | .active j =>
              -- Active head: fire the selected filler, then instantiate the
              -- fresh binder introduced by that filler with transformed args.
              instOneAt .nil (υ ⧺ χ) j.arity
                (fun k => instOneAt (.cons pχ k.arity) υ α fill (args k))
                (renameLocal (localCons (localTail pχ υ) j.arity) (fill j))
termination_by χ _ υ α _ e =>
  (α, (⟨(υ ∷ α) ⧺ χ, e⟩ : Σ τ : Shape C, ScopedExpr Γ τ))
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ ⟨j, rfl⟩
      | exact Prod.Lex.right _ (Subterm.of_arg_ext _ _ _)

/-! ## One-binder computation lemmas -/

theorem instOneAt_freeHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α β : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (x : Γ ∋ β)
    (args : (j : C.Binder β) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill (.ap (.free x) args) =
      .ap (.free x)
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j)) := by
  exact instOneAt.eq_1 χ pχ υ α fill β args x

theorem instOneAt_preHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α β : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (x : χ ∋ β)
    (args : (j : C.Binder β) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill (.ap (.local (localPrefix pχ (υ ∷ α) x)) args) =
      .ap (.local (localPrefix pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j)) := by
  exact instOneAt.eq_2 χ pχ υ α fill β args
    (localPrefix pχ (υ ∷ α) x) x (LocalSite.classify_pre pχ α x)

theorem instOneAt_tailHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α β : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (x : υ ∋ β)
    (args : (j : C.Binder β) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill (.ap (.local (localTail pχ (υ ∷ α) (.there x))) args) =
      .ap (.local (localTail pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j)) := by
  exact instOneAt.eq_3 χ pχ υ α fill β args
    (localTail pχ (υ ∷ α) (.there x)) x (LocalSite.classify_tail pχ α x)

theorem instOneAt_activeHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (i : C.Binder α)
    (args : (j : C.Binder i.arity) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill (.ap (.local (localTail pχ (υ ∷ α) (.here i))) args) =
      instOneAt .nil (υ ⧺ χ) i.arity
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
        (renameLocal (localCons (localTail pχ υ) i.arity) (fill i)) := by
  exact instOneAt.eq_4 χ pχ υ α fill i args
    (localTail pχ (υ ∷ α) (.here i)) (LocalSite.classify_active pχ α i)

theorem instOneAt_preSiteHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α β : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (x : χ ∋ β)
    (args : (j : C.Binder β) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill
        (.ap (.local (LocalSite.embedSource pχ (LocalSite.pre x))) args) =
      .ap (.local (localPrefix pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j)) := by
  change
    instOneAt pχ υ α fill
        (.ap (.local (localPrefix pχ (υ ∷ α) x)) args) =
      .ap (.local (localPrefix pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
  exact instOneAt_preHead pχ fill x args

theorem instOneAt_tailSiteHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α β : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (x : υ ∋ β)
    (args : (j : C.Binder β) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill
        (.ap (.local (LocalSite.embedSource pχ (LocalSite.tail x))) args) =
      .ap (.local (localTail pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j)) := by
  change
    instOneAt pχ υ α fill
        (.ap (.local (localTail pχ (υ ∷ α) (.there x))) args) =
      .ap (.local (localTail pχ υ x))
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
  exact instOneAt_tailHead pχ fill x args

theorem instOneAt_activeSiteHead {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α : C.Arity}
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (i : C.Binder α)
    (args : (j : C.Binder i.arity) →
      ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ j.arity)) :
    instOneAt pχ υ α fill
        (.ap (.local (LocalSite.embedSource pχ (LocalSite.active i))) args) =
      instOneAt .nil (υ ⧺ χ) i.arity
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
        (renameLocal (localCons (localTail pχ υ) i.arity) (fill i)) := by
  change
    instOneAt pχ υ α fill
        (.ap (.local (localTail pχ (υ ∷ α) (.here i))) args) =
      instOneAt .nil (υ ⧺ χ) i.arity
        (fun j => instOneAt (.cons pχ j.arity) υ α fill (args j))
        (renameLocal (localCons (localTail pχ υ) i.arity) (fill i))
  exact instOneAt_activeHead pχ fill i args

theorem renameLocal_activeFiller {C : Carrier} {Γ χ υ ν : Shape C}
    (pχ : ProperSpine χ) (ρ : υ →ʳ ν) {β : C.Arity}
    (e : ScopedExpr Γ (υ ∷ β)) :
    renameLocal (localCons (localMapTail pχ ρ) β)
        (renameLocal (localCons (localTail pχ υ) β) e) =
      renameLocal (localCons (localTail pχ ν) β)
        (renameLocal (localCons ρ β) e) := by
  rw [← renameLocal_comp, ← renameLocal_comp]
  congr 1
  ext γ x
  cases x with
  | here i => rfl
  | there x =>
      exact congrArg ListSlotAt.there (localMapTail_tail pχ ρ x)

theorem instOneAt_congr {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) {α : C.Arity}
    {fill fill' : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity)}
    (hfill : ∀ i, fill i = fill' i)
    {e e' : ScopedExpr Γ ((υ ∷ α) ⧺ χ)}
    (he : e = e') :
    instOneAt pχ υ α fill e = instOneAt pχ υ α fill' e' := by
  subst he
  congr
  funext i
  exact hfill i

private theorem localPrefix_append_right {C : Carrier} {χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    {α : C.Arity} (x : ψ ∋ α) :
    localPrefix (ProperSpine.append pχ pψ) υ (localPrefix pψ χ x) =
      localPrefix pψ (υ ⧺ χ) x :=
  ProperSpine.append_inr_inr pχ pψ υ x

private theorem localPrefix_append_left {C : Carrier} {χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    {α : C.Arity} (x : χ ∋ α) :
    localPrefix (ProperSpine.append pχ pψ) υ (localTail pψ χ x) =
      localTail pψ (υ ⧺ χ) (localPrefix pχ υ x) :=
  ProperSpine.append_inr_inl pχ pψ υ x

private theorem localTail_append {C : Carrier} {χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    {α : C.Arity} (x : υ ∋ α) :
    localTail (ProperSpine.append pχ pψ) υ x =
      localTail pψ (υ ⧺ χ) (localTail pχ υ x) :=
  ProperSpine.append_inl pχ pψ υ x

private theorem renameLocal_extendPassiveFiller {C : Carrier}
    {Γ χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ) {β : C.Arity}
    (e : ScopedExpr Γ (υ ∷ β)) :
    renameLocal (localCons (localTail (ProperSpine.append pχ pψ) υ) β) e =
      renameLocal (localCons (localTail pψ (υ ⧺ χ)) β)
        (renameLocal (localCons (localTail pχ υ) β) e) := by
  rw [← renameLocal_comp]
  congr 1
  ext γ x
  cases x with
  | here i => rfl
  | there x =>
      exact congrArg ListSlotAt.there (localTail_append pχ pψ x)

private def extendPassiveRen {C : Carrier} {χ ψ ω base : Shape C}
    (pψ : ProperSpine ψ) (pω : ProperSpine ω) :
    (base ⧺ χ) ⧺ ω →ʳ (base ⧺ (χ ⧺ ψ)) ⧺ ω :=
  localMapTail pω (localTail pψ (base ⧺ χ))

private theorem extendPassiveRen_cons {C : Carrier}
    {χ ψ ω base : Shape C}
    (pψ : ProperSpine ψ) (pω : ProperSpine ω) (β : C.Arity) :
    extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω ∷ β)
        (base := base) pψ (.cons pω β) =
      localCons
        (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
          (base := base) pψ pω)
        β := by
  unfold extendPassiveRen
  rw [localMapTail_cons]

private def passiveInsert {C : Carrier} {χ ψ ω : Shape C}
    (pψ : ProperSpine ψ) (pω : ProperSpine ω) :
    χ ⧺ ω →ʳ (χ ⧺ ψ) ⧺ ω :=
  localMapTail pω (localTail pψ χ)

private theorem localPrefix_extendPassive {C : Carrier}
    {χ ψ ω base : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    (pω : ProperSpine ω)
    {α : C.Arity} (x : χ ⧺ ω ∋ α) :
    extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω) (base := base) pψ pω
        (localPrefix (ProperSpine.append pχ pω) base x)
      =
    localPrefix (ProperSpine.append (ProperSpine.append pχ pψ) pω)
        base (passiveInsert pψ pω x) := by
  unfold extendPassiveRen
  rcases ProperSpine.coverEq pω χ x with ⟨xω, rfl⟩ | ⟨xχ, rfl⟩
  · unfold passiveInsert
    have hleft :
        localPrefix (ProperSpine.append pχ pω) base
            ((ProperSpine.inr pω χ) xω) =
          localPrefix pω (base ⧺ χ) xω :=
      ProperSpine.append_inr_inr pχ pω base xω
    rw [hleft]
    rw [localMapTail_prefix]
    have hpass :
        localMapTail pω (localTail pψ χ)
            ((ProperSpine.inr pω χ) xω) =
          (ProperSpine.inr pω (χ ⧺ ψ)) xω :=
      localMapTail_prefix pω (localTail pψ χ) xω
    rw [hpass]
    have hright :
        localPrefix (ProperSpine.append (ProperSpine.append pχ pψ) pω)
            base ((ProperSpine.inr pω (χ ⧺ ψ)) xω) =
          localPrefix pω (base ⧺ (χ ⧺ ψ)) xω :=
      ProperSpine.append_inr_inr (ProperSpine.append pχ pψ) pω base xω
    rw [hright]
  · unfold passiveInsert
    have hleft :
        localPrefix (ProperSpine.append pχ pω) base
            ((ProperSpine.inl pω χ) xχ) =
          localTail pω (base ⧺ χ) (localPrefix pχ base xχ) :=
      ProperSpine.append_inr_inl pχ pω base xχ
    rw [hleft]
    rw [localMapTail_tail]
    have hpass :
        localMapTail pω (localTail pψ χ)
            ((ProperSpine.inl pω χ) xχ) =
          localTail pω (χ ⧺ ψ) (localTail pψ χ xχ) :=
      localMapTail_tail pω (localTail pψ χ) xχ
    rw [hpass]
    rw [← localPrefix_append_left pχ pψ (υ := base) xχ]
    have hright :
        localPrefix (ProperSpine.append (ProperSpine.append pχ pψ) pω)
            base (localTail pω (χ ⧺ ψ) (localTail pψ χ xχ)) =
          localTail pω (base ⧺ (χ ⧺ ψ))
            (localPrefix (ProperSpine.append pχ pψ) base
              (localTail pψ χ xχ)) :=
      ProperSpine.append_inr_inl (ProperSpine.append pχ pψ) pω base
        (localTail pψ χ xχ)
    rw [hright]

private theorem localTail_extendPassive {C : Carrier}
    {χ ψ ω base : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    (pω : ProperSpine ω)
    {α : C.Arity} (x : base ∋ α) :
    extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω) (base := base) pψ pω
        (localTail (ProperSpine.append pχ pω) base x)
      =
    localTail (ProperSpine.append (ProperSpine.append pχ pψ) pω)
        base x := by
  unfold extendPassiveRen
  rw [localTail_append pχ pω (υ := base) x]
  rw [localMapTail_tail]
  rw [← localTail_append pχ pψ (υ := base) x]
  rw [localTail_append (ProperSpine.append pχ pψ) pω
    (υ := base) x]

private theorem renameLocal_extendPassiveAtFiller {C : Carrier}
    {Γ χ ψ ω υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ)
    (pω : ProperSpine ω) {β : C.Arity}
    (e : ScopedExpr Γ (υ ∷ β)) :
    renameLocal
        (localCons
          (localTail (ProperSpine.append (ProperSpine.append pχ pψ) pω) υ)
          β)
        e =
      renameLocal
        (localCons
          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω) (base := υ)
            pψ pω)
          β)
        (renameLocal
          (localCons (localTail (ProperSpine.append pχ pω) υ) β)
          e) := by
  rw [← renameLocal_comp]
  congr 1
  ext γ x
  cases x with
  | here i => rfl
  | there x =>
      exact congrArg ListSlotAt.there
        (localTail_extendPassive pχ pψ pω (base := υ) x).symm

/-! ## Local renaming and one-binder instantiation -/

/-- Argument-descent facade for one-binder instantiation.

When we recurse through the arguments of an application whose local context is
`(υ ∷ α) ⧺ χ`, the argument lives in `((υ ∷ α) ⧺ χ) ∷ β`.  This is
definitionally the same shape as `(υ ∷ α) ⧺ (χ ∷ β)`, but this facade states
the argument-shaped version directly.  That keeps recursive proof calls visibly
structural instead of asking Lean to rediscover the reassociation each time. -/
private def instOneAtUnder {C : Carrier} {Γ χ υ : Shape C}
    (pχ : ProperSpine χ) (α : C.Arity)
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    {β : C.Arity}
    (e : ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ β)) :
    ScopedExpr Γ ((υ ⧺ χ) ∷ β) :=
  instOneAt (.cons pχ β) υ α fill e

/-- Renaming the older local tail commutes with one-binder instantiation.

The proof follows the four semantic head cases for the source local context:
free head, passive-prefix local head, older-tail local head, and active local
head.  The first three cases preserve the head and use argument recursion.  In
the active case, the selected filler is smaller in arity, so we use the same
theorem recursively at that smaller active binder. -/
theorem renameLocal_instOneAt {C : Carrier} {Γ : Shape C} :
    {χ υ ν : Shape C} → (pχ : ProperSpine χ) → (ρ : υ →ʳ ν) →
    (α : C.Arity) →
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity)) →
    (e : ScopedExpr Γ ((υ ∷ α) ⧺ χ)) →
    renameLocal (localMapTail pχ ρ) (instOneAt pχ υ α fill e) =
      instOneAt pχ ν α
        (fun i => renameLocal (localCons ρ i.arity) (fill i))
        (renameLocal (localMapTail pχ (localCons ρ α)) e)
  | χ, υ, ν, pχ, ρ, α, fill, .ap head args => by
      let fill' : (i : C.Binder α) → ScopedExpr Γ (ν ∷ i.arity) :=
        fun i => renameLocal (localCons ρ i.arity) (fill i)
      have hargs : ∀ j,
          renameLocal (localCons (localMapTail pχ ρ) j.arity)
              (instOneAtUnder pχ α fill (args j)) =
            instOneAtUnder pχ α fill'
              (renameLocal
                (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                (args j)) := by
        intro j
        unfold instOneAtUnder
        have h := renameLocal_instOneAt (.cons pχ j.arity) ρ α fill (args j)
        rw [localMapTail_cons, localMapTail_cons] at h
        exact h
      cases head
      · rename_i x
        -- Free head: instantiate below the same free head and recurse through
        -- every binder argument.
        rw [instOneAt_freeHead pχ fill x args]
        change
          .ap (.free x)
              (fun j =>
                renameLocal (localCons (localMapTail pχ ρ) j.arity)
                  (instOneAtUnder pχ α fill (args j))) =
            instOneAt pχ ν α fill'
              (.ap (.free x)
                (fun j =>
                  renameLocal
                    (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                    (args j)))
        rw [instOneAt_freeHead pχ fill' x
          (fun j =>
            renameLocal
              (localCons (localMapTail pχ (localCons ρ α)) j.arity)
              (args j))]
        exact ap_args_congr (.free x) hargs
      · rename_i x
        obtain ⟨site, rfl⟩ := LocalSite.cover pχ α x
        cases site with
        | pre xχ =>
            -- Passive-prefix local head: it is newer than the active binder,
            -- so it is preserved by instantiation and by tail renaming.
            rw [instOneAt_preSiteHead pχ fill xχ args]
            change
              .ap (.local (localMapTail pχ ρ (localPrefix pχ υ xχ)))
                  (fun j =>
                    renameLocal (localCons (localMapTail pχ ρ) j.arity)
                      (instOneAtUnder pχ α fill (args j))) =
                instOneAt pχ ν α fill'
                  (.ap
                    (.local
                      (localMapTail pχ (localCons ρ α)
                        (LocalSite.embedSource pχ (LocalSite.pre xχ))))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [localMapTail_prefix]
            rw [LocalSite.mapTail_embedSource]
            change
              .ap (.local (localPrefix pχ ν xχ))
                  (fun j =>
                    renameLocal (localCons (localMapTail pχ ρ) j.arity)
                      (instOneAtUnder pχ α fill (args j))) =
                instOneAt pχ ν α fill'
                  (.ap (.local (LocalSite.embedSource pχ (LocalSite.pre xχ)))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [instOneAt_preSiteHead pχ fill' xχ
              (fun j =>
                renameLocal
                  (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                  (args j))]
            exact ap_args_congr (.local (localPrefix pχ ν xχ)) hargs
        | tail xυ =>
            -- Older-tail local head: it survives instantiation, but the
            -- surrounding local renaming acts on the selected tail slot.
            rw [instOneAt_tailSiteHead pχ fill xυ args]
            change
              .ap (.local (localMapTail pχ ρ (localTail pχ υ xυ)))
                  (fun j =>
                    renameLocal (localCons (localMapTail pχ ρ) j.arity)
                      (instOneAtUnder pχ α fill (args j))) =
                instOneAt pχ ν α fill'
                  (.ap
                    (.local
                      (localMapTail pχ (localCons ρ α)
                        (LocalSite.embedSource pχ (LocalSite.tail xυ))))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [localMapTail_tail]
            rw [LocalSite.mapTail_embedSource]
            change
              .ap (.local (localTail pχ ν (ρ xυ)))
                  (fun j =>
                    renameLocal (localCons (localMapTail pχ ρ) j.arity)
                      (instOneAtUnder pχ α fill (args j))) =
                instOneAt pχ ν α fill'
                  (.ap (.local (LocalSite.embedSource pχ (LocalSite.tail (ρ xυ))))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [instOneAt_tailSiteHead pχ fill' (ρ xυ)
              (fun j =>
                renameLocal
                  (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                  (args j))]
            exact ap_args_congr (.local (localTail pχ ν (ρ xυ))) hargs
        | active i =>
            -- Active local head: instantiation fires the selected filler.  We
            -- then commute the outer renaming through that smaller
            -- one-binder instantiation, and finish by the active-filler
            -- renaming equation plus argument recursion.
            rw [instOneAt_activeSiteHead pχ fill i args]
            change
              renameLocal (localMapTail pχ ρ)
                (instOneAt .nil (υ ⧺ χ) i.arity
                  (fun j => instOneAtUnder pχ α fill (args j))
                  (renameLocal (localCons (localTail pχ υ) i.arity)
                    (fill i))) =
                instOneAt pχ ν α fill'
                  (.ap
                    (.local
                      (localMapTail pχ (localCons ρ α)
                        (LocalSite.embedSource pχ (LocalSite.active i))))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            change
              renameLocal (localMapTail .nil (localMapTail pχ ρ))
                (instOneAt .nil (υ ⧺ χ) i.arity
                  (fun j => instOneAtUnder pχ α fill (args j))
                  (renameLocal (localCons (localTail pχ υ) i.arity)
                    (fill i))) =
                instOneAt pχ ν α fill'
                  (.ap
                    (.local
                      (localMapTail pχ (localCons ρ α)
                        (LocalSite.embedSource pχ (LocalSite.active i))))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [renameLocal_instOneAt .nil (localMapTail pχ ρ)
              i.arity
              (fun j => instOneAtUnder pχ α fill (args j))
              (renameLocal (localCons (localTail pχ υ) i.arity) (fill i))]
            rw [LocalSite.mapTail_embedSource]
            change
              instOneAt .nil (ν ⧺ χ) i.arity
                  (fun j =>
                    renameLocal (localCons (localMapTail pχ ρ) j.arity)
                      (instOneAtUnder pχ α fill (args j)))
                  (renameLocal (localCons (localMapTail pχ ρ) i.arity)
                    (renameLocal (localCons (localTail pχ υ) i.arity)
                      (fill i))) =
                instOneAt pχ ν α fill'
                  (.ap (.local (LocalSite.embedSource pχ (LocalSite.active i)))
                    (fun j =>
                      renameLocal
                        (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                        (args j)))
            rw [instOneAt_activeSiteHead pχ fill' i
              (fun j =>
                renameLocal
                  (localCons (localMapTail pχ (localCons ρ α)) j.arity)
                  (args j))]
            exact instOneAt_congr .nil hargs
              (renameLocal_activeFiller pχ ρ (fill i))
termination_by χ υ ν _ _ α _ e =>
  (α, (⟨(υ ∷ α) ⧺ χ, e⟩ : Σ τ : Shape C, ScopedExpr Γ τ))
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ ⟨i, rfl⟩
      | exact Prod.Lex.right _ (Subterm.of_arg_ext _ _ _)

/-! ## Passive extension and one-binder instantiation -/

private theorem instOneAt_extendPassiveAt {C : Carrier} {Γ : Shape C} :
    {χ ψ ω υ : Shape C} →
    (pχ : ProperSpine χ) → (pψ : ProperSpine ψ) →
    (pω : ProperSpine ω) → (α : C.Arity) →
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity)) →
    (e : ScopedExpr Γ (((υ ∷ α) ⧺ χ) ⧺ ω)) →
    instOneAt (ProperSpine.append (ProperSpine.append pχ pψ) pω) υ α fill
        (renameLocal
          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
            (base := υ ∷ α) pψ pω) e)
      =
      renameLocal
        (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
          (base := υ) pψ pω)
        (instOneAt (ProperSpine.append pχ pω) υ α fill e)
  | χ, ψ, ω, υ, pχ, pψ, pω, α, fill, .ap head args => by
      have hargs : ∀ j,
          instOneAt
              (ProperSpine.append (ProperSpine.append pχ pψ)
                (.cons pω j.arity))
              υ α fill
              (renameLocal
                (localCons
                  (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                    (base := υ ∷ α) pψ pω)
                  j.arity)
                (args j))
            =
            renameLocal
              (localCons
                (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                  (base := υ) pψ pω)
                j.arity)
              (instOneAt (ProperSpine.append pχ (.cons pω j.arity))
                υ α fill (args j)) := by
        intro j
        have h :=
          instOneAt_extendPassiveAt pχ pψ (.cons pω j.arity) α fill
            (args j)
        rw [extendPassiveRen_cons, extendPassiveRen_cons] at h
        exact h
      cases head
      · rename_i x
        -- Free head: passive extension only changes the local telescope, so
        -- both routes preserve the head and recurse through arguments.
        change
          instOneAt (ProperSpine.append (ProperSpine.append pχ pψ) pω)
              υ α fill
              (.ap (.free x)
                (fun j =>
                  renameLocal
                    (localCons
                      (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                        (base := υ ∷ α) pψ pω)
                      j.arity)
                    (args j))) =
            renameLocal
              (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                (base := υ) pψ pω)
              (instOneAt (ProperSpine.append pχ pω) υ α fill
                (.ap (.free x) args))
        rw [instOneAt_freeHead
          (ProperSpine.append (ProperSpine.append pχ pψ) pω)
          fill x
          (fun j =>
            renameLocal
              (localCons
                (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                  (base := υ ∷ α) pψ pω)
                j.arity)
              (args j))]
        rw [instOneAt_freeHead (ProperSpine.append pχ pω) fill x args]
        exact ap_args_congr (.free x) hargs
      · rename_i x
        obtain ⟨site, rfl⟩ :=
          LocalSite.cover (ProperSpine.append pχ pω) α x
        cases site with
        | pre y =>
            -- Passive-prefix head: the old passive slot is transported by
            -- `passiveInsert`, then preserved by both instantiations.
            change
              instOneAt (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                  υ α fill
                  (.ap
                    (.local
                      (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                        (base := υ ∷ α) pψ pω
                        (localPrefix (ProperSpine.append pχ pω)
                          (υ ∷ α) y)))
                    (fun j =>
                      renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j))) =
                renameLocal
                  (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                    (base := υ) pψ pω)
                  (instOneAt (ProperSpine.append pχ pω) υ α fill
                    (.ap
                      (.local
                        (localPrefix (ProperSpine.append pχ pω)
                          (υ ∷ α) y))
                      args))
            rw [localPrefix_extendPassive pχ pψ pω (base := υ ∷ α) y]
            rw [instOneAt_preHead
              (ProperSpine.append (ProperSpine.append pχ pψ) pω)
              fill (passiveInsert pψ pω y)
              (fun j =>
                renameLocal
                  (localCons
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ ∷ α) pψ pω)
                    j.arity)
                  (args j))]
            rw [instOneAt_preHead (ProperSpine.append pχ pω) fill y args]
            change
              ScopedExpr.ap
                  (.local
                    (localPrefix
                      (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                      υ (passiveInsert pψ pω y)))
                  (fun j =>
                    instOneAt
                      (ProperSpine.append (ProperSpine.append pχ pψ)
                        (.cons pω j.arity))
                      υ α fill
                      (renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j))) =
                ScopedExpr.ap
                  (.local
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ) pψ pω
                      (localPrefix (ProperSpine.append pχ pω) υ y)))
                  (fun j =>
                    renameLocal
                      (localCons
                        (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                          (base := υ) pψ pω)
                        j.arity)
                      (instOneAt (ProperSpine.append pχ (.cons pω j.arity))
                        υ α fill (args j)))
            rw [localPrefix_extendPassive pχ pψ pω (base := υ) y]
            exact ap_args_congr
              (.local
                (localPrefix
                  (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                  υ (passiveInsert pψ pω y)))
              hargs
        | tail xυ =>
            -- Older-tail head: inserting passive binders leaves it an
            -- older-tail head.
            change
              instOneAt (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                  υ α fill
                  (.ap
                    (.local
                      (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                        (base := υ ∷ α) pψ pω
                        (localTail (ProperSpine.append pχ pω)
                          (υ ∷ α) (.there xυ))))
                    (fun j =>
                      renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j))) =
                renameLocal
                  (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                    (base := υ) pψ pω)
                  (instOneAt (ProperSpine.append pχ pω) υ α fill
                    (.ap
                      (.local
                        (localTail (ProperSpine.append pχ pω)
                          (υ ∷ α) (.there xυ)))
                      args))
            rw [localTail_extendPassive pχ pψ pω (base := υ ∷ α)
              (.there xυ)]
            rw [instOneAt_tailHead
              (ProperSpine.append (ProperSpine.append pχ pψ) pω)
              fill xυ
              (fun j =>
                renameLocal
                  (localCons
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ ∷ α) pψ pω)
                    j.arity)
                  (args j))]
            rw [instOneAt_tailHead (ProperSpine.append pχ pω) fill xυ args]
            change
              ScopedExpr.ap
                  (.local
                    (localTail
                      (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                      υ xυ))
                  (fun j =>
                    instOneAt
                      (ProperSpine.append (ProperSpine.append pχ pψ)
                        (.cons pω j.arity))
                      υ α fill
                      (renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j))) =
                ScopedExpr.ap
                  (.local
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ) pψ pω
                      (localTail (ProperSpine.append pχ pω) υ xυ)))
                  (fun j =>
                    renameLocal
                      (localCons
                        (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                          (base := υ) pψ pω)
                        j.arity)
                      (instOneAt (ProperSpine.append pχ (.cons pω j.arity))
                        υ α fill (args j)))
            rw [localTail_extendPassive pχ pψ pω (base := υ) xυ]
            exact ap_args_congr
              (.local
                (localTail
                  (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                  υ xυ))
              hargs
        | active i =>
            -- Active head: after both routes fire the same filler, the
            -- remaining equality is renaming-through-instantiation for the
            -- smaller active arity plus passive-extension of the filler
            -- weakening.
            change
              instOneAt (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                  υ α fill
                  (.ap
                    (.local
                      (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                        (base := υ ∷ α) pψ pω
                        (localTail (ProperSpine.append pχ pω)
                          (υ ∷ α) (.here i))))
                    (fun j =>
                      renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j))) =
                renameLocal
                  (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                    (base := υ) pψ pω)
                  (instOneAt (ProperSpine.append pχ pω) υ α fill
                    (.ap
                      (.local
                        (localTail (ProperSpine.append pχ pω)
                          (υ ∷ α) (.here i)))
                      args))
            rw [localTail_extendPassive pχ pψ pω (base := υ ∷ α)
              (.here i)]
            rw [instOneAt_activeHead
              (ProperSpine.append (ProperSpine.append pχ pψ) pω)
              fill i
              (fun j =>
                renameLocal
                  (localCons
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ ∷ α) pψ pω)
                    j.arity)
                  (args j))]
            rw [instOneAt_activeHead (ProperSpine.append pχ pω) fill i args]
            change
              instOneAt .nil (((υ ⧺ χ) ⧺ ψ) ⧺ ω) i.arity
                  (fun j =>
                    instOneAt
                      (ProperSpine.append (ProperSpine.append pχ pψ)
                        (.cons pω j.arity))
                      υ α fill
                      (renameLocal
                        (localCons
                          (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                            (base := υ ∷ α) pψ pω)
                          j.arity)
                        (args j)))
                  (renameLocal
                    (localCons
                      (localTail
                        (ProperSpine.append (ProperSpine.append pχ pψ) pω)
                        υ)
                      i.arity)
                    (fill i)) =
                renameLocal
                  (localMapTail .nil
                    (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                      (base := υ) pψ pω))
                  (instOneAt .nil ((υ ⧺ χ) ⧺ ω) i.arity
                    (fun j =>
                      instOneAt (ProperSpine.append pχ (.cons pω j.arity))
                        υ α fill (args j))
                    (renameLocal
                      (localCons
                        (localTail (ProperSpine.append pχ pω) υ)
                        i.arity)
                      (fill i)))
            rw [renameLocal_instOneAt .nil
              (extendPassiveRen (χ := χ) (ψ := ψ) (ω := ω)
                (base := υ) pψ pω)
              i.arity
              (fun j =>
                instOneAt (ProperSpine.append pχ (.cons pω j.arity))
                  υ α fill (args j))
              (renameLocal
                (localCons (localTail (ProperSpine.append pχ pω) υ)
                  i.arity)
                (fill i))]
            exact instOneAt_congr .nil hargs
              (renameLocal_extendPassiveAtFiller pχ pψ pω (fill i))
termination_by χ ψ ω υ _ _ _ α _ e =>
  (α, (⟨((υ ∷ α) ⧺ χ) ⧺ ω, e⟩ :
    Σ τ : Shape C, ScopedExpr Γ τ))
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ ⟨i, rfl⟩
      | exact Prod.Lex.right _ (Subterm.of_arg_ext _ _ _)

private theorem instOneAt_extendPassive {C : Carrier} {Γ χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ) (α : C.Arity)
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    (e : ScopedExpr Γ ((υ ∷ α) ⧺ χ)) :
    instOneAt (ProperSpine.append pχ pψ) υ α fill
        (renameLocal (localTail pψ ((υ ∷ α) ⧺ χ)) e)
      =
      renameLocal (localTail pψ (υ ⧺ χ))
        (instOneAt pχ υ α fill e) := by
  exact instOneAt_extendPassiveAt pχ pψ .nil α fill e

private theorem instOneAt_extendPassiveUnder {C : Carrier} {Γ χ ψ υ : Shape C}
    (pχ : ProperSpine χ) (pψ : ProperSpine ψ) (α : C.Arity)
    (fill : (i : C.Binder α) → ScopedExpr Γ (υ ∷ i.arity))
    {β : C.Arity}
    (e : ScopedExpr Γ (((υ ∷ α) ⧺ χ) ∷ β)) :
    instOneAt (.cons (ProperSpine.append pχ pψ) β) υ α fill
        (renameLocal (localCons (localTail pψ ((υ ∷ α) ⧺ χ)) β) e)
      =
      renameLocal (localCons (localTail pψ (υ ⧺ χ)) β)
        (instOneAtUnder pχ α fill e) := by
  unfold instOneAtUnder
  have h := instOneAt_extendPassiveAt pχ pψ (.cons .nil β) α fill e
  rw [extendPassiveRen_cons, extendPassiveRen_cons] at h
  exact h

end ScopedExpr
