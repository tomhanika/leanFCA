/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Scale.Standard
public import FCA.ScaleMeasure.Hierarchy
public import FCA.Order.ClosureSubsystem.Reconstruction

/-!
# The scale-hierarchy does not determine the concept lattice

The scale-hierarchy of a context depends only on its concept lattice. The converse fails:
adjoining a new greatest element to a concept lattice and adjoining a new least element yield
isomorphic scale-hierarchies, since in both cases exactly one closed set can be added or removed
freely. For the four-element Boolean lattice the two extended lattices are not isomorphic.

What the scale-hierarchy does determine is described in
`FCA.Order.ClosureSubsystem.Reconstruction`: the proper extents up to bijections preserving
comparability and intersections of incomparable extents. The example above is an instance,
since a new greatest and a new least proper extent are both comparable to every other extent.
For coatomistic concept lattices of contexts with finitely many objects this invariant is the
concept lattice itself.

## Main definitions

* `FCA.adjoinTop r`, `FCA.adjoinBot r`: contexts whose concept lattices are the concept lattice
  of `r` with a new greatest, respectively least, element.
* `FCA.ClosureSubsystem.adjoinTopIso`, `FCA.ClosureSubsystem.adjoinBotIso`: the lattice of
  closure systems of extents of either context is the product of that of `r` with the
  two-element chain.

## Main results

* `FCA.ClosureSubsystem.adjoinTopAdjoinBotIso`: `adjoinTop r` and `adjoinBot r` have isomorphic
  scale-hierarchies.
* `FCA.exists_scaleHierarchy_orderIso_and_isEmpty_concept_orderIso`: there are two contexts on
  three objects with isomorphic scale-hierarchies and non-isomorphic concept lattices.
* `FCA.nonempty_concept_orderIso_of_scaleHierarchy_orderIso`: if the concept lattice of a
  context with finitely many objects is coatomistic, every context with an isomorphic
  scale-hierarchy has an isomorphic concept lattice.

## References

* [N. Caspard, B. Monjardet, *The lattices of closure systems, closure operators, and
  implicational systems on a finite set: a survey*][caspard2003]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β : Type*} {r : α → β → Prop}

/-! ### Adjoining a greatest element -/

/-- The context `r` with a new object without attributes and a new attribute shared by all old
objects. Its concept lattice is that of `r` with a new greatest element. -/
def adjoinTop (r : α → β → Prop) : Option α → Option β → Prop
  | none, _ => False
  | some _, none => True
  | some a, some b => r a b

@[simp]
theorem adjoinTop_none (b : Option β) : adjoinTop r none b ↔ False := by
  cases b <;> rfl

@[simp]
theorem adjoinTop_some_none (a : α) : adjoinTop r (some a) none ↔ True :=
  Iff.rfl

@[simp]
theorem adjoinTop_some_some (a : α) (b : β) : adjoinTop r (some a) (some b) ↔ r a b :=
  Iff.rfl

theorem preimage_some_lowerPolar_adjoinTop (T : Set (Option β)) :
    some ⁻¹' lowerPolar (adjoinTop r) T = lowerPolar r (some ⁻¹' T) := by
  ext a
  simp only [mem_preimage, mem_lowerPolar_iff]
  refine ⟨fun h b hb ↦ h hb, fun h b hb ↦ ?_⟩
  cases b with
  | none => trivial
  | some b => exact h hb

/-- A set not containing the new object is determined by its old objects. -/
theorem image_some_preimage_some {X : Set (Option α)} (h : none ∉ X) :
    some '' (some ⁻¹' X) = X := by
  ext x
  cases x <;> simp [h]

/-- The extents of `adjoinTop r` are the whole object set and the extents of `r`. -/
theorem isExtent_adjoinTop_iff {X : Set (Option α)} :
    IsExtent (adjoinTop r) X ↔ X = univ ∨ none ∉ X ∧ IsExtent r (some ⁻¹' X) := by
  constructor
  · rintro ⟨T, rfl⟩
    rcases T.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
    · exact .inl (lowerPolar_empty _)
    · refine .inr ⟨fun h ↦ (adjoinTop_none b).1 (h hb), ?_⟩
      rw [preimage_some_lowerPolar_adjoinTop]
      exact isExtent_lowerPolar
  · rintro (rfl | ⟨hX, T, hT⟩)
    · exact .univ
    · refine ⟨insert none (some '' T), ?_⟩
      rw [← image_some_preimage_some hX, ← hT]
      ext x
      cases x with
      | none =>
        exact ⟨fun h ↦ ((adjoinTop_none none).1 (h (mem_insert _ _))).elim, fun h ↦ by simp at h⟩
      | some a => simp [mem_lowerPolar_iff]

/-- The old objects form an extent of `adjoinTop r`. -/
theorem isExtent_adjoinTop_range_some : IsExtent (adjoinTop r) (range some) :=
  isExtent_adjoinTop_iff.2 (.inr ⟨by simp, by simp⟩)

/-- The greatest element of the concept lattice of `adjoinTop r` is join-irreducible. -/
theorem eq_top_or_eq_top_of_sup_eq_top_adjoinTop {c d : Concept (Option α) (Option β) (adjoinTop r)}
    (h : c ⊔ d = ⊤) : c = ⊤ ∨ d = ⊤ := by
  by_contra! hne
  have key : ∀ e : Concept (Option α) (Option β) (adjoinTop r), e ≠ ⊤ →
      e ≤ .ofIsExtent _ _ isExtent_adjoinTop_range_some := by
    intro e he
    rw [← Concept.extent_subset_extent_iff]
    rcases isExtent_adjoinTop_iff.1 e.isExtent_extent with h' | h'
    · exact absurd (Concept.extent_injective (h'.trans Concept.extent_top.symm)) he
    · rintro (_ | a) ha
      · exact absurd ha h'.1
      · exact mem_range_self a
  have hle := sup_le (key c hne.1) (key d hne.2)
  rw [h, ← Concept.extent_subset_extent_iff, Concept.extent_top] at hle
  simpa using hle (mem_univ none)

/-! ### Adjoining a least element -/

/-- The context `r` with a new object having all old attributes and a new attribute without
objects. Its concept lattice is that of `r` with a new least element. -/
def adjoinBot (r : α → β → Prop) : Option α → Option β → Prop
  | _, none => False
  | none, some _ => True
  | some a, some b => r a b

@[simp]
theorem adjoinBot_none_right (a : Option α) : adjoinBot r a none ↔ False := by
  cases a <;> rfl

@[simp]
theorem adjoinBot_none_some (b : β) : adjoinBot r none (some b) ↔ True :=
  Iff.rfl

@[simp]
theorem adjoinBot_some_some (a : α) (b : β) : adjoinBot r (some a) (some b) ↔ r a b :=
  Iff.rfl

/-- A set containing the new object is determined by its old objects. -/
theorem insert_none_image_some_preimage_some {X : Set (Option α)} (h : none ∈ X) :
    insert none (some '' (some ⁻¹' X)) = X := by
  ext x
  cases x <;> simp [h]

theorem preimage_some_insert_none_image_some (A : Set α) :
    some ⁻¹' insert none (some '' A) = A := by
  ext a
  simp

/-- The extents of `adjoinBot r` are the empty set and the extents of `r` together with the new
object. -/
theorem isExtent_adjoinBot_iff {X : Set (Option α)} :
    IsExtent (adjoinBot r) X ↔ X = ∅ ∨ none ∈ X ∧ IsExtent r (some ⁻¹' X) := by
  constructor
  · rintro ⟨T, rfl⟩
    by_cases hT : none ∈ T
    · exact .inl (eq_empty_of_forall_notMem fun x hx ↦ (adjoinBot_none_right x).1 (hx hT))
    · have hnone : none ∈ lowerPolar (adjoinBot r) T := by
        rintro (_ | b) hb
        exacts [absurd hb hT, trivial]
      refine .inr ⟨hnone, ⟨some ⁻¹' T, ?_⟩⟩
      ext a
      simp only [mem_preimage, mem_lowerPolar_iff]
      refine ⟨fun h b hb ↦ ?_, fun h b hb ↦ h hb⟩
      cases b with
      | none => exact absurd hb hT
      | some b => exact h hb
  · rintro (rfl | ⟨hX, T, hT⟩)
    · exact ⟨{none}, eq_empty_of_forall_notMem fun x hx ↦
        (adjoinBot_none_right x).1 (hx (mem_singleton _))⟩
    · refine ⟨some '' T, ?_⟩
      rw [← insert_none_image_some_preimage_some hX, ← hT]
      ext x
      cases x <;> simp [mem_lowerPolar_iff]

theorem isExtent_adjoinBot_insert_none {A : Set α} (hA : IsExtent r A) :
    IsExtent (adjoinBot r) (insert none (some '' A)) :=
  isExtent_adjoinBot_iff.2 (.inr ⟨mem_insert _ _, by rwa [preimage_some_insert_none_image_some]⟩)

namespace ClosureSubsystem

/-! ### The scale-hierarchies of the extended contexts -/

/-- The closure systems of extents of `adjoinTop r` are the closure systems of extents of `r`
together with the choice whether the set of old objects is closed. -/
def adjoinTopIso (r : α → β → Prop) :
    ClosureSubsystem (IsExtent (adjoinTop r)) ≃o ClosureSubsystem (IsExtent r) × Prop :=
  Equiv.toOrderIso
    { toFun 𝒜 :=
        (⟨{A | ∃ X ∈ 𝒜, some ⁻¹' X = A}, fun S hS ↦ by
            choose! f hf hfS using hS
            refine ⟨⋂₀ (f '' S), 𝒜.sInter_mem (forall_mem_image.2 hf), ?_⟩
            rw [sInter_image, preimage_iInter₂, sInter_eq_biInter]
            exact iInter₂_congr hfS,
          by
            rintro _ ⟨X, hX, rfl⟩
            rcases isExtent_adjoinTop_iff.1 (𝒜.isExtent hX) with rfl | h
            · exact .univ
            · exact h.2⟩, range some ∈ 𝒜)
      invFun p :=
        ⟨{X | X = univ ∨ none ∉ X ∧ some ⁻¹' X ∈ p.1 ∧ (some ⁻¹' X = univ → p.2)}, fun S hS ↦ by
            by_cases hall : ∀ X ∈ S, X = univ
            · exact .inl (sInter_eq_univ.2 hall)
            · push Not at hall
              obtain ⟨X₀, hX₀, hne⟩ := hall
              have h₀ := (hS hX₀).resolve_left hne
              refine .inr ⟨fun h ↦ h₀.1 (h X₀ hX₀), ?_, fun h ↦ h₀.2.2 ?_⟩
              · rw [sInter_eq_biInter, preimage_iInter₂, ← sInter_image]
                refine p.1.sInter_mem (forall_mem_image.2 fun X hX ↦ ?_)
                rcases hS hX with rfl | h
                · exact p.1.univ_mem
                · exact h.2.1
              · exact eq_univ_of_univ_subset
                  (h ▸ preimage_mono (sInter_subset_of_mem hX₀)),
          by
            rintro X (rfl | h)
            · exact .univ
            · exact isExtent_adjoinTop_iff.2 (.inr ⟨h.1, p.1.isExtent h.2.1⟩)⟩
      left_inv 𝒜 := by
        ext X
        simp only [mem_carrier, mem_mk, mem_ofPred]
        constructor
        · rintro (rfl | ⟨hX, ⟨Y, hY, hYX⟩, hr⟩)
          · exact 𝒜.univ_mem
          · rcases isExtent_adjoinTop_iff.1 (𝒜.isExtent hY) with rfl | h
            · have := hr hYX.symm
              rwa [← image_some_preimage_some hX, ← hYX, preimage_univ, image_univ]
            · rwa [← image_some_preimage_some hX, ← hYX, image_some_preimage_some h.1]
        · intro hX
          rcases isExtent_adjoinTop_iff.1 (𝒜.isExtent hX) with rfl | h
          · exact .inl rfl
          · refine .inr ⟨h.1, ⟨X, hX, rfl⟩, fun huniv ↦ ?_⟩
            rwa [← image_univ, ← huniv, image_some_preimage_some h.1]
      right_inv p := by
        refine Prod.ext (ClosureSubsystem.ext (Set.ext fun A ↦ ?_)) (propext ?_)
        · simp only [mem_ofPred, mem_mk]
          constructor
          · rintro ⟨X, rfl | h, rfl⟩
            · exact p.1.univ_mem
            · exact h.2.1
          · intro hA
            have hA' : A ∈ p.1 := hA
            by_cases huniv : A = univ
            · exact ⟨univ, .inl rfl, by rw [huniv, preimage_univ]⟩
            · refine ⟨some '' A, .inr ⟨by simp, ?_, ?_⟩, ?_⟩ <;>
                simp [preimage_image_eq _ (Option.some_injective α), hA', huniv]
        · simp only [mem_mk, mem_ofPred]
          constructor
          · rintro (h | h)
            · exact absurd (h ▸ mem_univ none : none ∈ range some) (by simp)
            · exact h.2.2 (by simp)
          · exact fun h ↦ .inr ⟨by simp, by simpa using p.1.univ_mem, fun _ ↦ h⟩ }
    (fun 𝒜 ℬ h ↦ ⟨le_def.2 fun _ ⟨X, hX, hXA⟩ ↦ ⟨X, le_def.1 h hX, hXA⟩, fun h' ↦ le_def.1 h h'⟩)
    (fun p q h ↦ le_def.2 fun _ hX ↦ hX.imp_right fun hX ↦
      ⟨hX.1, le_def.1 h.1 hX.2.1, fun h' ↦ h.2 (hX.2.2 h')⟩)

/-- The closure systems of extents of `adjoinBot r` are the closure systems of extents of `r`
together with the choice whether the empty set is closed. -/
def adjoinBotIso (r : α → β → Prop) :
    ClosureSubsystem (IsExtent (adjoinBot r)) ≃o ClosureSubsystem (IsExtent r) × Prop :=
  Equiv.toOrderIso
    { toFun 𝒜 :=
        (⟨{A | insert none (some '' A) ∈ 𝒜}, fun S hS ↦ by
            have : insert none (some '' ⋂₀ S) = ⋂₀ ((fun A ↦ insert none (some '' A)) '' S) := by
              ext x
              cases x <;> simp
            rw [mem_ofPred, this]
            exact 𝒜.sInter_mem (forall_mem_image.2 hS),
          fun A hA ↦ by
            rcases isExtent_adjoinBot_iff.1 (𝒜.isExtent hA) with h | h
            · exact absurd (h ▸ mem_insert none _) (notMem_empty _)
            · simpa [preimage_some_insert_none_image_some] using h.2⟩, ∅ ∈ 𝒜)
      invFun p :=
        ⟨{X | X = ∅ ∧ p.2 ∨ none ∈ X ∧ some ⁻¹' X ∈ p.1}, fun S hS ↦ by
            by_cases hempty : ∅ ∈ S
            · refine .inl ⟨subset_empty_iff.1 (sInter_subset_of_mem hempty), ?_⟩
              exact (hS hempty).elim (·.2) fun h ↦ absurd h.1 (notMem_empty _)
            · have hS' : ∀ X ∈ S, none ∈ X ∧ some ⁻¹' X ∈ p.1 := fun X hX ↦
                (hS hX).resolve_left fun h ↦ hempty (h.1 ▸ hX)
              refine .inr ⟨fun X hX ↦ (hS' X hX).1, ?_⟩
              rw [sInter_eq_biInter, preimage_iInter₂, ← sInter_image]
              exact p.1.sInter_mem (forall_mem_image.2 fun X hX ↦ (hS' X hX).2),
          by
            rintro X (h | h)
            · exact isExtent_adjoinBot_iff.2 (.inl h.1)
            · exact isExtent_adjoinBot_iff.2 (.inr ⟨h.1, p.1.isExtent h.2⟩)⟩
      left_inv 𝒜 := by
        ext X
        simp only [mem_carrier, mem_mk, mem_ofPred]
        constructor
        · rintro (⟨rfl, h⟩ | ⟨hX, h⟩)
          · exact h
          · rwa [insert_none_image_some_preimage_some hX] at h
        · intro hX
          rcases isExtent_adjoinBot_iff.1 (𝒜.isExtent hX) with rfl | h
          · exact .inl ⟨rfl, hX⟩
          · exact .inr ⟨h.1, by rwa [insert_none_image_some_preimage_some h.1]⟩
      right_inv p := by
        refine Prod.ext (ClosureSubsystem.ext (Set.ext fun A ↦ ?_)) (propext ?_)
        · change (_ = ∅ ∧ p.2 ∨ none ∈ insert none (some '' A) ∧
            some ⁻¹' insert none (some '' A) ∈ p.1) ↔ A ∈ p.1
          rw [preimage_some_insert_none_image_some]
          exact ⟨fun h ↦ h.elim (fun h ↦ absurd h.1 (insert_nonempty _ _).ne_empty) (·.2),
            fun h ↦ .inr ⟨mem_insert _ _, h⟩⟩
        · simp }
    (fun 𝒜 ℬ h ↦ ⟨le_def.2 fun _ hA ↦ le_def.1 h hA, fun h' ↦ le_def.1 h h'⟩)
    (fun p q h ↦ le_def.2 fun _ hX ↦ hX.imp (fun hX ↦ ⟨hX.1, h.2 hX.2⟩)
      fun hX ↦ ⟨hX.1, le_def.1 h.1 hX.2⟩)

/-- Adjoining a greatest element to a concept lattice and adjoining a least element yield
isomorphic lattices of closure systems of extents. -/
def adjoinTopAdjoinBotIso (r : α → β → Prop) :
    ClosureSubsystem (IsExtent (adjoinTop r)) ≃o ClosureSubsystem (IsExtent (adjoinBot r)) :=
  (adjoinTopIso r).trans (adjoinBotIso r).symm

end ClosureSubsystem

/-! ### The counterexample -/

/-- The concept lattices of `adjoinTop (· ≠ ·)` and `adjoinBot (· ≠ ·)` on a two-element set are
not isomorphic: only in the latter the greatest element is the join of two smaller ones. -/
theorem isEmpty_concept_adjoinTop_orderIso_adjoinBot :
    IsEmpty (Concept (Option Bool) (Option Bool) (adjoinTop (· ≠ ·)) ≃o
      Concept (Option Bool) (Option Bool) (adjoinBot (· ≠ ·))) := by
  refine ⟨fun e ↦ ?_⟩
  let c : Concept (Option Bool) (Option Bool) (adjoinBot (· ≠ ·)) :=
    .ofIsExtent _ _ (isExtent_adjoinBot_insert_none (isExtent_ne {true}))
  let d : Concept (Option Bool) (Option Bool) (adjoinBot (· ≠ ·)) :=
    .ofIsExtent _ _ (isExtent_adjoinBot_insert_none (isExtent_ne {false}))
  have hc : c ≠ ⊤ := fun h ↦ by
    have : some false ∈ c.extent := by rw [h, Concept.extent_top]; trivial
    simp [c] at this
  have hd : d ≠ ⊤ := fun h ↦ by
    have : some true ∈ d.extent := by rw [h, Concept.extent_top]; trivial
    simp [d] at this
  have hcd : c ⊔ d = ⊤ := by
    rw [eq_top_iff, ← Concept.extent_subset_extent_iff, Concept.extent_top]
    have h₁ := Concept.extent_subset_extent_iff.2 (le_sup_left : c ≤ c ⊔ d)
    have h₂ := Concept.extent_subset_extent_iff.2 (le_sup_right : d ≤ c ⊔ d)
    rintro (_ | _ | _) -
    · exact h₁ (by simp [c])
    · exact h₂ (by simp [d])
    · exact h₁ (by simp [c])
  have h : e.symm c ⊔ e.symm d = ⊤ := by rw [← e.symm.map_sup, hcd, e.symm.map_top]
  rcases eq_top_or_eq_top_of_sup_eq_top_adjoinTop h with h | h
  · exact hc (by rw [← e.apply_symm_apply c, h, e.map_top])
  · exact hd (by rw [← e.apply_symm_apply d, h, e.map_top])

/-- The lattice of closure systems of extents does not determine the concept lattice. -/
theorem exists_closureSubsystem_orderIso_and_isEmpty_concept_orderIso :
    ∃ r₁ r₂ : Option Bool → Option Bool → Prop,
      Nonempty (ClosureSubsystem (IsExtent r₁) ≃o ClosureSubsystem (IsExtent r₂)) ∧
        IsEmpty (Concept _ _ r₁ ≃o Concept _ _ r₂) :=
  ⟨_, _, ⟨ClosureSubsystem.adjoinTopAdjoinBotIso _⟩, isEmpty_concept_adjoinTop_orderIso_adjoinBot⟩

/-- **The scale-hierarchy does not determine the concept lattice**: there are two contexts with
three objects whose scale-hierarchies are isomorphic while their concept lattices, with five
elements each, are not. -/
theorem exists_scaleHierarchy_orderIso_and_isEmpty_concept_orderIso :
    ∃ r₁ r₂ : Option Bool → Option Bool → Prop,
      Nonempty (ScaleHierarchy r₁ ≃o ScaleHierarchy r₂) ∧
        IsEmpty (Concept _ _ r₁ ≃o Concept _ _ r₂) :=
  ⟨_, _, ⟨(scaleHierarchyIso _).symm.trans <|
    (ClosureSubsystem.adjoinTopAdjoinBotIso _).trans (scaleHierarchyIso _)⟩,
    isEmpty_concept_adjoinTop_orderIso_adjoinBot⟩

/-! ### Reconstruction for coatomistic concept lattices -/

section Coatomistic

variable {γ δ : Type*} {s : γ → δ → Prop}

/-- In a coatomistic concept lattice every extent is an intersection of maximal proper
extents. -/
theorem isClosedCoatomistic_isExtent [IsCoatomistic (Concept α β r)] :
    IsClosedCoatomistic (IsExtent r) := by
  intro A hA
  obtain ⟨S, hS, hS'⟩ := IsCoatomistic.isGLB_coatoms (Concept.ofIsExtent r A hA)
  refine ⟨Concept.extent '' S, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    have hd' := hS' d hd
    refine ⟨d.isExtent_extent, fun h ↦ hd'.1 ?_, fun D hD hdD ↦ ?_⟩
    · exact Concept.extent_injective (h.trans Concept.extent_top.symm)
    · have hle : d ≤ Concept.ofIsExtent r D hD := Concept.extent_subset_extent_iff.1 hdD
      rcases eq_or_lt_of_le hle with h | h
      · exact .inl (congrArg Concept.extent h).symm
      · exact .inr ((congrArg Concept.extent (hd'.2 _ h)).trans Concept.extent_top)
  · have h := congrArg Concept.extent hS.sInf_eq
    rw [Concept.extent_sInf] at h
    rw [sInter_image]
    exact h

/-- **Reconstruction for coatomistic concept lattices.** If the concept lattice of a context
with finitely many objects is coatomistic, then it is determined by the lattice of closure
systems of extents: every context with an isomorphic lattice of closure systems of extents has
an isomorphic concept lattice. -/
theorem nonempty_concept_orderIso_of_closureSubsystem_orderIso [Finite α]
    [IsCoatomistic (Concept α β r)]
    (e : ClosureSubsystem (IsExtent r) ≃o ClosureSubsystem (IsExtent s)) :
    Nonempty (Concept α β r ≃o Concept γ δ s) :=
  let ⟨f⟩ := ClosureSubsystem.nonempty_closed_orderIso isClosedCoatomistic_isExtent e
  ⟨(Concept.extentOrderIso r).trans (f.trans (Concept.extentOrderIso s).symm)⟩

/-- **The scale-hierarchy determines coatomistic concept lattices.** If the concept lattice of
a context with finitely many objects is coatomistic, then every context with an isomorphic
scale-hierarchy has an isomorphic concept lattice. -/
theorem nonempty_concept_orderIso_of_scaleHierarchy_orderIso [Finite α]
    [IsCoatomistic (Concept α β r)] (e : ScaleHierarchy r ≃o ScaleHierarchy s) :
    Nonempty (Concept α β r ≃o Concept γ δ s) :=
  nonempty_concept_orderIso_of_closureSubsystem_orderIso
    ((scaleHierarchyIso r).trans (e.trans (scaleHierarchyIso s).symm))

end Coatomistic

end FCA
