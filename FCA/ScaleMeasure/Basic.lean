/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ClosureSystem
public import FCA.Context.Constructions
public import Mathlib.Data.Set.Lattice.Image

/-!
# Scale-measures

A *scale-measure* of a formal context `r : α → β → Prop` into a *scale* context
`s : γ → δ → Prop` is a map `σ : α → γ` between the object sets such that the preimage of every
extent of `s` is an extent of `r` (Ganter–Wille, Definition 91). Scale-measures are exactly the
continuous maps between the closure spaces of extents.

This file follows Section 2 and Section 3.2 of Hanika and Hirth, *On the Lattice of Conceptual
Measurements*. None of the results needs the finiteness assumption made there.

## Main definitions

* `FCA.IsScaleMeasure r s σ`: `σ` is an `s`-measure of `r`.
* `FCA.IsFullScaleMeasure r s σ`: additionally, every extent of `r` is such a preimage.
* `FCA.scaleExtents s σ`: the extents of `r` reflected by the scale-measure, written
  `σ⁻¹(Ext(𝕊))` in the literature.
* `FCA.ScaleCoarser`, `FCA.ScaleEquiv`: the refinement preorder on scale-measures and its
  equivalence (Definition 4).

## Main results

* `FCA.isScaleMeasure_iff_extentClosure`: scale-measures are the continuous maps.
* `FCA.IsScaleMeasure.comp`: scale-measures compose (Corollary 2).
* `FCA.isScaleMeasure_iff_forall_singleton`: it suffices to test the attribute extents of the
  scale (Proposition 20).
* `FCA.IsScaleMeasure.apposition`: apposition of scale-measures (Proposition 19).
* `FCA.isScaleMeasure_id_comp_attr`: attribute projection (Corollary 22).
* `FCA.IsScaleMeasure.conceptOrderIso`: for surjective equivalent scale-measures the concept
  lattices of the scales are isomorphic (Lemma 6).

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β γ δ ε ζ : Type*} {r : α → β → Prop} {s : γ → δ → Prop} {t : ε → ζ → Prop}
  {σ : α → γ} {ψ : α → ε}

/-! ### Scale-measures -/

/-- The map `σ` between the object sets is an `s`-*measure* of the context `r` if the preimage of
every extent of the scale `s` is an extent of `r`. -/
def IsScaleMeasure (r : α → β → Prop) (s : γ → δ → Prop) (σ : α → γ) : Prop :=
  ∀ ⦃A⦄, IsExtent s A → IsExtent r (σ ⁻¹' A)

/-- A scale-measure is *full* if every extent of `r` is the preimage of an extent of the
scale. -/
def IsFullScaleMeasure (r : α → β → Prop) (s : γ → δ → Prop) (σ : α → γ) : Prop :=
  IsScaleMeasure r s σ ∧ ∀ ⦃A⦄, IsExtent r A → ∃ B, IsExtent s B ∧ σ ⁻¹' B = A

/-- Scale-measures are exactly the continuous maps between the closure spaces of extents. -/
theorem isScaleMeasure_iff_extentClosure :
    IsScaleMeasure r s σ ↔
      ∀ A : Set γ, extentClosure r (σ ⁻¹' A) ⊆ σ ⁻¹' extentClosure s A := by
  refine ⟨fun h A ↦ ?_, fun h A hA ↦ ?_⟩
  · exact (h (isExtent_lowerPolar (t := upperPolar s A))).lowerPolar_upperPolar_subset
      (preimage_mono (subset_lowerPolar_upperPolar s A))
  · refine isExtent_iff.2 (((h A).trans ?_).antisymm (subset_lowerPolar_upperPolar r _))
    exact (preimage_mono hA.eq.subset :)

/-- The identity is a scale-measure of every context into itself. -/
theorem isScaleMeasure_id (r : α → β → Prop) : IsScaleMeasure r r id :=
  fun _ hA ↦ hA

theorem isFullScaleMeasure_id (r : α → β → Prop) : IsFullScaleMeasure r r id :=
  ⟨isScaleMeasure_id r, fun A hA ↦ ⟨A, hA, rfl⟩⟩

/-- Scale-measures compose. -/
theorem IsScaleMeasure.comp {φ : γ → ε} (hφ : IsScaleMeasure s t φ) (hσ : IsScaleMeasure r s σ) :
    IsScaleMeasure r t (φ ∘ σ) :=
  fun _ hA ↦ hσ (hφ hA)

/-- To check that `σ` is a scale-measure it suffices to consider the attribute extents of the
scale. -/
theorem isScaleMeasure_iff_forall_singleton :
    IsScaleMeasure r s σ ↔ ∀ n : δ, IsExtent r (σ ⁻¹' lowerPolar s {n}) := by
  refine ⟨fun h n ↦ h isExtent_lowerPolar, ?_⟩
  rintro h _ ⟨u, rfl⟩
  have : lowerPolar s u = ⋂ n ∈ u, lowerPolar s {n} := by
    rw [← lowerPolar_iUnion₂, biUnion_of_singleton]
  rw [this, preimage_iInter₂]
  exact .iInter₂ _ fun n _ ↦ h n

/-- If `σ` is a measure into two scales on the same objects, it is a measure into their
apposition. -/
theorem IsScaleMeasure.apposition {s₂ : γ → ζ → Prop} (h₁ : IsScaleMeasure r s σ)
    (h₂ : IsScaleMeasure r s₂ σ) : IsScaleMeasure r (apposition s s₂) σ := by
  intro A hA
  obtain ⟨A₁, A₂, hA₁, hA₂, rfl⟩ := isExtent_apposition_iff.1 hA
  exact (h₁ hA₁).inter (h₂ hA₂)

theorem isScaleMeasure_apposition_iff {s₂ : γ → ζ → Prop} :
    IsScaleMeasure r (apposition s s₂) σ ↔ IsScaleMeasure r s σ ∧ IsScaleMeasure r s₂ σ := by
  refine ⟨fun h ↦ ⟨fun A hA ↦ ?_, fun A hA ↦ ?_⟩, fun h ↦ h.1.apposition h.2⟩
  · exact h (isExtent_apposition_iff.2 ⟨A, univ, hA, .univ, inter_univ A⟩)
  · exact h (isExtent_apposition_iff.2 ⟨univ, A, .univ, hA, univ_inter A⟩)

/-- **Attribute projection**: selecting (and renaming) attributes of a context yields a scale for
which the identity is a scale-measure. -/
theorem isScaleMeasure_id_comp_attr (r : α → β → Prop) (f : δ → β) :
    IsScaleMeasure r (fun a n ↦ r a (f n)) id := by
  rw [isScaleMeasure_iff_forall_singleton]
  intro n
  have : lowerPolar (fun a n ↦ r a (f n)) {n} = lowerPolar r {f n} := by
    ext a
    simp
  rw [preimage_id, this]
  exact isExtent_lowerPolar

/-- The identity is a scale-measure into every subcontext obtained by restricting the
attributes. -/
theorem isScaleMeasure_id_restrictAttributes (r : α → β → Prop) (u : Set β) :
    IsScaleMeasure r (restrictAttributes r u) id :=
  isScaleMeasure_id_comp_attr r Subtype.val

/-! ### Extents reflected by a scale-measure -/

/-- The sets of objects of the form `σ ⁻¹' A` for an extent `A` of the scale `s`. For a
scale-measure these are the extents of `r` *reflected* by the scale. -/
def scaleExtents (s : γ → δ → Prop) (σ : α → γ) : Set (Set α) :=
  preimage σ '' {A | IsExtent s A}

theorem mem_scaleExtents {A : Set α} :
    A ∈ scaleExtents s σ ↔ ∃ B, IsExtent s B ∧ σ ⁻¹' B = A :=
  Iff.rfl

theorem preimage_mem_scaleExtents {B : Set γ} (hB : IsExtent s B) :
    σ ⁻¹' B ∈ scaleExtents s σ :=
  ⟨B, hB, rfl⟩

@[simp]
theorem scaleExtents_id (r : α → β → Prop) : scaleExtents r id = {A | IsExtent r A} := by
  simp [scaleExtents]

theorem isScaleMeasure_iff_scaleExtents_subset :
    IsScaleMeasure r s σ ↔ scaleExtents s σ ⊆ {A | IsExtent r A} := by
  refine ⟨?_, fun h A hA ↦ h (preimage_mem_scaleExtents hA)⟩
  rintro h _ ⟨B, hB, rfl⟩
  exact h hB

theorem isFullScaleMeasure_iff_scaleExtents_eq :
    IsFullScaleMeasure r s σ ↔ scaleExtents s σ = {A | IsExtent r A} := by
  rw [IsFullScaleMeasure, isScaleMeasure_iff_scaleExtents_subset, Subset.antisymm_iff]
  rfl

theorem univ_mem_scaleExtents (s : γ → δ → Prop) (σ : α → γ) : univ ∈ scaleExtents s σ :=
  ⟨univ, .univ, rfl⟩

/-- The reflected extents are closed under arbitrary intersections. -/
theorem sInter_mem_scaleExtents {S : Set (Set α)} (hS : S ⊆ scaleExtents s σ) :
    ⋂₀ S ∈ scaleExtents s σ := by
  have hS' : ∀ A, A ∈ S → ∃ B, IsExtent s B ∧ σ ⁻¹' B = A := fun A hA ↦ hS hA
  choose! B hB hBS using hS'
  refine ⟨⋂ A ∈ S, B A, .iInter₂ _ hB, ?_⟩
  rw [preimage_iInter₂, sInter_eq_biInter]
  exact iInter₂_congr hBS

theorem inter_mem_scaleExtents {A B : Set α} (hA : A ∈ scaleExtents s σ)
    (hB : B ∈ scaleExtents s σ) : A ∩ B ∈ scaleExtents s σ := by
  obtain ⟨A, hA, rfl⟩ := hA
  obtain ⟨B, hB, rfl⟩ := hB
  exact ⟨A ∩ B, hA.inter hB, rfl⟩

/-! ### Refinement of scale-measures -/

/-- The scale-measure `(σ, s)` is *coarser* than `(ψ, t)` if every extent reflected by `(σ, s)`
is reflected by `(ψ, t)`. This is a preorder on the scale-measures of a context. -/
def ScaleCoarser (s : γ → δ → Prop) (σ : α → γ) (t : ε → ζ → Prop) (ψ : α → ε) : Prop :=
  scaleExtents s σ ⊆ scaleExtents t ψ

/-- Two scale-measures are *equivalent* if they reflect the same extents. -/
def ScaleEquiv (s : γ → δ → Prop) (σ : α → γ) (t : ε → ζ → Prop) (ψ : α → ε) : Prop :=
  scaleExtents s σ = scaleExtents t ψ

theorem ScaleCoarser.refl (s : γ → δ → Prop) (σ : α → γ) : ScaleCoarser s σ s σ :=
  Subset.rfl

theorem ScaleCoarser.trans {η θ : Type*} {u : η → θ → Prop} {φ : α → η}
    (h₁ : ScaleCoarser s σ t ψ) (h₂ : ScaleCoarser t ψ u φ) : ScaleCoarser s σ u φ :=
  Subset.trans h₁ h₂

theorem scaleEquiv_iff_scaleCoarser :
    ScaleEquiv s σ t ψ ↔ ScaleCoarser s σ t ψ ∧ ScaleCoarser t ψ s σ :=
  Subset.antisymm_iff

theorem ScaleEquiv.refl (s : γ → δ → Prop) (σ : α → γ) : ScaleEquiv s σ s σ :=
  rfl

theorem ScaleEquiv.symm (h : ScaleEquiv s σ t ψ) : ScaleEquiv t ψ s σ :=
  Eq.symm h

theorem ScaleEquiv.trans {η θ : Type*} {u : η → θ → Prop} {φ : α → η}
    (h₁ : ScaleEquiv s σ t ψ) (h₂ : ScaleEquiv t ψ u φ) : ScaleEquiv s σ u φ :=
  Eq.trans h₁ h₂

/-- Being a scale-measure only depends on the equivalence class. -/
theorem ScaleEquiv.isScaleMeasure_iff (h : ScaleEquiv s σ t ψ) :
    IsScaleMeasure r s σ ↔ IsScaleMeasure r t ψ := by
  rw [isScaleMeasure_iff_scaleExtents_subset, isScaleMeasure_iff_scaleExtents_subset, h]

/-- A measure coarser than a scale-measure of `r` is a scale-measure of `r`. -/
theorem ScaleCoarser.isScaleMeasure (h : ScaleCoarser s σ t ψ) (hψ : IsScaleMeasure r t ψ) :
    IsScaleMeasure r s σ :=
  isScaleMeasure_iff_scaleExtents_subset.2
    (Subset.trans h (isScaleMeasure_iff_scaleExtents_subset.1 hψ))

/-- Every scale-measure of `r` is coarser than the identity measure into `r` itself. -/
theorem IsScaleMeasure.scaleCoarser_id (h : IsScaleMeasure r s σ) : ScaleCoarser s σ r id := by
  rw [ScaleCoarser, scaleExtents_id]
  exact isScaleMeasure_iff_scaleExtents_subset.1 h

/-- The apposition of two measures on the same scale objects is finer than both. -/
theorem scaleCoarser_apposition_left (s : γ → δ → Prop) (s₂ : γ → ζ → Prop) (σ : α → γ) :
    ScaleCoarser s σ (apposition s s₂) σ := by
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨A, isExtent_apposition_iff.2 ⟨A, univ, hA, .univ, inter_univ A⟩, rfl⟩

theorem scaleCoarser_apposition_right (s : γ → δ → Prop) (s₂ : γ → ζ → Prop) (σ : α → γ) :
    ScaleCoarser s₂ σ (apposition s s₂) σ := by
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨A, isExtent_apposition_iff.2 ⟨univ, A, .univ, hA, univ_inter A⟩, rfl⟩

/-- The extents reflected by an apposition are the pairwise intersections of the extents
reflected by its parts. -/
theorem scaleExtents_apposition (s : γ → δ → Prop) (s₂ : γ → ζ → Prop) (σ : α → γ) :
    scaleExtents (apposition s s₂) σ =
      {C | ∃ A ∈ scaleExtents s σ, ∃ B ∈ scaleExtents s₂ σ, A ∩ B = C} := by
  ext C
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨A, B, hA, hB, rfl⟩ := isExtent_apposition_iff.1 hD
    exact ⟨_, preimage_mem_scaleExtents hA, _, preimage_mem_scaleExtents hB, rfl⟩
  · rintro ⟨_, ⟨A, hA, rfl⟩, _, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨A ∩ B, isExtent_apposition_iff.2 ⟨A, B, hA, hB, rfl⟩, rfl⟩

/-! ### Surjective scale-measures -/

/-- For a surjective map `σ`, the concept lattice of the scale is isomorphic to the reflected
extents ordered by inclusion. -/
noncomputable def conceptOrderIsoScaleExtents (s : γ → δ → Prop) (hσ : Surjective σ) :
    Concept γ δ s ≃o scaleExtents s σ :=
  (Concept.extentOrderIso s).trans
    { toEquiv := Equiv.ofBijective
        (fun A ↦ ⟨σ ⁻¹' A.1, preimage_mem_scaleExtents A.2⟩)
        ⟨fun A B h ↦ Subtype.ext (preimage_injective.2 hσ (congrArg Subtype.val h)),
          fun ⟨_, B, hB, h⟩ ↦ ⟨⟨B, hB⟩, Subtype.ext h⟩⟩
      map_rel_iff' := fun {A B} ↦
        preimage_subset_preimage_iff (by simp [hσ.range_eq]) }

/-- Equivalent surjective scale-measures have scales with isomorphic concept lattices. -/
noncomputable def ScaleEquiv.conceptOrderIso (h : ScaleEquiv s σ t ψ) (hσ : Surjective σ)
    (hψ : Surjective ψ) : Concept γ δ s ≃o Concept ε ζ t :=
  (conceptOrderIsoScaleExtents s hσ).trans <|
    (orderIsoOfEq _ _ h).trans (conceptOrderIsoScaleExtents t hψ).symm

/-- A full surjective scale-measure induces an isomorphism of concept lattices. -/
noncomputable def IsFullScaleMeasure.conceptOrderIso (h : IsFullScaleMeasure r s σ)
    (hσ : Surjective σ) : Concept γ δ s ≃o Concept α β r :=
  (conceptOrderIsoScaleExtents s hσ).trans <|
    (orderIsoOfEq _ _ (isFullScaleMeasure_iff_scaleExtents_eq.1 h)).trans
      (Concept.extentOrderIso r).symm

end FCA
