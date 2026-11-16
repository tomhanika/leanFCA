/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Ferrers
public import FCA.Order.Dimension
public import FCA.Scale.Standard

/-!
# The order dimension of concept lattices

This file proves that the order dimension of a concept lattice equals the Ferrers dimension of
its context (Ganter–Wille, Theorem 46): the incidence `r` is an intersection of Ferrers relations
indexed by `ι` if and only if the order of the concept lattice of `r` is an intersection of
linear orders indexed by `ι`. No finiteness assumption is needed.

## Main results

* `FCA.hasRealizer_concept_iff`: `HasRealizer (Concept α β r) ι ↔ HasFerrersCover r ι`.
* `FCA.hasRealizer_set_iff`: the powerset lattice of `α` has a realizer indexed by `ι` if and
  only if `α` embeds into `ι`, i.e. its order dimension is the cardinality of `α`.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order Concept

universe u v

namespace FCA

variable {α : Type u} {β : Type v} {ι : Type*} {r : α → β → Prop}

/-- A Ferrers cover of the incidence yields a realizer of the concept lattice: each concept is
sent to the closure of its extent with respect to each Ferrers relation, and the extents of a
Ferrers relation form a chain. -/
theorem HasFerrersCover.hasRealizer_concept (h : HasFerrersCover r ι) :
    HasRealizer (Concept α β r) ι := by
  obtain ⟨F, hF, hr⟩ := h
  let (i : ι) : LinearOrder {A // IsExtent (F i) A} := (hF i).linearOrderExtents
  refine .of_forall_le_iff (fun i c ↦ (⟨lowerPolar (F i) (upperPolar (F i) c.extent),
    isExtent_lowerPolar⟩ : {A // IsExtent (F i) A})) fun c d ↦ ⟨fun hcd i ↦ ?_, fun h a ha ↦ ?_⟩
  · exact lowerPolar_anti _ (upperPolar_anti _ hcd)
  · rw [← d.lowerPolar_intent]
    intro b hb
    refine (hr a b).2 fun i ↦ ?_
    have hd : lowerPolar (F i) (upperPolar (F i) d.extent) ⊆ lowerPolar (F i) {b} :=
      IsExtent.lowerPolar_upperPolar_subset isExtent_lowerPolar fun a' ha' b' hb' ↦ by
        rw [mem_singleton_iff.1 hb']
        exact (hr a' b).1 (d.rel_extent_intent ha' hb) i
    exact hd (h i (subset_lowerPolar_upperPolar _ _ ha)) (mem_singleton b)

/-- A realizer of the concept lattice yields a Ferrers cover of the incidence: an object is
related to an attribute if its object concept is below the attribute concept in the respective
linear order. -/
theorem HasRealizer.hasFerrersCover (h : HasRealizer (Concept α β r) ι) :
    HasFerrersCover r ι := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun i a b ↦ (L i).le (ofObject r a) (ofAttribute r b), fun i a b a' b' h h' ↦ ?_,
    fun a b ↦ ofObject_le_ofAttribute_iff.symm.trans (hL _ _)⟩
  refine or_iff_not_imp_right.2 fun hn ↦ ?_
  have h'' := (@le_total _ (L i) (ofObject r a') (ofAttribute r b)).resolve_left hn
  exact @le_trans _ (L i).toPreorder _ _ _ (@le_trans _ (L i).toPreorder _ _ _ h h'') h'

/-- **Ganter–Wille, Theorem 46**: the order dimension of a concept lattice equals the Ferrers
dimension of its context. Precisely, the order of the concept lattice of `r` is an intersection
of linear orders indexed by `ι` if and only if `r` is an intersection of Ferrers relations
indexed by `ι`. -/
theorem hasRealizer_concept_iff : HasRealizer (Concept α β r) ι ↔ HasFerrersCover r ι :=
  ⟨HasRealizer.hasFerrersCover, HasFerrersCover.hasRealizer_concept⟩

/-- The concept lattice of `r` embeds into a product of chains indexed by `ι` if and only if `r`
is an intersection of Ferrers relations indexed by `ι`. -/
theorem hasFerrersCover_iff_exists_orderEmbedding :
    HasFerrersCover r ι ↔ ∃ (C : ι → Type (max u v)) (_ : ∀ i, LinearOrder (C i)),
      Nonempty (Concept α β r ↪o ∀ i, C i) :=
  hasRealizer_concept_iff.symm.trans hasRealizer_iff_exists_orderEmbedding

/-- The powerset lattice of `α` has a realizer indexed by `ι` if and only if `α` embeds into `ι`.
In other words, the order dimension of the powerset of `α` is the cardinality of `α`. -/
theorem hasRealizer_set_iff : HasRealizer (Set α) ι ↔ Nonempty (α ↪ ι) :=
  contranominalIso.hasRealizer_iff.symm.trans <|
    hasRealizer_concept_iff.trans hasFerrersCover_ne_iff

end FCA
