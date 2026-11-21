/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ScaleMeasure.Dimension
public import FCA.Order.ClosureSubsystem.Ordinal
public import FCA.ScaleMeasure.Structure

/-!
# Scaling dimension in the scale-hierarchy

The *scaling dimension* of a context with respect to a family of scales asks how many scales of
that family are needed to represent the context. This file phrases the notion inside the lattice
`FCA.ClosureSubsystem (IsExtent r)` of closure systems of extents, which is the scale-hierarchy
of `r`: a closure system `𝒜` has scaling dimension at most `|ι|` with respect to a property `P`
if it is the join of an `ι`-indexed family of closure systems satisfying `P`. The definitions and
the chain-cover characterisation hold for the closure systems contained in an arbitrary closure
system and live in `FCA.Order.ClosureSubsystem.Ordinal`; this file relates them to Ferrers
relations and the order dimension.

For *ordinal* scales the property is that the closed sets form a chain. As for the order
dimension (`FCA.HasRealizer`) we do not define a numeric dimension but the predicate "at most
`|ι|`".

## Main definitions

* `FCA.ClosureSubsystem.IsOrdinal 𝒜`: the closed sets of `𝒜` form a chain.
* `FCA.ClosureSubsystem.HasCover P 𝒜 ι`: `𝒜` is the join of `ι` closure systems satisfying `P`.
* `FCA.ClosureSubsystem.HasOrdinalCover 𝒜 ι`: the ordinal scaling dimension of `𝒜` is at most
  `|ι|`.

## Main results

* `FCA.ClosureSubsystem.isOrdinal_iff_isFerrers`: `𝒜` is ordinal iff the incidence of its
  canonical scale is a Ferrers relation.
* `FCA.ClosureSubsystem.HasOrdinalCover.hasRealizer_concept`: the order dimension of the concept
  lattice of a scale-measure is at most its ordinal scaling dimension.
* `FCA.ClosureSubsystem.hasOrdinalCover_iff_irreducibles`: for finitely many objects, the
  ordinal scaling dimension of `𝒜` is at most `|ι|` iff the `⋂`-irreducible closed sets of `𝒜`
  can be covered by `ι` chains. The implication from left to right needs no finiteness.

## References

* [B. Ganter, T. Hanika, J. Hirth, *Scaling Dimension*][ganter2023]
* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function Order

namespace FCA

namespace ClosureSubsystem

variable {α β ι : Type*} {r : α → β → Prop} {𝒜 : ClosureSubsystem (IsExtent r)}

/-! ### Ordinal closure systems and Ferrers relations -/

/-- A closure system is ordinal iff the incidence of its canonical scale is a Ferrers
relation. -/
theorem isOrdinal_iff_isFerrers : 𝒜.IsOrdinal ↔ IsFerrers 𝒜.context := by
  constructor
  · intro h a A a' A' ha ha'
    rcases h A.2 A'.2 with hsub | hsub
    · exact .inl (hsub ha)
    · exact .inr (hsub ha')
  · intro h A B hA hB
    exact h.isExtent_total (isExtent_context_iff.2 hA) (isExtent_context_iff.2 hB)

theorem IsOrdinal.isFerrers_closure (h : 𝒜.IsOrdinal) :
    IsFerrers fun (a : α) (A : Set α) ↦ a ∈ 𝒜.closure A :=
  fun _ A _ A' ha ha' ↦ (h (closure_mem (A := A)) (closure_mem (A := A'))).elim
    (fun hs ↦ .inl (hs ha)) fun hs ↦ .inr (hs ha')

/-! ### Scaling dimension and order dimension -/

/-- An ordinal cover of `𝒜` yields a Ferrers cover of the canonical scale of `𝒜`. -/
theorem HasOrdinalCover.hasFerrersCover (h : 𝒜.HasOrdinalCover ι) :
    HasFerrersCover 𝒜.context ι := by
  obtain ⟨f, hf, rfl⟩ := h
  refine ⟨fun i a A ↦ a ∈ (f i).closure A.1,
    fun i ↦ (hf i).isFerrers_closure.comp id Subtype.val,
    fun a A ↦ ⟨fun ha i ↦ subset_closure ha, fun ha ↦ ?_⟩⟩
  exact (iInter_closure_eq_of_mem_iSup A.2).subset (mem_iInter.2 ha)

/-- The order dimension of the concept lattice of a scale-measure is at most its ordinal
scaling dimension. -/
theorem HasOrdinalCover.hasRealizer_concept (h : 𝒜.HasOrdinalCover ι) :
    HasRealizer (Concept α {A // A ∈ 𝒜} 𝒜.context) ι :=
  hasRealizer_concept_iff.2 h.hasFerrersCover

end ClosureSubsystem

end FCA
