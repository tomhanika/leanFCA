/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ClosureSystem
public import FCA.Order.ClosureSubsystem.Structure
public import FCA.ScaleMeasure.Hierarchy

/-!
# The structure of the scale-hierarchy

By `FCA.scaleHierarchyIso` the scale-hierarchy of a context `r` is the lattice
`FCA.ClosureSubsystem (IsExtent r)` of closure systems of extents of `r`. Its structure is
described in Section 3 of Hanika and Hirth, *Exploring Scale-Measures of Data Sets*.

Almost all of that structure holds for the closure systems contained in an arbitrary closure
system and is proved in `FCA.Order.ClosureSubsystem.Structure`: atoms and atomisticity, the
covering relation, lower semimodularity, the grading, coatoms, meet-irreducible elements,
distributivity, join-semidistributivity, join-pseudocomplements and meet-distributivity. All of
it applies to `FCA.ClosureSubsystem (IsExtent r)`.

This file adds what is specific to formal contexts: the meet-irreducible elements of the
scale-hierarchy in terms of the covering relation of the concept lattice.

## Main definitions

* `FCA.ClosureSubsystem.infIrredEquiv`: for finite contexts, the covering pairs of the concept
  lattice correspond to the meet-irreducible elements of the scale-hierarchy.

## Main results

* `Concept.covBy_iff_extent`: a concept is covered by another one iff no extent lies strictly
  between their extents.
* `FCA.ClosureSubsystem.infIrred_respecting_extent_iff`: for concepts `c < d`, the closure
  system of the extents respecting the implication `c.extent → d.extent` is meet-irreducible
  iff `d` covers `c`.
* `FCA.ClosureSubsystem.natCard_infIrred`: for finite contexts, the number of meet-irreducible
  elements of the scale-hierarchy is the number of covering pairs of the *concept lattice*, not
  of the scale-hierarchy.

## References

* [T. Hanika, J. Hirth, *Exploring Scale-Measures of Data Sets*][hanika2021]
* [N. Caspard, B. Monjardet, *The lattices of closure systems, closure operators, and
  implicational systems on a finite set: a survey*][caspard2003]
-/

@[expose] public section

open Set Function Order

namespace Concept

variable {α β : Type*} {r : α → β → Prop} {c d : Concept α β r}

/-- A concept is covered by another one if and only if no extent lies strictly between their
extents. -/
theorem covBy_iff_extent : c ⋖ d ↔ c.extent ⊂ d.extent ∧
    ∀ D, IsExtent r D → c.extent ⊆ D → D ⊆ d.extent → D = c.extent ∨ D = d.extent := by
  constructor
  · refine fun h ↦ ⟨extent_ssubset_extent_iff.2 h.lt, fun D hD hc hd ↦ ?_⟩
    have hc' : c ≤ ofIsExtent r D hD := extent_subset_extent_iff.1 hc
    have hd' : ofIsExtent r D hD ≤ d := extent_subset_extent_iff.1 hd
    rcases hc'.eq_or_lt with heq | hlt
    · exact .inl (congrArg extent heq).symm
    · exact .inr (congrArg extent (hd'.eq_of_not_lt (h.2 hlt)))
  · rintro ⟨hlt, h⟩
    refine ⟨extent_ssubset_extent_iff.1 hlt, fun e hce hed ↦ ?_⟩
    rcases h e.extent e.isExtent_extent (extent_subset_extent_iff.2 hce.le)
      (extent_subset_extent_iff.2 hed.le) with heq | heq
    · exact hce.ne' (extent_injective heq)
    · exact hed.ne (extent_injective heq)

end Concept

namespace FCA

namespace ClosureSubsystem

variable {α β : Type*} {r : α → β → Prop}

/-! ### Meet-irreducible elements and covering pairs of the concept lattice -/

/-- For concepts `c < d`, the closure system `respecting (IsExtent r) c.extent d.extent` is
meet-irreducible if and only if `d` covers `c`. -/
theorem infIrred_respecting_extent_iff {c d : Concept α β r} (h : c < d) :
    InfIrred (respecting (IsExtent r) c.extent d.extent) ↔ c ⋖ d := by
  have hlt := Concept.extent_ssubset_extent_iff.2 h
  rw [infIrred_respecting_iff c.isExtent_extent d.isExtent_extent hlt, Concept.covBy_iff_extent]
  exact (and_iff_right hlt).symm

/-- For a finite context, the covering pairs of the concept lattice correspond bijectively to
the meet-irreducible elements of the lattice of closure systems of extents. -/
noncomputable def infIrredEquiv [Finite α] (r : α → β → Prop) :
    {p : Concept α β r × Concept α β r // p.1 ⋖ p.2} ≃
      {𝒜 : ClosureSubsystem (IsExtent r) // InfIrred 𝒜} :=
  Equiv.ofBijective
    (fun p ↦ ⟨respecting (IsExtent r) p.1.1.extent p.1.2.extent,
      (infIrred_respecting_extent_iff p.2.lt).2 p.2⟩)
    ⟨fun p q h ↦ by
      have := (respecting_inj p.1.1.isExtent_extent p.1.2.isExtent_extent
        (Concept.extent_ssubset_extent_iff.2 p.2.lt) q.1.1.isExtent_extent q.1.2.isExtent_extent
        (Concept.extent_ssubset_extent_iff.2 q.2.lt)).1 (congrArg Subtype.val h)
      exact Subtype.ext (Prod.ext (Concept.extent_injective this.1)
        (Concept.extent_injective this.2)),
    fun 𝒜 ↦ by
      obtain ⟨A, C, hA, hC, hAC, hcov, h𝒜⟩ := InfIrred.exists_respecting 𝒜.2
      refine ⟨⟨(.ofIsExtent r A hA, .ofIsExtent r C hC),
        Concept.covBy_iff_extent.2 ⟨hAC, hcov⟩⟩, Subtype.ext h𝒜.symm⟩⟩

@[simp]
theorem coe_infIrredEquiv [Finite α] (p : {p : Concept α β r × Concept α β r // p.1 ⋖ p.2}) :
    (infIrredEquiv r p : ClosureSubsystem (IsExtent r)) =
      respecting (IsExtent r) p.1.1.extent p.1.2.extent :=
  rfl

/-- For a finite context, the number of meet-irreducible elements of the lattice of closure
systems of extents is the number of covering pairs of the concept lattice. -/
theorem natCard_infIrred [Finite α] (r : α → β → Prop) :
    Nat.card {𝒜 : ClosureSubsystem (IsExtent r) // InfIrred 𝒜} =
      Nat.card {p : Concept α β r × Concept α β r // p.1 ⋖ p.2} :=
  Nat.card_congr (infIrredEquiv r).symm

end ClosureSubsystem

end FCA
