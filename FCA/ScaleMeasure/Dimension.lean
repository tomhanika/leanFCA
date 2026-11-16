/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Concept.Dimension
public import FCA.ScaleMeasure.Hierarchy

/-!
# Dimension bounds for scale-measures

This file proves the dimension bounds of Section 3.3 of Hanika and Hirth, *On the Lattice of
Conceptual Measurements*, both for the Ferrers dimension of the scale contexts
(`FCA.HasFerrersCover`) and for the order dimension of their concept lattices
(`FCA.HasRealizer`).

## Main results

* `FCA.ClosureSubsystem.HasFerrersCover.mono`, `FCA.ClosureSubsystem.hasRealizer_concept_mono`:
  a coarser scale-measure in canonical form has at most the dimension of a finer one
  (Proposition 24).
* `FCA.HasRealizer.concept_apposition`: the order dimension of the concept lattice of an
  apposition is at most the sum of the order dimensions of the concept lattices of its parts
  (Proposition 25). The Ferrers version is `FCA.HasFerrersCover.apposition`; the bound is sharp by
  `FCA.hasFerrersCover_apposition_ne_inl_ne_inr_iff`.

## Implementation notes

The order dimension of a concept lattice equals the Ferrers dimension of its context
(Ganter–Wille, Theorem 46, formalised without any finiteness assumption as
`FCA.hasRealizer_concept_iff`). The order-dimension statements of this file are obtained from
their Ferrers counterparts through this theorem. Proposition 24 is stated for scale-measures in
canonical form.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function

namespace FCA

variable {α β γ δ ζ ι κ : Type*} {r : α → β → Prop}

/-! ### Coarser scale-measures -/

/-- A coarser closure system of extents has a canonical scale of at most the Ferrers dimension
of a finer one. -/
theorem ClosureSubsystem.HasFerrersCover.mono {𝒜 ℬ : ClosureSubsystem r} (h : 𝒜 ≤ ℬ)
    (hℬ : HasFerrersCover ℬ.context ι) : HasFerrersCover 𝒜.context ι :=
  hℬ.comp id fun A : {A // A ∈ 𝒜} ↦ (⟨A.1, ClosureSubsystem.le_def.1 h A.2⟩ : {A // A ∈ ℬ})

/-- The concept lattice of the canonical scale of a coarser closure system of extents has at
most the order dimension of that of a finer one. -/
theorem ClosureSubsystem.hasRealizer_concept_mono {𝒜 ℬ : ClosureSubsystem r} (h : 𝒜 ≤ ℬ)
    (hℬ : HasRealizer (Concept α {A // A ∈ ℬ} ℬ.context) ι) :
    HasRealizer (Concept α {A // A ∈ 𝒜} 𝒜.context) ι :=
  hasRealizer_concept_iff.2 (HasFerrersCover.mono h (hasRealizer_concept_iff.1 hℬ))

/-- If `(σ, s)` is coarser than `(ψ, t)`, the canonical representation of `(σ, s)` has at most
the Ferrers dimension of the canonical representation of `(ψ, t)`. -/
theorem ScaleCoarser.hasFerrersCover {ε η θ : Type*} {s : γ → δ → Prop} {t : ε → η → Prop}
    {σ : α → γ} {ψ : α → ε} (hσ : IsScaleMeasure r s σ) (hψ : IsScaleMeasure r t ψ)
    (h : ScaleCoarser s σ t ψ) (hc : HasFerrersCover hψ.closureSubsystem.context θ) :
    HasFerrersCover hσ.closureSubsystem.context θ :=
  ClosureSubsystem.HasFerrersCover.mono ((scaleCoarser_iff_closureSubsystem_le hσ hψ).1 h) hc

/-- If `(σ, s)` is coarser than `(ψ, t)`, the concept lattice of the canonical representation of
`(σ, s)` has at most the order dimension of that of `(ψ, t)`. -/
theorem ScaleCoarser.hasRealizer_concept {ε η θ : Type*} {s : γ → δ → Prop} {t : ε → η → Prop}
    {σ : α → γ} {ψ : α → ε} (hσ : IsScaleMeasure r s σ) (hψ : IsScaleMeasure r t ψ)
    (h : ScaleCoarser s σ t ψ)
    (hc : HasRealizer (Concept α _ hψ.closureSubsystem.context) θ) :
    HasRealizer (Concept α _ hσ.closureSubsystem.context) θ :=
  ClosureSubsystem.hasRealizer_concept_mono ((scaleCoarser_iff_closureSubsystem_le hσ hψ).1 h) hc

/-! ### Apposition -/

/-- The order dimension of the concept lattice of an apposition is at most the sum of the order
dimensions of the concept lattices of its parts. -/
theorem HasRealizer.concept_apposition {r₂ : α → ζ → Prop}
    (h₁ : HasRealizer (Concept α β r) ι) (h₂ : HasRealizer (Concept α ζ r₂) κ) :
    HasRealizer (Concept α (β ⊕ ζ) (apposition r r₂)) (ι ⊕ κ) :=
  hasRealizer_concept_iff.2 <|
    (hasRealizer_concept_iff.1 h₁).apposition (hasRealizer_concept_iff.1 h₂)

/-- The order dimension of the concept lattice of an apposition, for finite dimensions. -/
theorem HasRealizer.concept_apposition_fin {r₂ : α → ζ → Prop} {m n : ℕ}
    (h₁ : HasRealizer (Concept α β r) (Fin m)) (h₂ : HasRealizer (Concept α ζ r₂) (Fin n)) :
    HasRealizer (Concept α (β ⊕ ζ) (apposition r r₂)) (Fin (m + n)) :=
  hasRealizer_concept_iff.2 <|
    (hasRealizer_concept_iff.1 h₁).apposition_fin (hasRealizer_concept_iff.1 h₂)

end FCA
