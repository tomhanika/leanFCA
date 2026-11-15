/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ScaleMeasure.Hierarchy
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ferrers dimension of scale-measures

A *Ferrers relation* is a relation `F` such that `F a b` and `F a' b'` imply `F a b'` or
`F a' b`. The *Ferrers dimension* of a context is the least number of Ferrers relations whose
intersection is the incidence. This file proves the dimension bounds of Section 3.3 of Hanika and
Hirth, *On the Lattice of Conceptual Measurements*, in terms of Ferrers covers.

## Main definitions

* `FCA.IsFerrers F`: `F` is a Ferrers relation.
* `FCA.HasFerrersCover r ι`: the incidence `r` is the intersection of a family of Ferrers
  relations indexed by `ι`.

## Main results

* `FCA.ClosureSubsystem.HasFerrersCover.mono`: a coarser scale-measure in canonical form has at
  most the Ferrers dimension of a finer one (Proposition 24).
* `FCA.HasFerrersCover.apposition`: the Ferrers dimension of an apposition is at most the sum of
  the Ferrers dimensions of its parts (Proposition 25).

## Implementation notes

For finite contexts the Ferrers dimension equals the order dimension of the concept lattice
(Ganter–Wille, Theorem 46). Neither the order dimension nor this theorem is formalised here, so
the results are stated for the Ferrers dimension, and Proposition 24 for scale-measures in
canonical form.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function

namespace FCA

variable {α β γ δ ζ ι κ : Type*} {r : α → β → Prop}

/-- A relation `F` is a *Ferrers relation* if `F a b` and `F a' b'` imply `F a b'` or
`F a' b`. -/
def IsFerrers (F : α → β → Prop) : Prop :=
  ∀ ⦃a b a' b'⦄, F a b → F a' b' → F a b' ∨ F a' b

theorem IsFerrers.comp {F : α → β → Prop} (hF : IsFerrers F) (f : γ → α) (g : δ → β) :
    IsFerrers fun c d ↦ F (f c) (g d) :=
  fun _ _ _ _ h h' ↦ hF h h'

theorem isFerrers_top : IsFerrers fun (_ : α) (_ : β) ↦ True :=
  fun _ _ _ _ _ _ ↦ .inl trivial

/-- The incidence `r` is the intersection of a family of Ferrers relations indexed by `ι`. -/
def HasFerrersCover (r : α → β → Prop) (ι : Type*) : Prop :=
  ∃ F : ι → α → β → Prop, (∀ i, IsFerrers (F i)) ∧ ∀ a b, r a b ↔ ∀ i, F i a b

/-- A Ferrers cover restricts along maps of objects and attributes. -/
theorem HasFerrersCover.comp (h : HasFerrersCover r ι) (f : γ → α) (g : δ → β) :
    HasFerrersCover (fun c d ↦ r (f c) (g d)) ι :=
  let ⟨F, hF, hr⟩ := h
  ⟨fun i c d ↦ F i (f c) (g d), fun i ↦ (hF i).comp f g, fun _ _ ↦ hr _ _⟩

/-- A Ferrers cover can be reindexed along a surjection. -/
theorem HasFerrersCover.of_surjective (h : HasFerrersCover r ι) (e : κ → ι)
    (he : Surjective e) : HasFerrersCover r κ :=
  let ⟨F, hF, hr⟩ := h
  ⟨fun k ↦ F (e k), fun k ↦ hF (e k), fun a b ↦ (hr a b).trans he.forall⟩

/-- The Ferrers dimension of an apposition is at most the sum of the Ferrers dimensions. -/
theorem HasFerrersCover.apposition {r₂ : α → ζ → Prop} (h₁ : HasFerrersCover r ι)
    (h₂ : HasFerrersCover r₂ κ) : HasFerrersCover (apposition r r₂) (ι ⊕ κ) := by
  obtain ⟨F, hF, hr⟩ := h₁
  obtain ⟨F', hF', hr'⟩ := h₂
  refine ⟨Sum.elim (fun i a ↦ Sum.elim (F i a) fun _ ↦ True)
    (fun k a ↦ Sum.elim (fun _ ↦ True) (F' k a)), ?_, ?_⟩
  · rintro (i | k) a (b | b) a' (b' | b') h h' <;>
      first | exact hF i h h' | exact hF' k h h' | exact .inl trivial | exact .inr trivial
  · rintro a (b | b) <;> simp [hr, hr']

/-- The Ferrers dimension of an apposition, for finite dimensions. -/
theorem HasFerrersCover.apposition_fin {r₂ : α → ζ → Prop} {m n : ℕ}
    (h₁ : HasFerrersCover r (Fin m)) (h₂ : HasFerrersCover r₂ (Fin n)) :
    HasFerrersCover (FCA.apposition r r₂) (Fin (m + n)) :=
  (h₁.apposition h₂).of_surjective finSumFinEquiv.symm finSumFinEquiv.symm.surjective

/-- A coarser closure system of extents has a canonical scale of at most the Ferrers dimension
of a finer one. -/
theorem ClosureSubsystem.HasFerrersCover.mono {𝒜 ℬ : ClosureSubsystem r} (h : 𝒜 ≤ ℬ)
    (hℬ : HasFerrersCover ℬ.context ι) : HasFerrersCover 𝒜.context ι :=
  hℬ.comp id fun A : {A // A ∈ 𝒜} ↦ (⟨A.1, ClosureSubsystem.le_def.1 h A.2⟩ : {A // A ∈ ℬ})

/-- If `(σ, s)` is coarser than `(ψ, t)`, the canonical representation of `(σ, s)` has at most
the Ferrers dimension of the canonical representation of `(ψ, t)`. -/
theorem ScaleCoarser.hasFerrersCover {ε η θ : Type*} {s : γ → δ → Prop} {t : ε → η → Prop}
    {σ : α → γ} {ψ : α → ε} (hσ : IsScaleMeasure r s σ) (hψ : IsScaleMeasure r t ψ)
    (h : ScaleCoarser s σ t ψ) (hc : HasFerrersCover hψ.closureSubsystem.context θ) :
    HasFerrersCover hσ.closureSubsystem.context θ :=
  ClosureSubsystem.HasFerrersCover.mono ((scaleCoarser_iff_closureSubsystem_le hσ hψ).1 h) hc

end FCA
