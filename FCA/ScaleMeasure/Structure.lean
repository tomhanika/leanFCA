/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ClosureSystem
public import FCA.ScaleMeasure.Hierarchy
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Atoms
public import Mathlib.Order.Grade
public import Mathlib.Order.Irreducible
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.SuccPred.Nat

/-!
# The structure of the scale-hierarchy

By `FCA.scaleHierarchyIso` the scale-hierarchy of a context `r` is the lattice
`FCA.ClosureSubsystem r` of closure systems of extents of `r`. This file describes that lattice,
following Section 3 of Hanika and Hirth, *Exploring Scale-Measures of Data Sets*, and the
classical theory of the lattice of closure systems (Caspard and Monjardet).

## Main definitions

* `FCA.ClosureSubsystem.pair A hA`: the closure system `{G, A}`.
* `FCA.ClosureSubsystem.erase A hA`: all extents except `A`.
* `FCA.ClosureSubsystem.respecting r A C`: the extents `B` with `A ⊆ B → C ⊆ B`.
* `FCA.ClosureSubsystem.infIrredEquiv`: for finite contexts, the covering pairs of the concept
  lattice correspond to the meet-irreducible elements of the scale-hierarchy.

## Main results

* `FCA.ClosureSubsystem.isAtom_iff`: the atoms are the closure systems `{G, A}`, and the lattice
  is atomistic.
* `FCA.ClosureSubsystem.covBy_iff`: `𝒜` is covered by `ℬ` if and only if `ℬ` has exactly one
  closed set more than `𝒜`.
* The lattice is lower semimodular, and for finite contexts graded by `|𝒜| - 1`.
* `FCA.ClosureSubsystem.isCoatom_iff`: the coatoms are obtained by removing one extent which is
  not an intersection of other extents.
* `FCA.ClosureSubsystem.infIrred_respecting_iff`: `respecting r A C` is meet-irreducible if and
  only if `C` covers `A` among the extents. Every closure system is an infimum of such elements
  (`FCA.ClosureSubsystem.sInf_respecting_closure`), and for finite contexts every meet-irreducible
  element has this form (`FCA.ClosureSubsystem.InfIrred.exists_respecting`).
* `FCA.ClosureSubsystem.sup_inf_le_iff_total`: the lattice is distributive if and only if the
  extents form a chain.
* `FCA.ClosureSubsystem.sup_eq_sup_inf_of_sup_eq_sup`: for finite contexts the lattice is
  join-semidistributive.
* `FCA.ClosureSubsystem.IccCoreIso`: the lattice is meet-distributive, that is, the interval
  between a closure system and the meet of its lower covers is a powerset lattice.

## Implementation notes

Only the grading, the classification of all meet-irreducible elements and
join-semidistributivity need finiteness.

The number of meet-irreducible elements is the number of covering pairs of the *concept lattice*
(`FCA.ClosureSubsystem.natCard_infIrred`), not of the scale-hierarchy.

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

variable {α β : Type*} {r : α → β → Prop} {𝒜 ℬ 𝒞 : ClosureSubsystem r} {A B C : Set α}

instance [Finite α] : Finite (ClosureSubsystem r) :=
  Finite.of_injective carrier carrier_injective

/-! ### Atoms -/

/-- The closure system `{G, A}` for an extent `A`. -/
def pair (A : Set α) (hA : IsExtent r A) : ClosureSubsystem r where
  carrier := {univ, A}
  sInter_mem' S hS := by
    rw [mem_insert_iff, mem_singleton_iff]
    by_cases h : A ∈ S
    · refine .inr (Subset.antisymm (sInter_subset_of_mem h) (subset_sInter fun B hB ↦ ?_))
      rcases hS hB with rfl | rfl
      exacts [subset_univ _, Subset.rfl]
    · refine .inl (sInter_eq_univ.2 fun B hB ↦ ?_)
      rcases hS hB with rfl | rfl
      exacts [rfl, absurd hB h]
  isExtent' := by
    rintro _ (rfl | rfl)
    exacts [.univ, hA]

@[simp]
theorem mem_pair {hA : IsExtent r A} : B ∈ pair A hA ↔ B = univ ∨ B = A :=
  Iff.rfl

theorem self_mem_pair {hA : IsExtent r A} : A ∈ pair A hA :=
  .inr rfl

@[simp]
theorem pair_le_iff {hA : IsExtent r A} : pair A hA ≤ 𝒜 ↔ A ∈ 𝒜 := by
  refine ⟨fun h ↦ le_def.1 h self_mem_pair, fun h ↦ le_def.2 fun B hB ↦ ?_⟩
  rcases hB with rfl | rfl
  exacts [𝒜.univ_mem, h]

theorem pair_ne_bot {hA : IsExtent r A} (h : A ≠ univ) : pair A hA ≠ ⊥ :=
  fun hbot ↦ h (mem_bot.1 (hbot ▸ self_mem_pair))

/-- The closure system `{G, A}` is an atom of the lattice of closure systems of extents. -/
theorem isAtom_pair {hA : IsExtent r A} (h : A ≠ univ) : IsAtom (pair A hA) := by
  refine ⟨pair_ne_bot h, fun 𝒞 h𝒞 ↦ eq_bot_iff.2 (le_def.2 fun B hB ↦ mem_bot.2 ?_)⟩
  rcases le_def.1 h𝒞.le hB with rfl | rfl
  · rfl
  · exact absurd (pair_le_iff.2 hB) h𝒞.not_ge

/-- The atoms of the lattice of closure systems of extents are the closure systems `{G, A}`. -/
theorem isAtom_iff :
    IsAtom 𝒜 ↔ ∃ (A : Set α) (hA : IsExtent r A), A ≠ univ ∧ 𝒜 = pair A hA := by
  constructor
  · intro h
    obtain ⟨A, hA, hne⟩ : ∃ A ∈ 𝒜, A ≠ univ := by
      by_contra! hall
      exact h.1 (eq_bot_iff.2 (le_def.2 fun B hB ↦ mem_bot.2 (hall B hB)))
    refine ⟨A, 𝒜.isExtent hA, hne, ?_⟩
    rcases h.le_iff.1 (pair_le_iff.2 hA : pair A (𝒜.isExtent hA) ≤ 𝒜) with h' | h'
    · exact absurd h' (pair_ne_bot hne)
    · exact h'.symm
  · rintro ⟨A, hA, hne, rfl⟩
    exact isAtom_pair hne

/-- Every closure system of extents is the supremum of the atoms below it. -/
instance : IsAtomistic (ClosureSubsystem r) where
  isLUB_atoms 𝒜 := by
    refine ⟨{𝒟 | IsAtom 𝒟 ∧ 𝒟 ≤ 𝒜}, ⟨fun 𝒟 h ↦ h.2, fun ℬ hℬ ↦ le_def.2 fun A hA ↦ ?_⟩,
      fun 𝒟 h ↦ h.1⟩
    by_cases hne : A = univ
    · exact hne ▸ ℬ.univ_mem
    · exact pair_le_iff.1 (hℬ ⟨isAtom_pair (hA := 𝒜.isExtent hA) hne, pair_le_iff.2 hA⟩)

/-! ### The covering relation -/

theorem mem_sup_pair {hA : IsExtent r A} : B ∈ 𝒜 ⊔ pair A hA ↔ B ∈ 𝒜 ∨ ∃ C ∈ 𝒜, C ∩ A = B := by
  rw [mem_sup]
  constructor
  · rintro ⟨C, hC, D, rfl | rfl, rfl⟩
    · exact .inl (by rwa [inter_univ])
    · exact .inr ⟨C, hC, rfl⟩
  · rintro (hB | ⟨C, hC, rfl⟩)
    · exact ⟨B, hB, univ, .inl rfl, inter_univ B⟩
    · exact ⟨C, hC, A, .inr rfl, rfl⟩

/-- If `ℬ` covers `𝒜`, then `ℬ` is generated by `𝒜` and any closed set of `ℬ` not in `𝒜`. -/
theorem sup_pair_eq_of_covBy (h : 𝒜 ⋖ ℬ) (hA : A ∈ ℬ) (hA' : A ∉ 𝒜) :
    𝒜 ⊔ pair A (ℬ.isExtent hA) = ℬ := by
  have hlt : 𝒜 < 𝒜 ⊔ pair A (ℬ.isExtent hA) :=
    lt_of_le_of_ne le_sup_left fun heq ↦ hA' (heq ▸ le_def.1 le_sup_right self_mem_pair)
  exact (sup_le h.le (pair_le_iff.2 hA)).eq_of_not_lt (h.2 hlt)

/-- A closure system of extents is covered by another one if and only if the latter has exactly
one closed set more. -/
theorem covBy_iff : 𝒜 ⋖ ℬ ↔ ∃ A, A ∉ 𝒜 ∧ ℬ.carrier = insert A 𝒜.carrier := by
  constructor
  · intro h
    obtain ⟨A, hA, hA'⟩ : ∃ A ∈ ℬ, A ∉ 𝒜 := by
      by_contra! hall
      exact h.lt.not_ge (le_def.2 hall)
    refine ⟨A, hA', Subset.antisymm (fun B hB ↦ ?_) (insert_subset hA (le_def.1 h.le))⟩
    by_contra hB'
    rw [mem_insert_iff, not_or] at hB'
    have h₁ : B ∈ 𝒜 ⊔ pair A (ℬ.isExtent hA) := by rwa [sup_pair_eq_of_covBy h hA hA']
    have h₂ : A ∈ 𝒜 ⊔ pair B (ℬ.isExtent hB) := by rwa [sup_pair_eq_of_covBy h hB hB'.2]
    rcases mem_sup_pair.1 h₁ with h₁ | ⟨C, -, hC⟩
    · exact hB'.2 h₁
    rcases mem_sup_pair.1 h₂ with h₂ | ⟨D, -, hD⟩
    · exact hA' h₂
    exact hB'.1 (Subset.antisymm (hC ▸ inter_subset_right) (hD ▸ inter_subset_right))
  · rintro ⟨A, hA, hℬ⟩
    have hAℬ : A ∈ ℬ := mem_carrier.1 (hℬ ▸ mem_insert A _)
    have hle : 𝒜 ≤ ℬ := le_def.2 fun B hB ↦ mem_carrier.1 (hℬ ▸ mem_insert_of_mem A hB)
    refine ⟨lt_of_le_of_ne hle fun heq ↦ hA (heq ▸ hAℬ), fun 𝒞 h𝒜𝒞 h𝒞ℬ ↦ ?_⟩
    by_cases hA𝒞 : A ∈ 𝒞
    · refine h𝒞ℬ.not_ge (le_def.2 fun B hB ↦ ?_)
      rcases (hℬ ▸ mem_carrier.2 hB : B ∈ insert A 𝒜.carrier) with rfl | hB
      exacts [hA𝒞, le_def.1 h𝒜𝒞.le hB]
    · refine h𝒜𝒞.not_ge (le_def.2 fun B hB ↦ ?_)
      rcases (hℬ ▸ mem_carrier.2 (le_def.1 h𝒞ℬ.le hB) : B ∈ insert A 𝒜.carrier) with rfl | hB
      exacts [absurd hB hA𝒞, hB]

/-- The lattice of closure systems of extents is lower semimodular. -/
instance : IsLowerModularLattice (ClosureSubsystem r) where
  inf_covBy_of_covBy_sup {𝒜 ℬ} h := by
    obtain ⟨A, hA, hsup⟩ := covBy_iff.1 h
    have hsub : ∀ B ∈ ℬ, B = A ∨ B ∈ 𝒜 := fun B hB ↦
      (hsup ▸ mem_carrier.2 (le_def.1 le_sup_right hB) : B ∈ insert A 𝒜.carrier)
    have hAℬ : A ∈ ℬ := by
      by_contra hAℬ
      have hle : ℬ ≤ 𝒜 := le_def.2 fun B hB ↦ (hsub B hB).resolve_left fun h ↦ hAℬ (h ▸ hB)
      exact h.lt.ne (sup_eq_left.2 hle).symm
    refine covBy_iff.2 ⟨A, fun h ↦ hA (mem_inf.1 h).1, Set.ext fun B ↦ ?_⟩
    simp only [mem_carrier, mem_insert_iff, mem_inf]
    refine ⟨fun hB ↦ (hsub B hB).imp_right fun h ↦ ⟨h, hB⟩, ?_⟩
    rintro (rfl | hB)
    exacts [hAℬ, hB.2]

section Finite

variable [Finite α]

/-- A cover in the lattice of closure systems of extents has exactly one closed set more. -/
theorem ncard_carrier_of_covBy (h : 𝒜 ⋖ ℬ) : ℬ.carrier.ncard = 𝒜.carrier.ncard + 1 := by
  obtain ⟨A, hA, hℬ⟩ := covBy_iff.1 h
  rw [hℬ, ncard_insert_of_notMem hA]

theorem ncard_carrier_pos (𝒜 : ClosureSubsystem r) : 0 < 𝒜.carrier.ncard :=
  (ncard_pos).2 ⟨univ, 𝒜.univ_mem⟩

/-- For a finite context the lattice of closure systems of extents is graded: the rank of a
closure system `𝒜` is `|𝒜| - 1`. -/
noncomputable instance : GradeMinOrder ℕ (ClosureSubsystem r) where
  grade 𝒜 := 𝒜.carrier.ncard - 1
  grade_strictMono 𝒜 ℬ h := by
    have := ncard_lt_ncard (show 𝒜.carrier ⊂ ℬ.carrier from h)
    have := ncard_carrier_pos 𝒜
    lia
  covBy_grade 𝒜 ℬ h := by
    have := ncard_carrier_of_covBy h
    have := ncard_carrier_pos 𝒜
    rw [Nat.covBy_iff_add_one_eq]
    lia
  isMin_grade 𝒜 h := by
    rw [h.eq_bot, bot_eq]
    simp [trivial]

theorem grade_eq (𝒜 : ClosureSubsystem r) : grade ℕ 𝒜 = 𝒜.carrier.ncard - 1 :=
  rfl

end Finite

/-! ### Coatoms -/

/-- The closure system of all extents except `A`, where `A` is not an intersection of other
extents. -/
def erase (A : Set α) (hA : ⋂₀ {B | IsExtent r B ∧ A ⊂ B} ≠ A) : ClosureSubsystem r where
  carrier := {B | IsExtent r B ∧ B ≠ A}
  sInter_mem' S hS := by
    refine ⟨.sInter fun B hB ↦ (hS hB).1, fun heq ↦ hA (Subset.antisymm ?_ ?_)⟩
    · refine (sInter_subset_sInter fun B hB ↦ ?_).trans heq.subset
      have hAB : A ⊆ B := heq ▸ sInter_subset_of_mem hB
      exact ⟨(hS hB).1, hAB.ssubset_of_ne (hS hB).2.symm⟩
    · exact subset_sInter fun B hB ↦ hB.2.subset
  isExtent' _ hB := hB.1

@[simp]
theorem mem_erase {hA : ⋂₀ {B | IsExtent r B ∧ A ⊂ B} ≠ A} :
    B ∈ erase A hA ↔ IsExtent r B ∧ B ≠ A :=
  Iff.rfl

/-- The coatoms of the lattice of closure systems of extents are obtained by removing an extent
that is not an intersection of other extents. -/
theorem isCoatom_iff : IsCoatom 𝒜 ↔ ∃ A, IsExtent r A ∧ ⋂₀ {B | IsExtent r B ∧ A ⊂ B} ≠ A ∧
    𝒜.carrier = {B | IsExtent r B ∧ B ≠ A} := by
  rw [← covBy_top_iff, covBy_iff]
  constructor
  · rintro ⟨A, hA, htop⟩
    have hmem : ∀ B, IsExtent r B → B = A ∨ B ∈ 𝒜 := fun B hB ↦
      (htop ▸ mem_carrier.2 (mem_top.2 hB) : B ∈ insert A 𝒜.carrier)
    refine ⟨A, mem_top.1 (mem_carrier.1 (htop ▸ mem_insert A _)), fun heq ↦ hA ?_, ?_⟩
    · rw [← heq]
      exact 𝒜.sInter_mem fun B hB ↦ (hmem B hB.1).resolve_left hB.2.ne'
    · ext B
      exact ⟨fun hB ↦ ⟨𝒜.isExtent hB, fun h ↦ hA (h ▸ hB)⟩,
        fun hB ↦ (hmem B hB.1).resolve_left hB.2⟩
  · rintro ⟨A, hA, -, h𝒜⟩
    refine ⟨A, fun h ↦ (h𝒜 ▸ mem_carrier.2 h : A ∈ {B | IsExtent r B ∧ B ≠ A}).2 rfl, ?_⟩
    ext B
    rw [mem_carrier, mem_top, h𝒜, mem_insert_iff]
    by_cases hB : B = A
    · simp [hB, hA]
    · simp [hB]

theorem isCoatom_erase {hA : ⋂₀ {B | IsExtent r B ∧ A ⊂ B} ≠ A} (hA' : IsExtent r A) :
    IsCoatom (erase A hA) :=
  isCoatom_iff.2 ⟨A, hA', hA, rfl⟩

/-! ### Meet-irreducible elements -/

/-- The closure system of all extents `B` that respect the implication `A → C` between sets of
objects: if `A ⊆ B` then `C ⊆ B`. -/
def respecting (r : α → β → Prop) (A C : Set α) : ClosureSubsystem r where
  carrier := {B | IsExtent r B ∧ (A ⊆ B → C ⊆ B)}
  sInter_mem' _ hS := ⟨.sInter fun _ hB ↦ (hS hB).1, fun h ↦
    subset_sInter fun _ hB ↦ (hS hB).2 (h.trans (sInter_subset_of_mem hB))⟩
  isExtent' _ hB := hB.1

@[simp]
theorem mem_respecting : B ∈ respecting r A C ↔ IsExtent r B ∧ (A ⊆ B → C ⊆ B) :=
  Iff.rfl

theorem le_respecting_iff : 𝒜 ≤ respecting r A C ↔ ∀ B ∈ 𝒜, A ⊆ B → C ⊆ B :=
  ⟨fun h _ hB ↦ (le_def.1 h hB).2, fun h ↦ le_def.2 fun B hB ↦ ⟨𝒜.isExtent hB, h B hB⟩⟩

theorem notMem_respecting (h : A ⊂ C) : A ∉ respecting r A C :=
  fun hA ↦ h.not_subset (hA.2 Subset.rfl)

/-- Splitting an implication at an intermediate set. -/
theorem respecting_inf_respecting {D : Set α} (hAD : A ⊆ D) (hDC : D ⊆ C) :
    respecting r A D ⊓ respecting r D C = respecting r A C := by
  ext B
  simp only [mem_carrier, mem_inf, mem_respecting]
  exact ⟨fun h ↦ ⟨h.1.1, fun hA ↦ h.2.2 (h.1.2 hA)⟩, fun h ↦
    ⟨⟨h.1, fun hA ↦ hDC.trans (h.2 hA)⟩, h.1, fun hD ↦ h.2 (hAD.trans hD)⟩⟩

/-- A pair of extents `A ⊂ C` is determined by the closure system `respecting r A C`. -/
theorem respecting_inj {A' C' : Set α} (hA : IsExtent r A) (hC : IsExtent r C) (hAC : A ⊂ C)
    (hA' : IsExtent r A') (hC' : IsExtent r C') (hAC' : A' ⊂ C') :
    respecting r A C = respecting r A' C' ↔ A = A' ∧ C = C' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h.1, h.2]⟩
  have h₁ : A' ⊆ A := by
    by_contra hsub
    have hmem : A ∈ respecting r A' C' := ⟨hA, fun h' ↦ absurd h' hsub⟩
    rw [← h] at hmem
    exact notMem_respecting hAC hmem
  have h₂ : A ⊆ A' := by
    by_contra hsub
    have hmem : A' ∈ respecting r A C := ⟨hA', fun h' ↦ absurd h' hsub⟩
    rw [h] at hmem
    exact notMem_respecting hAC' hmem
  obtain rfl := Subset.antisymm h₂ h₁
  have h₃ : C ∈ respecting r A C' := h ▸ ⟨hC, fun _ ↦ Subset.rfl⟩
  have h₄ : C' ∈ respecting r A C := h ▸ ⟨hC', fun _ ↦ Subset.rfl⟩
  exact ⟨rfl, Subset.antisymm (h₄.2 hAC'.subset) (h₃.2 hAC.subset)⟩

/-- If `C` covers `A` among the extents, every closure system strictly above
`respecting r A C` contains `A`. -/
theorem mem_of_respecting_lt (hC : IsExtent r C) (hAC : A ⊆ C)
    (hcov : ∀ D, IsExtent r D → A ⊆ D → D ⊆ C → D = A ∨ D = C)
    (h : respecting r A C < 𝒜) : A ∈ 𝒜 := by
  obtain ⟨B, hB, hB'⟩ : ∃ B ∈ 𝒜, B ∉ respecting r A C := by
    by_contra! hall
    exact h.not_ge (le_def.2 hall)
  have hB' : A ⊆ B ∧ ¬C ⊆ B := by
    simpa [mem_respecting, 𝒜.isExtent hB] using hB'
  have hC𝒜 : C ∈ 𝒜 := le_def.1 h.le ⟨hC, fun _ ↦ Subset.rfl⟩
  rcases hcov (B ∩ C) ((𝒜.isExtent hB).inter hC) (subset_inter hB'.1 hAC) inter_subset_right
    with heq | heq
  · exact heq ▸ inter_mem hB hC𝒜
  · exact absurd (inter_eq_right.1 heq) hB'.2

/-- For extents `A ⊂ C`, the closure system `respecting r A C` is meet-irreducible if and only
if `C` covers `A` among the extents. -/
theorem infIrred_respecting_iff (hA : IsExtent r A) (hC : IsExtent r C) (hAC : A ⊂ C) :
    InfIrred (respecting r A C) ↔
      ∀ D, IsExtent r D → A ⊆ D → D ⊆ C → D = A ∨ D = C := by
  constructor
  · intro h D hD hAD hDC
    by_contra! hne
    rcases h.2 (respecting_inf_respecting hAD hDC) with heq | heq
    · have hD' : D ∈ respecting r A C := heq ▸ ⟨hD, fun _ ↦ Subset.rfl⟩
      exact hne.2 (Subset.antisymm hDC (hD'.2 hAD))
    · have hA' : A ∈ respecting r D C :=
        ⟨hA, fun h' ↦ absurd (Subset.antisymm h' hAD) hne.1⟩
      exact notMem_respecting hAC (heq ▸ hA')
  · intro hcov
    refine ⟨not_isMax_iff_ne_top.2 fun htop ↦ notMem_respecting hAC (htop ▸ mem_top.2 hA),
      fun ℬ 𝒞 hinf ↦ ?_⟩
    by_contra! hne
    have hℬ : respecting r A C < ℬ := lt_of_le_of_ne (hinf ▸ inf_le_left) hne.1.symm
    have h𝒞 : respecting r A C < 𝒞 := lt_of_le_of_ne (hinf ▸ inf_le_right) hne.2.symm
    exact notMem_respecting hAC (hinf ▸ mem_inf.2
      ⟨mem_of_respecting_lt hC hAC.subset hcov hℬ, mem_of_respecting_lt hC hAC.subset hcov h𝒞⟩)

/-- For concepts `c < d`, the closure system `respecting r c.extent d.extent` is meet-irreducible
if and only if `d` covers `c`. -/
theorem infIrred_respecting_extent_iff {c d : Concept α β r} (h : c < d) :
    InfIrred (respecting r c.extent d.extent) ↔ c ⋖ d := by
  have hlt := Concept.extent_ssubset_extent_iff.2 h
  rw [infIrred_respecting_iff c.isExtent_extent d.isExtent_extent hlt, Concept.covBy_iff_extent]
  exact (and_iff_right hlt).symm

/-- The closure of a set of objects in a closure system. -/
def closure (𝒜 : ClosureSubsystem r) (A : Set α) : Set α :=
  ⋂₀ {B | B ∈ 𝒜 ∧ A ⊆ B}

theorem subset_closure : A ⊆ 𝒜.closure A :=
  subset_sInter fun _ hB ↦ hB.2

theorem closure_mem : 𝒜.closure A ∈ 𝒜 :=
  𝒜.sInter_mem fun _ hB ↦ hB.1

theorem closure_subset (hB : B ∈ 𝒜) (h : A ⊆ B) : 𝒜.closure A ⊆ B :=
  sInter_subset_of_mem ⟨hB, h⟩

theorem closure_eq_self_iff : 𝒜.closure A = A ↔ A ∈ 𝒜 :=
  ⟨fun h ↦ h ▸ closure_mem, fun h ↦ Subset.antisymm (closure_subset h Subset.rfl) subset_closure⟩

/-- Every closure system of extents is the infimum of the closure systems `respecting r A C`,
where `A` ranges over the extents it misses and `C` is the closure of `A`. -/
theorem sInf_respecting_closure (𝒜 : ClosureSubsystem r) :
    sInf {ℳ | ∃ A, IsExtent r A ∧ A ∉ 𝒜 ∧ ℳ = respecting r A (𝒜.closure A)} = 𝒜 := by
  ext B
  rw [mem_carrier, mem_carrier, mem_sInf]
  constructor
  · rintro ⟨hB, h⟩
    by_contra hB'
    exact hB' (closure_eq_self_iff.1 (Subset.antisymm
      ((h _ ⟨B, hB, hB', rfl⟩).2 Subset.rfl) subset_closure))
  · rintro hB
    refine ⟨𝒜.isExtent hB, ?_⟩
    rintro _ ⟨A, -, -, rfl⟩
    exact ⟨𝒜.isExtent hB, closure_subset hB⟩

/-- For a finite context, every meet-irreducible closure system of extents consists of the
extents respecting an implication `A → C`, where `C` covers `A` among the extents. -/
theorem InfIrred.exists_respecting [Finite α] (h : InfIrred 𝒜) :
    ∃ A C, IsExtent r A ∧ IsExtent r C ∧ A ⊂ C ∧
      (∀ D, IsExtent r D → A ⊆ D → D ⊆ C → D = A ∨ D = C) ∧ 𝒜 = respecting r A C := by
  have hfin := toFinite {ℳ | ∃ A, IsExtent r A ∧ A ∉ 𝒜 ∧ ℳ = respecting r A (𝒜.closure A)}
  obtain ⟨ℳ, hℳ, rfl⟩ := h.finset_inf_eq (s := hfin.toFinset) (f := id) (by
    rw [Finset.inf_id_eq_sInf, hfin.coe_toFinset, sInf_respecting_closure])
  obtain ⟨A, hA, hA', hℳ⟩ := hfin.mem_toFinset.1 hℳ
  have hC : IsExtent r ((id ℳ).closure A) := (id ℳ).isExtent closure_mem
  have hAC : A ⊂ (id ℳ).closure A :=
    subset_closure.ssubset_of_ne fun heq ↦ hA' (closure_eq_self_iff.1 heq.symm)
  refine ⟨A, _, hA, hC, hAC, ?_, hℳ⟩
  rw [← infIrred_respecting_iff hA hC hAC, ← hℳ]
  exact h

/-- For a finite context, the covering pairs of the concept lattice correspond bijectively to
the meet-irreducible elements of the lattice of closure systems of extents. -/
noncomputable def infIrredEquiv [Finite α] (r : α → β → Prop) :
    {p : Concept α β r × Concept α β r // p.1 ⋖ p.2} ≃ {𝒜 : ClosureSubsystem r // InfIrred 𝒜} :=
  Equiv.ofBijective
    (fun p ↦ ⟨respecting r p.1.1.extent p.1.2.extent,
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
    (infIrredEquiv r p : ClosureSubsystem r) = respecting r p.1.1.extent p.1.2.extent :=
  rfl

/-- For a finite context, the number of meet-irreducible elements of the lattice of closure
systems of extents is the number of covering pairs of the concept lattice. -/
theorem natCard_infIrred [Finite α] (r : α → β → Prop) :
    Nat.card {𝒜 : ClosureSubsystem r // InfIrred 𝒜} =
      Nat.card {p : Concept α β r × Concept α β r // p.1 ⋖ p.2} :=
  Nat.card_congr (infIrredEquiv r).symm

/-! ### Distributivity -/

/-- If the extents form a chain, the join of two closure systems of extents is their union. -/
theorem mem_sup_of_total (h : ∀ A B, IsExtent r A → IsExtent r B → A ⊆ B ∨ B ⊆ A) :
    A ∈ 𝒜 ⊔ ℬ ↔ A ∈ 𝒜 ∨ A ∈ ℬ := by
  refine ⟨fun hA ↦ ?_, fun hA ↦ hA.elim (le_def.1 le_sup_left ·) (le_def.1 le_sup_right ·)⟩
  obtain ⟨A₁, h₁, A₂, h₂, rfl⟩ := mem_sup.1 hA
  rcases h A₁ A₂ (𝒜.isExtent h₁) (ℬ.isExtent h₂) with h' | h'
  · exact .inl (by rwa [inter_eq_left.2 h'])
  · exact .inr (by rwa [inter_eq_right.2 h'])

/-- The lattice of closure systems of extents is distributive if and only if the extents form a
chain. -/
theorem sup_inf_le_iff_total :
    (∀ 𝒜 ℬ 𝒞 : ClosureSubsystem r, (𝒜 ⊔ ℬ) ⊓ (𝒜 ⊔ 𝒞) ≤ 𝒜 ⊔ ℬ ⊓ 𝒞) ↔
      ∀ A B, IsExtent r A → IsExtent r B → A ⊆ B ∨ B ⊆ A := by
  constructor
  · intro h A B hA hB
    by_contra! hne
    have hmem : A ∩ B ∈ pair A hA ⊔ pair B hB ⊓ pair (A ∩ B) (hA.inter hB) :=
      le_def.1 (h _ _ _) (mem_inf.2 ⟨mem_sup.2 ⟨A, self_mem_pair, B, self_mem_pair, rfl⟩,
        le_def.1 le_sup_right self_mem_pair⟩)
    obtain ⟨A₁, h₁, A₂, h₂, heq⟩ := mem_sup.1 hmem
    have hA₂ : A₂ = univ := by
      rcases (mem_inf.1 h₂).1 with h' | rfl
      · exact h'
      rcases (mem_inf.1 h₂).2 with h' | h'
      · exact h'
      · exact absurd (inter_eq_right.1 h'.symm) hne.2
    rw [hA₂, inter_univ] at heq
    rcases h₁ with rfl | rfl
    · exact hne.1 fun x _ ↦ (heq ▸ mem_univ x : x ∈ A ∩ B).2
    · exact hne.1 (inter_eq_left.1 heq.symm)
  · intro h 𝒜 ℬ 𝒞
    refine le_def.2 fun A hA ↦ ?_
    simp only [mem_inf, mem_sup_of_total h] at hA ⊢
    tauto

/-- If the extents form a chain, the lattice of closure systems of extents is distributive. -/
@[implicit_reducible]
def distribLattice (h : ∀ A B, IsExtent r A → IsExtent r B → A ⊆ B ∨ B ⊆ A) :
    DistribLattice (ClosureSubsystem r) :=
  { (inferInstance : Lattice (ClosureSubsystem r)) with
    le_sup_inf := (sup_inf_le_iff_total.2 h) }

/-! ### Join-semidistributivity -/

/-- For a finite context the lattice of closure systems of extents is join-semidistributive. -/
theorem sup_eq_sup_inf_of_sup_eq_sup [Finite α] (h : 𝒜 ⊔ ℬ = 𝒜 ⊔ 𝒞) :
    𝒜 ⊔ ℬ = 𝒜 ⊔ ℬ ⊓ 𝒞 := by
  refine le_antisymm (le_def.2 fun D ↦ ?_) (sup_le_sup_left inf_le_left _)
  refine WellFoundedGT.induction (motive := fun D ↦ D ∈ 𝒜 ⊔ ℬ → D ∈ 𝒜 ⊔ ℬ ⊓ 𝒞) D fun D ih hD ↦ ?_
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_sup.1 hD
  obtain ⟨A', hA', C, hC, hAC⟩ := mem_sup.1 (h ▸ hD)
  by_cases h₁ : D = B
  · by_cases h₂ : D = C
    · exact le_def.1 le_sup_right (mem_inf.2 ⟨h₁ ▸ hB, h₂ ▸ hC⟩)
    · have hlt : D ⊂ C := (hAC ▸ inter_subset_right).ssubset_of_ne h₂
      have hC' : C ∈ 𝒜 ⊔ ℬ := h ▸ le_def.1 le_sup_right hC
      exact hAC ▸ inter_mem (le_def.1 le_sup_left hA') (ih C hlt hC')
  · have hlt : D ⊂ B := (hAB ▸ inter_subset_right).ssubset_of_ne h₁
    exact hAB ▸ inter_mem (le_def.1 le_sup_left hA) (ih B hlt (le_def.1 le_sup_right hB))

/-! ### Meet-distributivity -/

/-- The closed sets of `ℬ` that are not intersections of other closed sets of `ℬ`. -/
def irreducibles (ℬ : ClosureSubsystem r) : Set (Set α) :=
  {A | A ∈ ℬ ∧ ⋂₀ {B | B ∈ ℬ ∧ A ⊂ B} ≠ A}

/-- The closure system obtained from `ℬ` by keeping, among its irreducible closed sets, only
those in `J`. -/
def restrictIrreducibles (ℬ : ClosureSubsystem r) (J : Set (Set α)) : ClosureSubsystem r where
  carrier := {B | B ∈ ℬ ∧ (B ∈ ℬ.irreducibles → B ∈ J)}
  sInter_mem' S hS := by
    refine ⟨ℬ.sInter_mem fun B hB ↦ (hS hB).1, fun hirr ↦ ?_⟩
    by_cases hmem : ⋂₀ S ∈ S
    · exact (hS hmem).2 hirr
    · refine absurd (Subset.antisymm ?_ (subset_sInter fun B hB ↦ hB.2.subset)) hirr.2
      refine sInter_subset_sInter fun B hB ↦ ⟨(hS hB).1, ?_⟩
      exact (sInter_subset_of_mem hB).ssubset_of_ne fun heq ↦ hmem (heq ▸ hB)
  isExtent' _ hB := ℬ.isExtent hB.1

@[simp]
theorem mem_restrictIrreducibles {J : Set (Set α)} :
    B ∈ ℬ.restrictIrreducibles J ↔ B ∈ ℬ ∧ (B ∈ ℬ.irreducibles → B ∈ J) :=
  Iff.rfl

theorem restrictIrreducibles_le {J : Set (Set α)} : ℬ.restrictIrreducibles J ≤ ℬ :=
  le_def.2 fun _ hB ↦ hB.1

/-- Removing one irreducible closed set yields a lower cover. -/
theorem restrictIrreducibles_covBy (hA : A ∈ ℬ.irreducibles) :
    ℬ.restrictIrreducibles (ℬ.irreducibles \ {A}) ⋖ ℬ := by
  refine covBy_iff.2 ⟨A, fun h ↦ (h.2 hA).2 rfl, Set.ext fun B ↦ ?_⟩
  simp only [mem_carrier, mem_insert_iff, mem_restrictIrreducibles, mem_sdiff,
    mem_singleton_iff]
  by_cases hB : B = A
  · simp [hB, hA.1]
  · simp [hB]

/-- The lower covers of `ℬ` are obtained by removing one irreducible closed set. -/
theorem covBy_iff_exists_irreducibles :
    𝒜 ⋖ ℬ ↔ ∃ A ∈ ℬ.irreducibles, 𝒜.carrier = {B | B ∈ ℬ ∧ B ≠ A} := by
  constructor
  · intro h
    obtain ⟨A, hA, hℬ⟩ := covBy_iff.1 h
    have hmem : ∀ B, B ∈ ℬ → B = A ∨ B ∈ 𝒜 := fun B hB ↦
      (hℬ ▸ mem_carrier.2 hB : B ∈ insert A 𝒜.carrier)
    refine ⟨A, ⟨mem_carrier.1 (hℬ ▸ mem_insert A _), fun heq ↦ hA ?_⟩, Set.ext fun B ↦
      ⟨fun hB ↦ ⟨le_def.1 h.le hB, fun h' ↦ hA (h' ▸ hB)⟩,
        fun hB ↦ (hmem B hB.1).resolve_left hB.2⟩⟩
    rw [← heq]
    exact 𝒜.sInter_mem fun B hB ↦ (hmem B hB.1).resolve_left hB.2.ne'
  · rintro ⟨A, hA, h𝒜⟩
    convert restrictIrreducibles_covBy hA using 1
    refine ClosureSubsystem.ext (h𝒜.trans (Set.ext fun B ↦ ?_))
    simp only [mem_ofPred, mem_carrier, mem_restrictIrreducibles, mem_sdiff, mem_singleton_iff]
    refine and_congr_right fun hB ↦ ⟨fun h _ ↦ ⟨‹_›, h⟩, fun h hBA ↦ (h (hBA ▸ hA)).2 hBA⟩

/-- The closure system of the closed sets of `ℬ` that are intersections of other closed sets. -/
def core (ℬ : ClosureSubsystem r) : ClosureSubsystem r :=
  ℬ.restrictIrreducibles ∅

theorem mem_core : B ∈ ℬ.core ↔ B ∈ ℬ ∧ B ∉ ℬ.irreducibles :=
  Iff.rfl

/-- The core of `ℬ` is the meet of the lower covers of `ℬ`. -/
theorem core_eq_inf_sInf_covBy (ℬ : ClosureSubsystem r) : ℬ.core = ℬ ⊓ sInf {𝒜 | 𝒜 ⋖ ℬ} := by
  ext B
  rw [mem_carrier, mem_carrier, mem_inf, mem_sInf, mem_core]
  refine and_congr_right fun hB ↦ ⟨fun hirr ↦ ⟨ℬ.isExtent hB, fun 𝒜 h𝒜 ↦ ?_⟩, fun h hirr ↦ ?_⟩
  · obtain ⟨A, hA, h𝒜⟩ := covBy_iff_exists_irreducibles.1 h𝒜
    exact mem_carrier.1 (h𝒜 ▸ ⟨hB, fun h ↦ hirr (h ▸ hA)⟩)
  · exact ((h.2 _ (restrictIrreducibles_covBy hirr)).2 hirr).2 rfl

/-- The lattice of closure systems of extents is **meet-distributive**: the interval between a
closure system `ℬ` and the meet of its lower covers is a Boolean lattice, namely the powerset of
the irreducible closed sets of `ℬ`. -/
def IccCoreIso (ℬ : ClosureSubsystem r) : Set.Icc ℬ.core ℬ ≃o Set ℬ.irreducibles :=
  Equiv.toOrderIso
    { toFun 𝒜 := {A | A.1 ∈ 𝒜.1}
      invFun J := ⟨ℬ.restrictIrreducibles (Subtype.val '' J),
        le_def.2 fun _ hB ↦ ⟨hB.1, fun h ↦ absurd h hB.2⟩, restrictIrreducibles_le⟩
      left_inv 𝒜 := by
        refine Subtype.ext (ClosureSubsystem.ext (Set.ext fun B ↦ ⟨fun hB ↦ ?_, fun hB ↦
          ⟨le_def.1 𝒜.2.2 hB, fun h ↦ ⟨⟨B, h⟩, hB, rfl⟩⟩⟩))
        by_cases hirr : B ∈ ℬ.irreducibles
        · obtain ⟨A, hA, rfl⟩ := hB.2 hirr
          exact hA
        · exact le_def.1 𝒜.2.1 ⟨hB.1, hirr⟩
      right_inv J := by
        ext A
        refine ⟨fun h ↦ ?_, fun h ↦ ⟨A.2.1, fun _ ↦ ⟨A, h, rfl⟩⟩⟩
        obtain ⟨A', hA', heq⟩ := h.2 A.2
        exact Subtype.ext heq ▸ hA' }
    (fun _ _ h _ hA ↦ le_def.1 h hA)
    (fun _ _ h ↦ le_def.2 fun _ hB ↦ ⟨hB.1, fun hirr ↦ image_mono h (hB.2 hirr)⟩)

end ClosureSubsystem

end FCA
