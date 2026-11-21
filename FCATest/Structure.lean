/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA

/-!
# Tests for the structure of the scale-hierarchy and for the order dimension

Examples exercising `FCA.ScaleMeasure.Structure`, `FCA.ScaleMeasure.Reconstruction` and
`FCA.Concept.Dimension` on small standard scales.
-/

@[expose] public section

namespace FCATest.Structure

open FCA Order Set

/-! ### Atoms, covers and rank -/

/-- In the contranominal scale every set is an extent, so `{G, {0}}` is an atom of the
scale-hierarchy. -/
example : IsAtom (ClosureSubsystem.pair (r := (· ≠ ·)) ({0} : Set (Fin 3)) (isExtent_ne _)) :=
  ClosureSubsystem.isAtom_pair fun h ↦ by
    have : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := h ▸ mem_univ _
    simp at this

/-- An atom covers the bottom element, and so has rank one. -/
example : grade ℕ (ClosureSubsystem.pair (r := (· ≠ ·)) ({0} : Set (Fin 3)) (isExtent_ne _)) =
    1 := by
  have h : IsAtom (ClosureSubsystem.pair (r := (· ≠ ·)) ({0} : Set (Fin 3)) (isExtent_ne _)) :=
    ClosureSubsystem.isAtom_pair fun h ↦ by
      have : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := h ▸ mem_univ _
      simp at this
  have := ClosureSubsystem.ncard_carrier_of_covBy h.bot_covBy
  rw [ClosureSubsystem.grade_eq, this, ClosureSubsystem.bot_eq]
  simp [ClosureSubsystem.trivial]

/-- The bottom of the scale-hierarchy has rank zero. -/
example : grade ℕ (⊥ : ClosureSubsystem (α := Fin 3) (· ≠ ·)) = 0 :=
  grade_bot

/-- Removing the empty set from the extents of the contranominal scale on two objects does not
yield a coatom: the empty set is the intersection of `{0}` and `{1}`. -/
example : ¬∃ 𝒜 : ClosureSubsystem (α := Fin 2) (· ≠ ·), IsCoatom 𝒜 ∧
    𝒜.carrier = {B | IsExtent (α := Fin 2) (· ≠ ·) B ∧ B ≠ ∅} := by
  rintro ⟨𝒜, -, h⟩
  have h0 : ({0} : Set (Fin 2)) ∈ 𝒜 :=
    (h ▸ ⟨isExtent_ne _, singleton_ne_empty _⟩ : _ ∈ 𝒜.carrier)
  have h1 : ({1} : Set (Fin 2)) ∈ 𝒜 :=
    (h ▸ ⟨isExtent_ne _, singleton_ne_empty _⟩ : _ ∈ 𝒜.carrier)
  have h01 : ({0} ∩ {1} : Set (Fin 2)) ∈ 𝒜.carrier := 𝒜.inter_mem h0 h1
  rw [h] at h01
  exact h01.2 (singleton_inter_eq_empty.2 (by simp))

/-! ### Meet-irreducible elements -/

/-- The number of meet-irreducible scale-measures is the number of covering pairs of the concept
lattice. -/
example : Nat.card {𝒜 : ClosureSubsystem (α := Fin 2) (· ≠ ·) // InfIrred 𝒜} =
    Nat.card {p : Concept (Fin 2) (Fin 2) (· ≠ ·) × Concept (Fin 2) (Fin 2) (· ≠ ·) //
      p.1 ⋖ p.2} :=
  ClosureSubsystem.natCard_infIrred _

/-- The extents of the contranominal scale respecting `∅ → {0}` form a meet-irreducible
scale-measure, since `{0}` covers `∅`. -/
example : InfIrred (ClosureSubsystem.respecting (α := Fin 2) (· ≠ ·) ∅ {0}) := by
  refine (ClosureSubsystem.infIrred_respecting_iff (isExtent_ne _) (isExtent_ne _)
    ((empty_subset _).ssubset_of_ne (singleton_ne_empty _).symm)).2 fun D _ _ hD ↦ ?_
  exact subset_singleton_iff_eq.1 hD

/-! ### Distributivity -/

/-- The extents of the ordinal scale on a chain form a chain, so its scale-hierarchy is
distributive. -/
example (𝒜 ℬ 𝒞 : ClosureSubsystem (α := Fin 3) (· ≤ ·)) : (𝒜 ⊔ ℬ) ⊓ (𝒜 ⊔ 𝒞) ≤ 𝒜 ⊔ ℬ ⊓ 𝒞 := by
  refine ClosureSubsystem.sup_inf_le_iff_total.2 ?_ 𝒜 ℬ 𝒞
  rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
  refine or_iff_not_imp_left.2 fun h b hb s hs ↦ ?_
  obtain ⟨a, ha, ha'⟩ := not_subset.1 h
  have hba : b ≤ a := by
    by_contra hlt
    exact ha' fun t ht ↦ (le_of_not_ge hlt).trans (hb ht)
  exact hba.trans (ha hs)

/-- The scale-hierarchy of the contranominal scale on two objects is not distributive. -/
example : ¬∀ 𝒜 ℬ 𝒞 : ClosureSubsystem (α := Fin 2) (· ≠ ·), (𝒜 ⊔ ℬ) ⊓ (𝒜 ⊔ 𝒞) ≤ 𝒜 ⊔ ℬ ⊓ 𝒞 := by
  rw [ClosureSubsystem.sup_inf_le_iff_total]
  intro h
  rcases h {0} {1} (isExtent_ne _) (isExtent_ne _) with h | h
  · simpa using h (mem_singleton 0)
  · simpa using h (mem_singleton 1)

/-- Join-semidistributivity for a finite context. -/
example (𝒜 ℬ 𝒞 : ClosureSubsystem (α := Fin 3) (· ≠ ·)) (h : 𝒜 ⊔ ℬ = 𝒜 ⊔ 𝒞) :
    𝒜 ⊔ ℬ = 𝒜 ⊔ ℬ ⊓ 𝒞 :=
  ClosureSubsystem.sup_eq_sup_inf_of_sup_eq_sup h

/-- Join-pseudocomplements: there is a least scale-measure whose join with a given one is the
finest scale-measure. -/
example (𝒜 ℬ : ClosureSubsystem (α := Fin 3) (· ≠ ·)) : 𝒜.joinPseudocompl ≤ ℬ ↔ 𝒜 ⊔ ℬ = ⊤ :=
  ClosureSubsystem.joinPseudocompl_le_iff

/-- The join-pseudocomplement of the finest scale-measure is the coarsest one: no irreducible
extent lies outside the finest scale-measure. -/
example : (⊤ : ClosureSubsystem (α := Fin 3) (· ≠ ·)).joinPseudocompl = ⊥ := by
  refine eq_bot_iff.2 (ClosureSubsystem.le_def.2 fun B hB ↦ ClosureSubsystem.mem_bot.2 ?_)
  obtain ⟨T, hT, rfl⟩ := ClosureSubsystem.mem_joinPseudocompl.1 hB
  exact sInter_eq_univ.2 fun A hA ↦ absurd (hT A hA).1.1 (hT A hA).2

/-- The join-pseudocomplement of the coarsest scale-measure contains every irreducible extent,
for instance `{0}ᶜ` in the contranominal scale. -/
example : ({0}ᶜ : Set (Fin 3)) ∈ (⊥ : ClosureSubsystem (α := Fin 3) (· ≠ ·)).joinPseudocompl := by
  have hirr : ({0}ᶜ : Set (Fin 3)) ∈ (⊤ : ClosureSubsystem (α := Fin 3) (· ≠ ·)).irreducibles := by
    refine ⟨ClosureSubsystem.mem_top.2 (isExtent_ne _), fun h ↦ ?_⟩
    have h0 : (0 : Fin 3) ∈ ⋂₀ {B | B ∈ (⊤ : ClosureSubsystem (α := Fin 3) (· ≠ ·)) ∧
        ({0}ᶜ : Set (Fin 3)) ⊂ B} := by
      rintro B ⟨-, hB⟩
      obtain ⟨x, hx, hx'⟩ := exists_of_ssubset hB
      rwa [← of_not_not hx']
    rw [h] at h0
    exact h0 rfl
  refine ClosureSubsystem.mem_joinPseudocompl.2 ⟨{{0}ᶜ}, ?_, sInter_singleton _⟩
  rintro A rfl
  refine ⟨hirr, fun h ↦ ?_⟩
  have : (0 : Fin 3) ∈ ({0}ᶜ : Set (Fin 3)) := ClosureSubsystem.mem_bot.1 h ▸ mem_univ _
  exact this rfl

/-- Meet-distributivity: the interval above the meet of the lower covers is a powerset. -/
example (ℬ : ClosureSubsystem (α := Fin 3) (· ≠ ·)) :
    Nonempty (Set.Icc (ℬ ⊓ sInf {𝒜 | 𝒜 ⋖ ℬ}) ℬ ≃o Set ℬ.irreducibles) :=
  ℬ.core_eq_inf_sInf_covBy ▸ ⟨ℬ.IccCoreIso⟩

/-! ### General lattice properties -/

example : IsJoinSemidistrib (ClosureSubsystem (α := Fin 3) (· ≠ ·)) := inferInstance

example : IsJoinPseudocomplemented (ClosureSubsystem (α := Fin 3) (· ≠ ·)) := inferInstance

example : IsMeetDistrib (ClosureSubsystem (α := ℕ) (· ≤ ·)) := inferInstance

/-- A distributive lattice is join- and meet-semidistributive. -/
example : IsJoinSemidistrib (Set ℕ) ∧ IsMeetSemidistrib (Set ℕ) := ⟨inferInstance, inferInstance⟩

/-- In a Boolean algebra the complement is both pseudocomplements. -/
example (s : Set ℕ) : IsMeetPseudocompl s sᶜ ∧ IsJoinPseudocompl s sᶜ :=
  ⟨isMeetPseudocompl_compl s, by rw [← hnot_eq_compl]; exact isJoinPseudocompl_hnot s⟩

/-- Finite chains are join-pseudocomplemented, as finite join-semidistributive lattices. -/
example : IsJoinPseudocomplemented (Fin 4) := isJoinPseudocomplemented_of_finite

/-! ### Structural properties of concept lattices -/

/-- In the contranominal scale every set is an extent, so extents are closed under unions and
the concept lattice is distributive. -/
example (c d e : Concept ℕ ℕ (· ≠ ·)) : (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e :=
  Concept.sup_inf_le_of_isExtent_union (fun _ _ _ _ ↦ isExtent_ne _) c d e

/-- For a finite context, meet-semidistributivity says that every object has at most one double
arrow, up to attributes with the same extent. -/
example (r : Fin 5 → Fin 5 → Prop) : IsMeetSemidistrib (Concept _ _ r) ↔
    ∀ a b b', DoubleArrow r a b → DoubleArrow r a b' → lowerPolar r {b} = lowerPolar r {b'} :=
  isMeetSemidistrib_iff_doubleArrow (.of_finite_objects r) (.of_finite_objects r)

/-! ### Representability in fragments of propositional logic -/

/-- Every scale-measure of a context with finitely many attributes is representable by
conjunctions. -/
example (𝒜 : ClosureSubsystem (α := Fin 3) (β := Fin 3) (· ≠ ·)) :
    𝒜.IsRepresentable {φ | φ.IsConjunctive} :=
  𝒜.isRepresentable_isConjunctive

/-- Disjunctions do not suffice. -/
example : ¬(ClosureSubsystem.pair ({0} : Set (Fin 3)) isExtent_fork_singleton).IsRepresentable
    {φ | φ.IsDisjunctive} :=
  not_isRepresentable_isDisjunctive_fork

/-! ### The scale-hierarchy does not determine the concept lattice -/

example : ∃ r₁ r₂ : Option Bool → Option Bool → Prop,
    Nonempty (ScaleHierarchy r₁ ≃o ScaleHierarchy r₂) ∧
      IsEmpty (Concept _ _ r₁ ≃o Concept _ _ r₂) :=
  exists_scaleHierarchy_orderIso_and_isEmpty_concept_orderIso

/-! ### Order dimension -/

/-- The powerset of a three-element set has order dimension at most three … -/
example : HasRealizer (Set (Fin 3)) (Fin 3) :=
  hasRealizer_set_iff.2 ⟨.refl _⟩

/-- … and not at most two. -/
example : ¬HasRealizer (Set (Fin 3)) (Fin 2) := by
  rw [hasRealizer_set_iff]
  rintro ⟨e⟩
  simpa using Fintype.card_le_of_embedding e

/-- A context with a Ferrers incidence has a concept lattice of order dimension at most one. -/
example : HasRealizer (Concept (Fin 4) (Fin 4) (· ≤ ·)) (Fin 1) :=
  hasRealizer_concept_iff.2 ⟨fun _ ↦ (· ≤ ·), fun _ a b a' b' h h' ↦ (le_total a a').elim
    (fun h₁ ↦ .inl (h₁.trans h')) (fun h₁ ↦ .inr (h₁.trans h)), fun _ _ ↦ by simp⟩

end FCATest.Structure
