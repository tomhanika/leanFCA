/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA

/-!
# Tests for scale-measures

Examples exercising `FCA.ScaleMeasure`: measures between standard scales, the counterexamples
of Hanika and Hirth for disjunctive and negated attributes, the scale-hierarchy, and Ferrers
covers.
-/

@[expose] public section

namespace FCATest.ScaleMeasure

open FCA Order Set

/-! ### Measures between standard scales -/

/-- Every map into any scale is a measure of the contranominal scale, since all sets are extents
of the latter. In particular the identity measures the Boolean context into the nominal scale. -/
example : IsScaleMeasure (α := Fin 3) (· ≠ ·) (· = ·) id :=
  fun _ _ ↦ isExtent_ne _

/-- The converse fails: `{0, 1}` is an extent of the contranominal scale but not of the nominal
scale, so the identity is not a measure of the nominal scale into the contranominal one. -/
example : ¬IsScaleMeasure (α := Fin 3) (· = ·) (· ≠ ·) id := by
  intro h
  have h01 : IsExtent (α := Fin 3) (· = ·) {0, 1} := h (isExtent_ne {0, 1})
  have h2 : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by
    rw [← h01.eq]
    intro m hm
    have h0 : (0 : Fin 3) = m := hm (a := 0) (by simp)
    have h1 : (1 : Fin 3) = m := hm (a := 1) (by simp)
    exact absurd (h0.trans h1.symm) (by decide)
  simp at h2

/-- The identity is a full scale-measure of every context into itself. -/
example : IsFullScaleMeasure (α := Fin 3) (· ≤ ·) (· ≤ ·) id :=
  isFullScaleMeasure_id _

/-- Scale-measures compose. -/
example {σ : Fin 4 → Fin 3} (h : IsScaleMeasure (· ≤ ·) (· ≤ ·) σ) :
    IsScaleMeasure (α := Fin 4) (· ≤ ·) (· = ·) σ → IsScaleMeasure (· ≤ ·) (· ≤ ·) (id ∘ σ) :=
  fun _ ↦ (isScaleMeasure_id _).comp h

/-! ### Attribute projection and apposition -/

/-- Dropping attributes yields a scale-measure. -/
example : IsScaleMeasure (α := Fin 4) (· ≤ ·) (restrictAttributes (· ≤ ·) {1, 3}) id :=
  isScaleMeasure_id_restrictAttributes _ _

/-- Two attribute projections can be combined by apposition. -/
example : IsScaleMeasure (α := Fin 4) (· ≤ ·)
    (apposition (restrictAttributes (· ≤ ·) {1}) (restrictAttributes (· ≤ ·) {3})) id :=
  (isScaleMeasure_id_restrictAttributes _ _).apposition (isScaleMeasure_id_restrictAttributes _ _)

/-- Attribute projection is coarser than the identity measure. -/
example : ScaleCoarser (α := Fin 4) (restrictAttributes (· ≤ ·) {1, 3}) id (· ≤ ·) id :=
  (isScaleMeasure_id_restrictAttributes _ _).scaleCoarser_id

/-! ### Logical attributes -/

open Formula in
/-- A conjunction of attributes always yields a scale-measure. -/
example : IsScaleMeasure (α := Fin 4) (· ≤ ·)
    (restrictAttributes (logicalScale (· ≤ ·)) {and (var 1) (var 2), var 3}) id :=
  isScaleMeasure_logicalScale_of_isConjunctive <| by
    rintro φ (rfl | rfl) <;> simp [IsConjunctive]

open Formula in
/-- The extent of a conjunctive formula. -/
example : (and (var 1) (var 2)).extent (α := Fin 4) (· ≤ ·) = lowerPolar (· ≤ ·) {1, 2} := by
  rw [extent_of_isConjunctive (by simp [IsConjunctive])]
  simp [vars]

open Formula in
/-- Figure 4 of Hanika and Hirth: in the nominal scale on three objects, the disjunction `A ∨ B`
does not yield a scale-measure. -/
example : ¬IsScaleMeasure (α := Fin 3) (· = ·)
    (restrictAttributes (logicalScale (· = ·)) {or (var 0) (var 1)}) id := by
  rw [isScaleMeasure_logicalScale_singleton_iff]
  exact not_isExtent_extent_or (c := 2) (by decide) (by decide) (by decide)

open Formula in
/-- Figure 4 of Hanika and Hirth: neither does the negation `¬A`. -/
example : ¬IsScaleMeasure (α := Fin 3) (· = ·)
    (restrictAttributes (logicalScale (· = ·)) {not (var 0)}) id := by
  rw [isScaleMeasure_logicalScale_singleton_iff]
  exact not_isExtent_extent_not (b := 1) (c := 2) (by decide) (by decide) (by decide)

/-! ### The scale-hierarchy -/

/-- The identity measure is the top of the scale-hierarchy. -/
example : (isScaleMeasure_id (α := Fin 3) (· ≤ ·)).closureSubsystem = ⊤ :=
  closureSubsystem_id _

/-- Every scale-measure is equivalent to its canonical representation and to its conjunctive
normal form. -/
example (h : IsScaleMeasure (α := Fin 4) (· ≤ ·) (restrictAttributes (· ≤ ·) {1, 3}) id) :
    ScaleEquiv (restrictAttributes (· ≤ ·) {1, 3}) id h.closureSubsystem.context id ∧
      ScaleEquiv (restrictAttributes (· ≤ ·) {1, 3}) id
        h.closureSubsystem.conjunctiveNormalForm id :=
  ⟨h.scaleEquiv_context, h.scaleEquiv_conjunctiveNormalForm⟩

/-- The join of two scale-measures with the same measure map is their apposition. -/
example (h₁ : IsScaleMeasure (α := Fin 4) (· ≤ ·) (restrictAttributes (· ≤ ·) {1}) id)
    (h₂ : IsScaleMeasure (α := Fin 4) (· ≤ ·) (restrictAttributes (· ≤ ·) {3}) id) :
    (h₁.apposition h₂).closureSubsystem = h₁.closureSubsystem ⊔ h₂.closureSubsystem :=
  h₁.closureSubsystem_apposition h₂

/-- The bottom of the hierarchy only reflects the extent of all objects. -/
example (A : Set (Fin 3)) : A ∈ (⊥ : ClosureSubsystem (IsExtent (α := Fin 3) (· ≤ ·))) ↔ A = univ :=
  ClosureSubsystem.mem_bot

/-- The scale-hierarchy is isomorphic to the closure systems of extents; in particular the
canonical measure of the top closure system is the top of the hierarchy. -/
example : scaleHierarchyIso (α := Fin 3) (· ≤ ·) ⊤ = ⊤ :=
  map_top _

/-! ### Ferrers dimension -/

/-- A linear order is a Ferrers relation. -/
example : IsFerrers (α := Fin 4) (· ≤ ·) := by
  intro a b a' b' h h'
  rcases le_total a a' with h₁ | h₁
  · exact .inl (h₁.trans h')
  · exact .inr (h₁.trans h)

/-- Hence the ordinal scale has Ferrers dimension at most one. -/
example : HasFerrersCover (α := Fin 4) (· ≤ ·) (Fin 1) :=
  ⟨fun _ ↦ (· ≤ ·), fun _ a b a' b' h h' ↦ (le_total a a').elim
    (fun h₁ ↦ .inl (h₁.trans h')) (fun h₁ ↦ .inr (h₁.trans h)), fun _ _ ↦ by simp⟩

/-- The apposition of two contexts of Ferrers dimension one has Ferrers dimension at most two. -/
example (h : HasFerrersCover (α := Fin 4) (· ≤ ·) (Fin 1)) :
    HasFerrersCover (apposition (α := Fin 4) (· ≤ ·) (· ≤ ·)) (Fin 2) :=
  h.apposition_fin h

end FCATest.ScaleMeasure
