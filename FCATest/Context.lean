/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Arrows

/-!
# Tests for the structure of contexts

Sanity checks for `FCA.Context`: the contranominal scale `(· ≠ ·)` on `Bool` is clarified and
reduced, and its arrows are exactly the diagonal.
-/

@[expose] public section

open FCA

namespace FCATest

/-- The contranominal scale on two elements. -/
abbrev contra : Bool → Bool → Prop := (· ≠ ·)

example : Clarified contra := by
  constructor
  · rw [objectClarified_iff]
    decide
  · rw [attributeClarified_iff]
    decide

example (a : Bool) : a ⤢[contra] a := by
  refine ⟨⟨by simp, fun a' h ↦ ?_⟩, ⟨by simp, fun b' h ↦ ?_⟩⟩
  · rintro rfl
    exact h.ne rfl
  · rintro rfl
    exact h.ne rfl

example (a : Bool) : ObjectIrreducible contra a :=
  objectIrreducible_iff_exists_downArrow.2
    ⟨a, by simp, fun a' h ↦ by rintro rfl; exact h.ne rfl⟩

example (b : Bool) : AttributeIrreducible contra b :=
  attributeIrreducible_iff_exists_doubleArrow_of_finite.2
    ⟨b, ⟨by simp, fun a' h ↦ by rintro rfl; exact h.ne rfl⟩,
      ⟨by simp, fun b' h ↦ by rintro rfl; exact h.ne rfl⟩⟩

example : complement contra = (· = ·) := by
  ext a b
  simp

example (r : Bool → Bool → Prop) :
    Nonempty (Concept (Bool ⊕ Bool) (Bool ⊕ Bool) (directSum r r) ≃o
      Concept Bool Bool r × Concept Bool Bool r) :=
  ⟨directSumOrderIso r r⟩

end FCATest
