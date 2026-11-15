/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Concept.Dense

/-!
# The basic theorem on concept lattices

Mathlib proves that the concept lattice `Concept α β r` is a complete lattice. This file proves
the second part of the basic theorem on concept lattices (Ganter–Wille, Theorem 3): a complete
lattice `L` is isomorphic to `Concept α β r` if and only if there are maps `γ : α → L` and
`μ : β → L` such that `γ` is supremum-dense, `μ` is infimum-dense, and `r a b ↔ γ a ≤ μ b`.

## Main definitions

* `Concept.ofDense`: the concept associated to an element of `L` by a pair of dense maps.
* `Concept.orderIsoOfDense`: the order isomorphism `Concept α β r ≃o L` induced by a pair of
  dense maps.

## Main results

* `Concept.nonempty_orderIso_iff`: the basic theorem on concept lattices.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set

namespace Concept

variable {α β L : Type*} [CompleteLattice L] {r : α → β → Prop} {γ : α → L} {μ : β → L}

/-- The concept of `r` associated to `x : L` by a supremum-dense map `γ` and an infimum-dense map
`μ` which are compatible with the incidence `r`. -/
@[simps]
def ofDense (γ : α → L) (μ : β → L) (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    Concept α β r where
  extent := {a | γ a ≤ x}
  intent := {b | x ≤ μ b}
  upperPolar_extent := by
    ext b
    refine ⟨fun hb ↦ ?_, fun hb a ha ↦ (h a b).2 (le_trans (mem_ofPred.1 ha) hb)⟩
    exact (hγ x).ge.trans (iSup₂_le fun a ha ↦ (h a b).1 (hb ha))
  lowerPolar_intent := by
    ext a
    refine ⟨fun ha ↦ ?_, fun ha b hb ↦ (h a b).2 (le_trans ha (mem_ofPred.1 hb))⟩
    exact (le_iInf₂ fun b hb ↦ (h a b).1 (ha hb)).trans (hμ x).le

theorem mem_extent_of_le_biSup (h : ∀ a b, r a b ↔ γ a ≤ μ b) {c : Concept α β r} {a : α}
    (ha : γ a ≤ ⨆ a' ∈ c.extent, γ a') : a ∈ c.extent := by
  rw [← c.lowerPolar_intent]
  intro b hb
  exact (h a b).2 (ha.trans (iSup₂_le fun a' ha' ↦ (h a' b).1 (c.rel_extent_intent ha' hb)))

/-- A supremum-dense map `γ : α → L` and an infimum-dense map `μ : β → L` into a complete lattice
with `r a b ↔ γ a ≤ μ b` induce an order isomorphism between the concept lattice of `r` and `L`.
This is the sufficiency part of the **basic theorem on concept lattices**. -/
def orderIsoOfDense (γ : α → L) (μ : β → L) (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b) :
    Concept α β r ≃o L where
  toFun c := ⨆ a ∈ c.extent, γ a
  invFun := ofDense γ μ hγ hμ h
  left_inv c := ext <| Subset.antisymm (fun _ ha ↦ mem_extent_of_le_biSup h ha)
    fun a ha ↦ le_iSup₂ (f := fun a (_ : a ∈ c.extent) ↦ γ a) a ha
  right_inv := hγ
  map_rel_iff' {c d} := by
    refine ⟨fun hcd a ha ↦ mem_extent_of_le_biSup h ?_, fun hcd ↦ biSup_mono fun a ha ↦ hcd ha⟩
    exact (le_iSup₂ (f := fun a (_ : a ∈ c.extent) ↦ γ a) a ha).trans hcd

@[simp]
theorem orderIsoOfDense_apply (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b)
    (c : Concept α β r) : orderIsoOfDense γ μ hγ hμ h c = ⨆ a ∈ c.extent, γ a :=
  rfl

@[simp]
theorem orderIsoOfDense_symm_apply (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b) (x : L) :
    (orderIsoOfDense γ μ hγ hμ h).symm x = ofDense γ μ hγ hμ h x :=
  rfl

/-- The isomorphism induced by dense maps sends object concepts to the image of `γ`. -/
theorem orderIsoOfDense_ofObject (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b) (a : α) :
    orderIsoOfDense γ μ hγ hμ h (ofObject r a) = γ a := by
  rw [← (orderIsoOfDense γ μ hγ hμ h).eq_symm_apply, orderIsoOfDense_symm_apply]
  refine le_antisymm (ofObject_le_iff.2 (le_refl (γ a))) ?_
  rw [← intent_subset_intent_iff]
  intro b hb
  exact (h a b).1 (hb (mem_singleton a))

/-- The isomorphism induced by dense maps sends attribute concepts to the image of `μ`. -/
theorem orderIsoOfDense_ofAttribute (hγ : ∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x)
    (hμ : ∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) (h : ∀ a b, r a b ↔ γ a ≤ μ b) (b : β) :
    orderIsoOfDense γ μ hγ hμ h (ofAttribute r b) = μ b := by
  rw [← (orderIsoOfDense γ μ hγ hμ h).eq_symm_apply, orderIsoOfDense_symm_apply]
  refine le_antisymm ?_ (le_ofAttribute_iff.2 (le_refl (μ b)))
  intro a ha
  exact (h a b).1 (ha (mem_singleton b))

/-- The **basic theorem on concept lattices**: a complete lattice `L` is isomorphic to the concept
lattice of `r` if and only if there are a supremum-dense map `γ : α → L` and an infimum-dense map
`μ : β → L` such that `r a b` is equivalent to `γ a ≤ μ b`. -/
theorem nonempty_orderIso_iff :
    Nonempty (Concept α β r ≃o L) ↔ ∃ (γ : α → L) (μ : β → L),
      (∀ x, ⨆ a, ⨆ (_ : γ a ≤ x), γ a = x) ∧ (∀ x, ⨅ b, ⨅ (_ : x ≤ μ b), μ b = x) ∧
        ∀ a b, r a b ↔ γ a ≤ μ b := by
  refine ⟨fun ⟨e⟩ ↦ ⟨fun a ↦ e (ofObject r a), fun b ↦ e (ofAttribute r b), fun x ↦ ?_,
    fun x ↦ ?_, fun a b ↦ ?_⟩, fun ⟨γ, μ, hγ, hμ, h⟩ ↦ ⟨orderIsoOfDense γ μ hγ hμ h⟩⟩
  · refine le_antisymm (iSup₂_le fun a ha ↦ ha) ?_
    calc x = e (⨆ a ∈ (e.symm x).extent, ofObject r a) := by
          rw [iSup_ofObject_extent, e.apply_symm_apply]
      _ = ⨆ a ∈ (e.symm x).extent, e (ofObject r a) := by simp_rw [e.map_iSup]
      _ ≤ _ := biSup_mono fun a ha ↦ by
          simpa using e.monotone (ofObject_le_iff.2 ha)
  · refine le_antisymm ?_ (le_iInf₂ fun b hb ↦ hb)
    calc _ ≤ ⨅ b ∈ (e.symm x).intent, e (ofAttribute r b) := biInf_mono fun b hb ↦ by
          simpa using e.monotone (le_ofAttribute_iff.2 hb)
      _ = e (⨅ b ∈ (e.symm x).intent, ofAttribute r b) := by simp_rw [e.map_iInf]
      _ = x := by rw [iInf_ofAttribute_intent, e.apply_symm_apply]
  · rw [e.le_iff_le, ofObject_le_ofAttribute_iff]

end Concept
