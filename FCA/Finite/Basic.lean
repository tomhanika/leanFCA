/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Concept

/-!
# Computable derivation operators for finite contexts

For a formal context `r : α → β → Prop` on finite types with decidable incidence, this file
provides executable versions of the derivation operators on `Finset`s, and enumerates all intents
and all concepts. Every executable definition comes with a lemma relating it to its
specification from `Mathlib.Order.Concept`.

## Main definitions

* `FCA.upperPolarFinset`, `FCA.lowerPolarFinset`: the derivation operators on finsets.
* `FCA.intentClosureFinset`, `FCA.extentClosureFinset`: the closure operators on finsets.
* `FCA.intents`: the finset of all intents.
* `FCA.concepts`: the finset of all concepts, as pairs `(extent, intent)`.

## Implementation notes

`FCA.intents` filters the whole powerset of the attribute set, which is exponential in the number
of attributes regardless of the number of concepts. It serves as an executable specification; see
`FCA.Algorithm.NextClosure` for the verified enumeration `FCA.intentsList` in lectic order.
-/

@[expose] public section

open Finset Order

namespace FCA

variable {α β : Type*} (r : α → β → Prop) [DecidableRel r]

section Polar

variable [Fintype β]

/-- The attributes shared by all objects of the finset `s`. -/
def upperPolarFinset (s : Finset α) : Finset β :=
  univ.filter fun b => ∀ a ∈ s, r a b

variable {r} in
@[simp]
theorem mem_upperPolarFinset {s : Finset α} {b : β} :
    b ∈ upperPolarFinset r s ↔ ∀ a ∈ s, r a b := by
  simp [upperPolarFinset]

@[simp, norm_cast]
theorem coe_upperPolarFinset (s : Finset α) :
    (upperPolarFinset r s : Set β) = upperPolar r (s : Set α) := by
  ext b
  simp [mem_upperPolar_iff]

end Polar

section Polar

variable [Fintype α]

/-- The objects having all attributes of the finset `t`. -/
def lowerPolarFinset (t : Finset β) : Finset α :=
  univ.filter fun a => ∀ b ∈ t, r a b

variable {r} in
@[simp]
theorem mem_lowerPolarFinset {t : Finset β} {a : α} :
    a ∈ lowerPolarFinset r t ↔ ∀ b ∈ t, r a b := by
  simp [lowerPolarFinset]

@[simp, norm_cast]
theorem coe_lowerPolarFinset (t : Finset β) :
    (lowerPolarFinset r t : Set α) = lowerPolar r (t : Set β) := by
  ext a
  simp [mem_lowerPolar_iff]

end Polar

variable [Fintype α] [Fintype β]

/-- The smallest intent containing the finset `t` of attributes. -/
def intentClosureFinset (t : Finset β) : Finset β :=
  upperPolarFinset r (lowerPolarFinset r t)

/-- The smallest extent containing the finset `s` of objects. -/
def extentClosureFinset (s : Finset α) : Finset α :=
  lowerPolarFinset r (upperPolarFinset r s)

@[simp, norm_cast]
theorem coe_intentClosureFinset (t : Finset β) :
    (intentClosureFinset r t : Set β) = upperPolar r (lowerPolar r (t : Set β)) := by
  rw [intentClosureFinset, coe_upperPolarFinset, coe_lowerPolarFinset]

@[simp, norm_cast]
theorem coe_extentClosureFinset (s : Finset α) :
    (extentClosureFinset r s : Set α) = lowerPolar r (upperPolar r (s : Set α)) := by
  rw [extentClosureFinset, coe_lowerPolarFinset, coe_upperPolarFinset]

variable [DecidableEq β]

/-- The finset of all intents of a finite formal context. -/
def intents : Finset (Finset β) :=
  univ.filter fun t => intentClosureFinset r t = t

variable {r} in
theorem mem_intents {t : Finset β} : t ∈ intents r ↔ IsIntent r (t : Set β) := by
  rw [intents, mem_filter, isIntent_iff, ← coe_intentClosureFinset, coe_inj]
  exact and_iff_right (mem_univ t)

variable [DecidableEq α]

/-- The finset of all concepts of a finite formal context, as pairs `(extent, intent)`. -/
def concepts : Finset (Finset α × Finset β) :=
  (intents r).image fun t => (lowerPolarFinset r t, t)

variable {r} in
theorem mem_concepts {c : Finset α × Finset β} :
    c ∈ concepts r ↔ upperPolarFinset r c.1 = c.2 ∧ lowerPolarFinset r c.2 = c.1 := by
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := mem_image.1 h
    exact ⟨(mem_filter.1 ht).2, rfl⟩
  · rintro ⟨h₁, h₂⟩
    refine mem_image.2 ⟨c.2, mem_filter.2 ⟨mem_univ _, ?_⟩, Prod.ext h₂ rfl⟩
    rw [intentClosureFinset, h₂, h₁]

end FCA
