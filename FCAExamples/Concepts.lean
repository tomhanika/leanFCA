/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCAExamples.Derivation

/-!
# Formal concepts and the concept lattice

A *formal concept* of a context `r` is a pair of a set of objects (the *extent*) and a set of
attributes (the *intent*) which are the derivations of each other. Mathlib's `Concept α β r` is
the type of all concepts of `r`; it is ordered by inclusion of extents and forms a complete
lattice, the *concept lattice*.
-/

@[expose] public section

namespace FCAExamples

open Animal Trait Set Order

/-! ### Concepts of the animals context -/

/-- The concept of birds: to build a concept, give its extent and its intent and prove that each
is the derivation of the other. -/
def birds : Concept Animal Trait animals where
  extent := {duck, eagle}
  intent := {feathers, flies}
  upperPolar_extent := upperPolar_duck_eagle
  lowerPolar_intent := lowerPolar_feathers_flies

/-- The *object concept* of the duck is the least concept containing the duck. Its intent is the
set of all traits of the duck. -/
def duckConcept : Concept Animal Trait animals :=
  Concept.ofObject animals duck

example : swims ∈ duckConcept.intent := by
  rintro a rfl
  rfl

/-- The duck concept is a subconcept of the bird concept: the duck is a bird. -/
example : duckConcept ≤ birds :=
  Concept.ofObjects_le_iff.2 (by simp [birds])

/-- The *attribute concept* of `predator` is the greatest concept having `predator` in its
intent. The incidence relation can be read off from object and attribute concepts. -/
example : Concept.ofObject animals eagle ≤ Concept.ofAttribute animals predator :=
  Concept.ofObject_le_ofAttribute_iff.2 rfl

example : ¬Concept.ofObject animals duck ≤ Concept.ofAttribute animals predator :=
  fun h ↦ Bool.false_ne_true
    ((Concept.ofObject_le_ofAttribute_iff (r := animals) (a := duck) (b := predator)).1 h)

/-- The greatest concept has all objects in its extent. -/
example : (⊤ : Concept Animal Trait animals).extent = univ :=
  Concept.extent_top

/-- No animal has all traits, so the least concept has an empty extent. -/
example : (⊥ : Concept Animal Trait animals).extent = ∅ := by
  ext g
  simp only [Concept.extent_bot, mem_empty_iff_false, iff_false]
  intro h
  have hfur : animals g fur := h (mem_univ _)
  have hfeathers : animals g feathers := h (mem_univ _)
  cases g <;> simp_all [animals, hasTrait]

/-! ### Concepts of an arbitrary context -/

variable {α β : Type*} {r : α → β → Prop} {c d : Concept α β r}

/-- Every object of the extent has every attribute of the intent. -/
example {a : α} {b : β} (ha : a ∈ c.extent) (hb : b ∈ c.intent) : r a b := by
  rw [← c.upperPolar_extent] at hb
  exact hb ha

/-- A concept is determined by its extent. -/
example (h : c.extent = d.extent) : c = d :=
  Concept.ext h

/-- Subconcepts have smaller extents and larger intents. -/
example (h : c ≤ d) : c.extent ⊆ d.extent ∧ d.intent ⊆ c.intent :=
  ⟨Concept.extent_subset_extent_iff.2 h, Concept.intent_subset_intent_iff.2 h⟩

/-- The extent of the meet of two concepts is the intersection of their extents. -/
example : (c ⊓ d).extent = c.extent ∩ d.extent :=
  Concept.extent_inf c d

/-- The extent of an object concept is the double derivation of the object. -/
example (a : α) : (Concept.ofObject r a).extent = lowerPolar r (upperPolar r {a}) :=
  rfl

/-- An object belongs to the extent of a concept iff its object concept lies below it. -/
example {a : α} : Concept.ofObject r a ≤ c ↔ a ∈ c.extent :=
  Concept.ofObject_le_iff

/-! ### A standard scale

In the *ordinal scale* `(· ≤ ·)` on the natural numbers the extents are the sets of numbers
below a bound. -/

example : IsExtent (α := ℕ) (· ≤ ·) {n | n ≤ 3} :=
  ⟨{3}, by ext n; simp⟩

/-- In the *contranominal scale* `(· ≠ ·)` every set is an extent, so its concept lattice is a
powerset lattice. -/
example (s : Set ℕ) : IsExtent (· ≠ ·) s :=
  FCA.isExtent_ne s

end FCAExamples
