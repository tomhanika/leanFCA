/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCAExamples.Animals

/-!
# The derivation operators

For a set `s` of objects, `upperPolar r s` (written `s'` in the literature) is the set of
attributes common to all objects of `s`. Dually, for a set `t` of attributes, `lowerPolar r t`
is the set of objects having all attributes of `t`. Both are defined in Mathlib:

* `b ∈ upperPolar r s ↔ ∀ a ∈ s, r a b` (`mem_upperPolar_iff`),
* `a ∈ lowerPolar r t ↔ ∀ b ∈ t, r a b` (`mem_lowerPolar_iff`).

The first part of this file computes derivations in the animals context by hand. The second part
reproves the basic laws of the derivation operators for an arbitrary context. All of them are in
Mathlib already; the proofs are repeated here because they are short and instructive.
-/

@[expose] public section

namespace FCAExamples

open Animal Trait Set Order

/-! ### Derivations in the animals context -/

/-- Ducks and eagles both have feathers. Unfolding the definition, we are given an animal `a`
in `{duck, eagle}` and must show that it has feathers; there are two cases. -/
example : feathers ∈ upperPolar animals {duck, eagle} := by
  intro a ha
  rcases ha with rfl | rfl
  · rfl
  · rfl

/-- Not all of them swim: the eagle does not. -/
example : swims ∉ upperPolar animals {duck, eagle} := by
  intro h
  have heagle : animals eagle swims := h (by simp)
  exact Bool.false_ne_true heagle

/-- The common traits of duck and eagle are exactly feathers and flying. -/
theorem upperPolar_duck_eagle : upperPolar animals {duck, eagle} = {feathers, flies} := by
  ext m
  constructor
  · intro h
    have hduck : animals duck m := h (by simp)
    have heagle : animals eagle m := h (by simp)
    cases m <;> simp_all [animals, hasTrait]
  · rintro (rfl | rfl) a (rfl | rfl) <;> rfl

/-- The animals with feathers which fly are exactly duck and eagle. -/
theorem lowerPolar_feathers_flies : lowerPolar animals {feathers, flies} = {duck, eagle} := by
  ext g
  constructor
  · intro h
    have hfeathers : animals g feathers := h (by simp)
    cases g <;> simp_all [animals, hasTrait]
  · rintro (rfl | rfl) m (rfl | rfl) <;> rfl

/-- The derivation of the empty set of objects is the set of all attributes. -/
example : upperPolar animals ∅ = univ :=
  upperPolar_empty animals

/-! ### The laws of the derivation operators -/

variable {α β : Type*} {r : α → β → Prop} {s s₁ s₂ : Set α} {t : Set β}

/-- More objects have fewer attributes in common. -/
example (h : s₁ ⊆ s₂) : upperPolar r s₂ ⊆ upperPolar r s₁ :=
  fun _ hb _ ha ↦ hb (h ha)

/-- Every set of objects is contained in its double derivation `s''`. -/
example : s ⊆ lowerPolar r (upperPolar r s) :=
  fun _ ha _ hb ↦ hb ha

/-- The derivation operators form a Galois connection. -/
example : t ⊆ upperPolar r s ↔ s ⊆ lowerPolar r t :=
  ⟨fun h _ ha _ hb ↦ h hb ha, fun h _ hb _ ha ↦ h ha hb⟩

/-- Deriving three times is the same as deriving once: `s''' = s'`. -/
example : upperPolar r (lowerPolar r (upperPolar r s)) = upperPolar r s := by
  apply Subset.antisymm
  · -- `s ⊆ s''`, and derivation reverses inclusions
    exact upperPolar_anti r (subset_lowerPolar_upperPolar r s)
  · -- `t ⊆ t''` for `t = s'`
    exact subset_upperPolar_lowerPolar r (upperPolar r s)

/-- The derivation of a union is the intersection of the derivations. -/
example : upperPolar r (s₁ ∪ s₂) = upperPolar r s₁ ∩ upperPolar r s₂ := by
  ext b
  constructor
  · intro h
    exact ⟨fun a ha ↦ h (.inl ha), fun a ha ↦ h (.inr ha)⟩
  · rintro ⟨h₁, h₂⟩ a (ha | ha)
    · exact h₁ ha
    · exact h₂ ha

/-! ### Extents and intents

A set of objects is an *extent* if it is the derivation of some set of attributes, equivalently
if `s'' = s`. Dually for *intents*. -/

/-- Every derivation of a set of attributes is an extent, by definition. -/
example : IsExtent r (lowerPolar r t) :=
  ⟨t, rfl⟩

/-- `{duck, eagle}` is an extent of the animals context. -/
theorem isExtent_duck_eagle : IsExtent animals {duck, eagle} :=
  ⟨{feathers, flies}, lowerPolar_feathers_flies⟩

/-- `{dog, duck, eagle}` is not an extent: its only common trait is none at all, so its double
derivation is the set of all animals, which contains the cat. -/
example : ¬IsExtent animals {dog, duck, eagle} := by
  intro h
  rw [isExtent_iff] at h
  have hcat : cat ∈ lowerPolar animals (upperPolar animals {dog, duck, eagle}) := by
    intro m hm
    have hdog : animals dog m := hm (by simp)
    have hduck : animals duck m := hm (by simp)
    have heagle : animals eagle m := hm (by simp)
    cases m <;> simp_all [animals, hasTrait]
  rw [h] at hcat
  simp at hcat

/-- The intersection of two extents is an extent. -/
example {t₁ t₂ : Set β} :
    IsExtent r (lowerPolar r t₁ ∩ lowerPolar r t₂) :=
  ⟨t₁ ∪ t₂, lowerPolar_union r t₁ t₂⟩

end FCAExamples
