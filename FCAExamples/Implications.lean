/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCAExamples.Animals

/-!
# Implications

An *implication* `A → B` between sets of attributes *holds* in a context if every object having
all attributes of `A` also has all attributes of `B`. In this library `FCA.Implication β` is a
pair of a `premise` and a `conclusion`, and `FCA.Implication.Holds r i` says that `i` holds in
the context `r`: the set of attributes of every object *respects* `i`.
-/

@[expose] public section

namespace FCAExamples

open Animal Trait Set Order FCA FCA.Implication

/-! ### Implications of the animals context -/

/-- Every animal with feathers flies. Given an animal `a` all of whose traits include feathers,
we check the four animals: two of them have no feathers, the other two fly. -/
example : Holds animals ⟨{feathers}, {flies}⟩ := by
  intro a h
  have hfeathers : animals a feathers := h (mem_singleton _) (mem_singleton _)
  rw [singleton_subset_iff, mem_upperPolar_singleton]
  cases a
  · exact absurd hfeathers Bool.false_ne_true
  · exact absurd hfeathers Bool.false_ne_true
  · rfl
  · rfl

/-- Not every flying animal is a predator: the duck is a counterexample. -/
example : ¬Holds animals ⟨{flies}, {predator}⟩ := by
  intro h
  have hduck : {predator} ⊆ upperPolar animals {duck} := h duck (by rintro _ rfl _ rfl; rfl)
  exact Bool.false_ne_true (hduck (mem_singleton _) (mem_singleton _))

/-- No animal has both fur and feathers, so `{fur, feathers}` implies everything. -/
example (B : Set Trait) : Holds animals ⟨{fur, feathers}, B⟩ := by
  intro a h
  have hfur : animals a fur := h (by simp) (mem_singleton _)
  have hfeathers : animals a feathers := h (by simp) (mem_singleton _)
  cases a <;> simp_all [animals, hasTrait]

/-! ### Implications of an arbitrary context -/

variable {α β : Type*} {r : α → β → Prop} {A B C : Set β}

/-- `A → A` always holds. -/
example : Holds r ⟨A, A⟩ :=
  fun _ h ↦ h

/-- Implications can be chained. -/
example (h₁ : Holds r ⟨A, B⟩) (h₂ : Holds r ⟨B, C⟩) : Holds r ⟨A, C⟩ :=
  fun a hA ↦ h₂ a (h₁ a hA)

/-- The premise of an implication can be enlarged. -/
example (h : Holds r ⟨A, B⟩) (hAC : A ⊆ C) : Holds r ⟨C, B⟩ :=
  fun a hC ↦ h a (hAC.trans hC)

/-- `A → B` holds iff `B` is contained in the double derivation `A''`. -/
example : Holds r ⟨A, B⟩ ↔ B ⊆ upperPolar r (lowerPolar r A) :=
  holds_iff_subset_closure

/-- In particular `A → A''` holds: `A''` is the largest conclusion of `A`. -/
example : Holds r ⟨A, upperPolar r (lowerPolar r A)⟩ :=
  holds_closure r A

/-! ### Entailment

A set `L` of implications *entails* `i` if every set of attributes respecting all of `L` respects
`i`. -/

/-- A set of implications entails each of its members. -/
example {L : Set (Implication β)} {i : Implication β} (hi : i ∈ L) : Entails L i :=
  entails_of_mem hi

/-- `{A → B, B → C}` entails `A → C`. -/
example : Entails {⟨A, B⟩, ⟨B, C⟩} (⟨A, C⟩ : Implication β) := by
  intro t ht hA
  have hB : B ⊆ t := ht ⟨A, B⟩ (by simp) hA
  exact ht ⟨B, C⟩ (by simp) hB

end FCAExamples
