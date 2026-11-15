/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Finite.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Concept lattices of finite contexts

A context with finitely many objects or finitely many attributes has a finite concept lattice,
with at most `2 ^ min |α| |β|` concepts. For finite contexts with decidable incidence, the
executable enumeration `FCA.intents` counts the concepts.

## Main results

* `Concept.finite_of_finite_left`, `Concept.finite_of_finite_right`: finiteness of the concept
  lattice.
* `Concept.natCard_le_two_pow_left`, `Concept.natCard_le_two_pow_right`: the exponential bound on
  the number of concepts.
* `FCA.natCard_concept`: the number of concepts equals the number of enumerated intents.
-/

@[expose] public section

open Order

namespace Concept

variable {α β : Type*} {r : α → β → Prop}

instance finite_of_finite_left [Finite α] : Finite (Concept α β r) :=
  .of_injective _ extent_injective

instance finite_of_finite_right [Finite β] : Finite (Concept α β r) :=
  .of_injective _ intent_injective

/-- A context with `n` objects has at most `2 ^ n` concepts. -/
theorem natCard_le_two_pow_left [Finite α] : Nat.card (Concept α β r) ≤ 2 ^ Nat.card α := by
  have := Fintype.ofFinite α
  calc Nat.card (Concept α β r) ≤ Nat.card (Set α) :=
        Nat.card_le_card_of_injective _ extent_injective
    _ = 2 ^ Nat.card α := by simp [Nat.card_eq_fintype_card]

/-- A context with `n` attributes has at most `2 ^ n` concepts. -/
theorem natCard_le_two_pow_right [Finite β] : Nat.card (Concept α β r) ≤ 2 ^ Nat.card β := by
  have := Fintype.ofFinite β
  calc Nat.card (Concept α β r) ≤ Nat.card (Set β) :=
        Nat.card_le_card_of_injective _ intent_injective
    _ = 2 ^ Nat.card β := by simp [Nat.card_eq_fintype_card]

end Concept

namespace FCA

variable {α β : Type*} (r : α → β → Prop) [DecidableRel r] [Fintype α] [Fintype β]
  [DecidableEq β]

/-- The concepts of a finite context correspond to the enumerated intents. -/
noncomputable def conceptEquivIntents : Concept α β r ≃ intents r :=
  .symm <| .ofBijective (fun t ↦ Concept.ofIsIntent r _ (mem_intents.1 t.2))
    ⟨fun s t h ↦ Subtype.ext (Finset.coe_injective congr(($h).intent)), fun c ↦
      ⟨⟨c.intent.toFinite.toFinset, mem_intents.2 (by simp)⟩, Concept.ext' (by simp)⟩⟩

/-- The number of concepts of a finite context is the number of its enumerated intents. -/
theorem natCard_concept : Nat.card (Concept α β r) = (intents r).card := by
  rw [Nat.card_congr (conceptEquivIntents r), Nat.card_eq_fintype_card, Fintype.card_coe]

end FCA
