/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA

/-!
# A first formal context

A *formal context* consists of objects, attributes and an incidence relation saying which object
has which attribute. In this library a context is nothing but a relation `r : α → β → Prop`,
where `α` is the type of objects and `β` the type of attributes.

This file defines the small context used throughout the examples:

|       | fur | feathers | flies | swims | predator |
|-------|:---:|:--------:|:-----:|:-----:|:--------:|
| dog   |  ×  |          |       |   ×   |          |
| cat   |  ×  |          |       |       |    ×     |
| duck  |     |    ×     |   ×   |   ×   |          |
| eagle |     |    ×     |   ×   |       |    ×     |
-/

@[expose] public section

namespace FCAExamples

/-- The objects of the example context. -/
inductive Animal
  | dog | cat | duck | eagle
  deriving DecidableEq, Repr

/-- The attributes of the example context. -/
inductive Trait
  | fur | feathers | flies | swims | predator
  deriving DecidableEq, Repr

open Animal Trait

/-- `Animal` is finite. This is needed only for computing, see `FCAExamples.Computing`. -/
instance : Fintype Animal :=
  ⟨{dog, cat, duck, eagle}, fun g ↦ by cases g <;> decide⟩

/-- `Trait` is finite. -/
instance : Fintype Trait :=
  ⟨{fur, feathers, flies, swims, predator}, fun m ↦ by cases m <;> decide⟩

/-- The cross table of the example context. -/
def hasTrait : Animal → Trait → Bool
  | dog, fur | dog, swims => true
  | cat, fur | cat, predator => true
  | duck, feathers | duck, flies | duck, swims => true
  | eagle, feathers | eagle, flies | eagle, predator => true
  | _, _ => false

/-- The example context: `animals g m` says that the animal `g` has the trait `m`. -/
abbrev animals (g : Animal) (m : Trait) : Prop := hasTrait g m = true

/-- A cross in the table is proved by `rfl`: both sides compute to `true`. -/
example : animals duck swims := rfl

/-- A missing cross: `hasTrait dog flies` computes to `false`, and `false ≠ true`. -/
example : ¬animals dog flies := Bool.false_ne_true

/-- Both can also be left to `decide`, which evaluates the table. -/
example : animals eagle predator ∧ ¬animals cat feathers := by decide

end FCAExamples
