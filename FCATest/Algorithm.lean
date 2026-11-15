/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Algorithm.CanonicalBase

/-!
# Tests for the algorithms

A context with four objects and four attributes, both indexed by `Fin 4`, used to exercise the
lectic order, NextClosure, the implication closure and the computation of the canonical base.

The enumerations `FCA.intentsList` and `FCA.canonicalBaseList` are defined by well-founded
recursion, which `decide` does not unfold; they are evaluated by the kernel with `decide +kernel`
(this does not use `native_decide` and adds no axioms).
-/

@[expose] public section

namespace FCATest.Algorithm

open FCA

/-- The incidence relation of the test context, as a Boolean table. -/
def table : Fin 4 → Fin 4 → Bool
  | 0, 0 | 0, 1 => true
  | 1, 0 | 1, 2 => true
  | 2, 0 | 2, 1 | 2, 3 => true
  | 3, 2 | 3, 3 => true
  | _, _ => false

/-- The incidence relation of the test context. -/
abbrev incidence (g m : Fin 4) : Prop := table g m = true

/-! ### The lectic order -/

example : ({0, 3} : Finset (Fin 4)) <ₗ[1] {0, 1} := by decide

example : ({1, 2, 3} : Finset (Fin 4)) <ₗ {0} := by decide

example : ¬({0} : Finset (Fin 4)) <ₗ {1, 2, 3} := by decide

example : oplus (intentClosureOperatorFinset incidence) {0, 2} 1 = {0, 1} := by decide

/-! ### NextClosure -/

example : nextClosure (intentClosureOperatorFinset incidence) {0, 2} = some {0, 1} := by decide

example : nextClosure (intentClosureOperatorFinset incidence) {0, 1} = some {0, 1, 3} := by
  decide

example : nextClosure (intentClosureOperatorFinset incidence) Finset.univ = none := by decide

example : intentsList incidence =
    [∅, {3}, {2}, {2, 3}, {0}, {0, 2}, {0, 1}, {0, 1, 3}, {0, 1, 2, 3}] := by
  decide +kernel

example : (conceptsList incidence).length = 9 := by decide +kernel

example : (FCA.intents incidence).card = 9 := by
  rw [← length_intentsList]
  decide +kernel

/-! ### Closure under implications -/

example : Implication.closureFinset [(({1} : Finset (Fin 4)), {2}), ({0, 2}, {3})] {1} =
    {1, 2} := by
  decide

example : Implication.closureFinset [(({0, 2} : Finset (Fin 4)), {3}), ({1}, {2}), (∅, {0})] {1} =
    {0, 1, 2, 3} := by
  decide

example : pseudoClosureOperator [(({1} : Finset (Fin 4)), {0, 1})] {1} = {1} := by decide

example : pseudoClosureOperator [(({1} : Finset (Fin 4)), {0, 1})] {1, 2} = {0, 1, 2} := by
  decide

/-! ### The canonical base -/

example : canonicalBaseList incidence =
    [({1}, {0, 1}), ({0, 3}, {0, 1, 3}), ({0, 1, 2}, {0, 1, 2, 3})] := by
  decide +kernel

example : pseudoIntentsList incidence = [{1}, {0, 3}, {0, 1, 2}] := by decide +kernel

example : IsPseudoIntent incidence (({0, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
  decide +kernel

example : ¬IsPseudoIntent incidence (({1, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
  decide +kernel

example : Implication.closureFinset (canonicalBaseList incidence) {0, 3} = {0, 1, 3} := by
  rw [closureFinset_canonicalBaseList]
  decide

end FCATest.Algorithm
