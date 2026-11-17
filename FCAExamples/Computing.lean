/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCAExamples.Derivation

/-!
# Computing with finite contexts

For a finite context with a decidable incidence relation, the derivation operators are available
on `Finset`s and can be evaluated: `FCA.upperPolarFinset`, `FCA.lowerPolarFinset`,
`FCA.intentClosureFinset`, `FCA.intents`, `FCA.concepts`. Statements about them are proved by
`decide`. In an editor one can also inspect the values, for instance

```lean
#eval FCA.upperPolarFinset animals {duck, eagle}  -- {Trait.feathers, Trait.flies}
```

The algorithms `FCA.intentsList` and `FCA.canonicalBaseList` need a linear order on the
attributes; the last section uses a context on `Fin 4` for them.
-/

@[expose] public section

namespace FCAExamples

open Animal Trait Set Order FCA

/-! ### Derivations -/

example : upperPolarFinset animals {duck, eagle} = {feathers, flies} := by decide

example : lowerPolarFinset animals {swims} = {dog, duck} := by decide

/-- The closure `{flies}''` of `{flies}`: every flying animal has feathers. -/
example : intentClosureFinset animals {flies} = {feathers, flies} := by decide

/-- The animals context has ten concepts. -/
example : (concepts animals).card = 10 := by decide

/-- The pair `({duck, eagle}, {feathers, flies})` is one of them. -/
example : (({duck, eagle} : Finset Animal), ({feathers, flies} : Finset Trait)) ∈
    concepts animals := by
  decide

/-! ### From computation to sets

The computable operators agree with Mathlib's operators on sets (`FCA.coe_upperPolarFinset`), so
a computation proves a statement about sets. Compare with the proof by hand in
`FCAExamples.upperPolar_duck_eagle`. -/

example : upperPolar animals {duck, eagle} = {feathers, flies} := by
  have h : upperPolarFinset animals {duck, eagle} = {feathers, flies} := by decide
  simpa [h] using (coe_upperPolarFinset animals {duck, eagle}).symm

/-! ### Enumerating intents and the canonical base -/

/-- Divisibility on `{0, 1, 2, 3}` as a formal context. -/
abbrev divides (a b : Fin 4) : Prop := a.val ∣ b.val

/-- All intents in lectic order, computed by NextClosure. The enumeration is defined by
well-founded recursion, so it is evaluated with `decide +kernel`. -/
example : intentsList divides = [{0}, {0, 3}, {0, 2}, {0, 1, 2, 3}] := by
  decide +kernel

/-- The canonical base: a smallest set of implications from which all implications of the
context follow. -/
example : canonicalBaseList divides =
    [(∅, {0}), ({0, 2, 3}, {0, 1, 2, 3}), ({0, 1}, {0, 1, 2, 3})] := by
  decide +kernel

end FCAExamples
