# Contributing

## Conventions

* **Contexts are relations.** Following Mathlib, a formal context is a relation
  `r : α → β → Prop` (objects `α`, attributes `β`). There is no context structure. Use Mathlib's
  `upperPolar r`, `lowerPolar r`, `Order.IsExtent r`, `Order.IsIntent r`, `Concept α β r`,
  `intentClosure r`, `extentClosure r`, `Concept.ofObject`, `Concept.ofAttribute` from
  `Mathlib.Order.Concept`; never redefine them.
* **Namespaces.** Lemmas about Mathlib declarations live in their namespace (e.g. `Concept`);
  new notions live in `FCA`.
* **Module system.** Every file is a Lean module:

  ```lean
  /-
  Copyright (c) 2026 Tom Hanika. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Tom Hanika
  -/
  module

  public import Mathlib.Order.Concept

  /-!
  # Title

  Summary, `## Main definitions`, `## Main results`, `## References`.
  -/

  @[expose] public section

  namespace FCA
  ...
  end FCA
  ```

* **Style.** Mathlib style and naming conventions: lines of at most 100 characters, docstrings on
  every definition, `theorem` names in `snake_case` describing the statement, `fun x => _` or
  `fun x ↦ _` consistently within a file, no `sorry`, no new axioms, no build warnings.
* **Computable definitions** on `Finset`s come with a lemma relating them to their `Set`-level
  specification.

## Known pitfalls

* `deriving Fintype` does not work inside module files; write the instance by hand.
* Instance-implicit section variables are not available inside `decreasing_by`; bind them in the
  signature of the definition.

## Building

```sh
lake exe cache get
lake build
lake test
```
