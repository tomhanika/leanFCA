# FCA — Formal Concept Analysis in Lean 4

A Lean 4 library for [formal concept analysis](https://en.wikipedia.org/wiki/Formal_concept_analysis)
(FCA), building on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Relation to Mathlib

Mathlib's [`Mathlib.Order.Concept`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Concept.html)
already provides the order-theoretic core: the derivation operators `upperPolar` / `lowerPolar`,
the predicates `Order.IsExtent` / `Order.IsIntent`, the type `Concept α β r` with its complete
lattice structure, object and attribute concepts, and duality.

This library does not duplicate any of that. Following Mathlib, a *formal context* is simply a
relation `r : α → β → Prop` between a type `α` of objects and a type `β` of attributes. On top of
it, this library adds the parts of FCA that Mathlib does not cover.

## Contents

| Module | Content |
| --- | --- |
| `FCA.Concept.Dense` | Object concepts are supremum-dense, attribute concepts are infimum-dense |
| `FCA.Implication.Basic` | Attribute implications, models, validity in a context, the closure operator of an implication set, entailment, sound and complete implication sets |
| `FCA.Implication.CanonicalBase` | Pseudo-intents and the canonical (Duquenne–Guigues) base; soundness and completeness |
| `FCA.Finite.Basic` | Executable derivation operators on `Finset`s, enumeration of intents and concepts, with correctness lemmas |
| `FCATest.Example` | A small worked example evaluated by `decide` |

## Roadmap

* The basic theorem on concept lattices in full (characterisation of the complete lattices
  isomorphic to a given concept lattice via dense maps)
* Clarified and reduced contexts, irreducible objects and attributes, arrow relations
* Minimality of the canonical base; Armstrong rules for finite attribute sets
* Verified NextClosure (lectic order) for intents and for the canonical base
* Context constructions (apposition, subposition, direct sum and product) and their lattices
* Attribute exploration

## Building

Install Lean via [elan](https://github.com/leanprover/elan), then run

```sh
lake exe cache get
lake build
lake test
```

## References

* B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999.
* J.-L. Guigues, V. Duquenne, *Familles minimales d'implications informatives résultant d'un
  tableau de données binaires*, Mathématiques et Sciences Humaines 95 (1986), 5–18.

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
