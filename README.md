# FCA — Formal Concept Analysis in Lean 4

A Lean 4 library for [formal concept analysis](https://en.wikipedia.org/wiki/Formal_concept_analysis)
(FCA), building on [Mathlib](https://github.com/leanprover-community/mathlib4). It covers both
the theory (machine-checked proofs) and computation (executable, verified algorithms).

> **Beta.** This library is under active development. Names, statements and the module
> structure may change without notice, and parts of it have not been independently reviewed.
> Use it at your own risk; it is provided without warranty of any kind (see [LICENSE](LICENSE)).

Lean `v4.35.0`, Mathlib `v4.35.0`. All files are Lean modules; there is no `sorry` and no axiom
beyond Lean's standard three.

## Relation to Mathlib

Mathlib's [`Mathlib.Order.Concept`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Concept.html)
provides the order-theoretic core: the derivation operators `upperPolar` / `lowerPolar`, the
predicates `Order.IsExtent` / `Order.IsIntent`, the type `Concept α β r` with its complete lattice
structure, object and attribute concepts, and duality.

This library does not duplicate any of that. Following Mathlib, a *formal context* is simply a
relation `r : α → β → Prop` between a type `α` of objects and a type `β` of attributes.

## Contents

| Module | Content |
| --- | --- |
| **Concept lattices** | |
| `FCA.Concept.Dense` | Object concepts are supremum-dense, attribute concepts infimum-dense |
| `FCA.Concept.BasicTheorem` | The basic theorem on concept lattices |
| `FCA.Concept.Dimension` | The order dimension of a concept lattice equals the Ferrers dimension of its context; order dimension of powersets |
| `FCA.Concept.Distributive` | Distributivity, semidistributivity and semimodularity of concept lattices in terms of the arrow relations |
| `FCA.Order.Semidistributive` | Semidistributive, pseudocomplemented and meet-distributive lattices |
| `FCA.Order.Dimension` | Realizers and the order dimension of a partial order |
| `FCA.ClosureSystem` | Extents and intents as closure systems; every closure operator is the intent closure of a context |
| **Closure systems** | |
| `FCA.Order.ClosureSubsystem` | The complete lattice of closure systems contained in a closure system; meet, join, closure, generated closure systems |
| `FCA.Order.ClosureSubsystem.Structure` | Its structure: atoms, covers, grading, coatoms, meet-irreducibles, distributivity, join-semidistributivity, join-pseudocomplements and their explicit description, meet-distributivity |
| `FCA.Order.ClosureSubsystem.Ordinal` | Covers of a closure system by chains of closed sets |
| `FCA.Order.ClosureSubsystem.Reconstruction` | When two closure systems have isomorphic lattices of closure subsystems; coatomistic closure systems are determined by that lattice |
| `FCA.Order.ClosureSubsystem.Truncation` | Truncated powersets; the ordinal scaling dimension is not monotone in the lattice of closure systems |
| `FCA.Order.ClosureSubsystem.Counterexample` | Join-semidistributivity and join-pseudocomplements fail without the ascending chain condition on closed sets |
| `FCA.Order.ClosureSubsystem.Ladder` | The lattice of closure subsystems is join-semidistributive iff the closure system has no ladder; it never is for all closure systems on an infinite set |
| `FCA.Order.ClosureSubsystem.Nominal` | Nominal closure systems and nominal covers; characterisation by partitions into closed sets; for the closure system of a graph these are the proper edge colourings |
| **Structure of contexts** | |
| `FCA.Context.Constructions` | Complement, apposition, subposition, subcontexts, disjoint union, direct sum |
| `FCA.Context.Clarified` | Clarified contexts; clarification preserves the concept lattice |
| `FCA.Context.Reduced` | Reducible and irreducible objects and attributes; reduction preserves the concept lattice |
| `FCA.Context.Arrows` | Arrow relations `↙`, `↗`, `⤢` and irreducibility |
| `FCA.Context.Ferrers` | Ferrers relations and the Ferrers dimension; the contranominal scale |
| **Implications** | |
| `FCA.Implication.Basic` | Implications, models, validity, entailment, sound and complete implication sets |
| `FCA.Implication.Armstrong` | Armstrong rules: soundness and completeness |
| `FCA.Implication.CanonicalBase` | Pseudo-intents and the canonical (Duquenne–Guigues) base |
| `FCA.Implication.Minimal` | The canonical base is non-redundant and of minimum cardinality |
| `FCA.Implication.PseudoClosed` | Pseudo-closed sets and the canonical base of a closure operator |
| **Association rules** | |
| `FCA.Association.Basic` | Support, confidence, frequent sets, iceberg lattices, Luxenburger base |
| **Scaling** | |
| `FCA.Scale.Standard` | Nominal, ordinal, interordinal, contranominal and dichotomic scales |
| `FCA.ManyValued.Basic` | Many-valued contexts, plain scaling, functional dependencies |
| **Scale-measures** | |
| `FCA.ScaleMeasure.Basic` | Scale-measures as continuous maps, refinement and equivalence, apposition, attribute projection |
| `FCA.ScaleMeasure.Hierarchy` | The scale-hierarchy is isomorphic to the complete lattice of closure systems of extents; canonical representation; meet and join |
| `FCA.ScaleMeasure.Logical` | Logical attributes and the conjunctive normal form of scale-measures |
| `FCA.ScaleMeasure.Dimension` | Ferrers and order dimension bounds for scale-measures |
| `FCA.ScaleMeasure.Structure` | Meet-irreducible elements of the scale-hierarchy and the covering pairs of the concept lattice; the general structure theory is in `FCA.Order.ClosureSubsystem.Structure` |
| `FCA.ScaleMeasure.Fragment` | Which scale-measures are representable in a fragment of propositional logic, e.g. by disjunctions only |
| `FCA.ScaleMeasure.ScalingDimension` | Scaling dimension inside the scale-hierarchy; the ordinal scaling dimension bounds the order dimension |
| `FCA.ScaleMeasure.Reconstruction` | The scale-hierarchy does not determine the concept lattice in general, but does determine coatomistic concept lattices |
| **Morphisms** | |
| `FCA.Morphism.Bond` | Bonds, their composition, and the correspondence with supremum-preserving maps |
| `FCA.Morphism.Infomorphism` | Infomorphisms and context isomorphisms |
| **Finite contexts and algorithms** | |
| `FCA.Finite.Basic` | Executable derivation operators on `Finset`s |
| `FCA.Finite.Concept` | Finiteness of concept lattices and the bound `2 ^ min |α| |β|` |
| `FCA.Algorithm.Lectic` | The lectic order |
| `FCA.Algorithm.NextClosure` | Verified NextClosure; enumeration of all intents and concepts |
| `FCA.Algorithm.ImplicationClosure` | Executable closure under a list of implications |
| `FCA.Algorithm.CanonicalBase` | Verified computation of the canonical base |

API documentation: <https://tomhanika.github.io/leanFCA/docs/>.

## Learning examples

`FCAExamples` is a short tutorial with easy, commented proofs on a small context of four animals
and five traits. Read the files in this order:

| File | Content |
| --- | --- |
| `FCAExamples.Animals` | Defining a formal context from a cross table |
| `FCAExamples.Derivation` | The derivation operators, their basic laws, extents and intents |
| `FCAExamples.Concepts` | Building concepts, the order of the concept lattice, object and attribute concepts |
| `FCAExamples.Implications` | Implications that hold in a context, and entailment |
| `FCAExamples.Computing` | Evaluating derivations, counting concepts, NextClosure and the canonical base |

Further examples, used as tests, live in `FCATest`.

## Using the library

Add the following to the `lakefile.toml` of your project, then run `lake update FCA`:

```toml
[[require]]
name = "FCA"
git = "https://github.com/tomhanika/leanFCA"
rev = "v0.1.0"
```

## Example

```lean
import FCA
import Mathlib.Data.Finset.Sort  -- `Repr` for finsets

open FCA

/-- Divisibility on `Fin 4` as a formal context. -/
abbrev divides (a b : Fin 4) : Prop := a.val ∣ b.val

#eval intentsList divides        -- all intents, in lectic order
#eval canonicalBaseList divides  -- the canonical base
```

## Not yet covered

* Attribute exploration
* Concept lattices of disjoint unions (horizontal sums) and of direct products
* Compatible subcontexts and complete congruences; tolerance relations
* A characterisation of modular concept lattices; distributive concept lattices as contraordinal scales
* Proper premises; an infinitary Armstrong calculus

## Building

Install Lean via [elan](https://github.com/leanprover/elan), then run

```sh
lake exe cache get
lake build
lake test
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for conventions and [docs/references.bib](docs/references.bib)
for the literature cited in docstrings.

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
