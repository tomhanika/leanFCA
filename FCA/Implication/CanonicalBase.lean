/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.Basic
public import Mathlib.Data.Set.Card

/-!
# Pseudo-intents and the canonical base

For a formal context `r : α → β → Prop` with finitely many attributes, a set `p` of attributes is
a *pseudo-intent* if it is not an intent, but contains the intent closure `q''` of every
pseudo-intent `q ⊂ p`. The implications `p → p''`, for `p` ranging over the pseudo-intents, form
the *canonical base* (also called *stem base* or *Duquenne–Guigues base*) of the context.

## Main definitions

* `FCA.IsPseudoIntent`: the predicate of being a pseudo-intent.
* `FCA.canonicalBase`: the canonical base of a formal context.

## Main results

* `FCA.isSound_canonicalBase`: all implications of the canonical base hold in the context.
* `FCA.isComplete_canonicalBase`: every implication holding in the context is entailed by the
  canonical base.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [J.-L. Guigues, V. Duquenne, *Familles minimales d'implications informatives résultant d'un
  tableau de données binaires*][guigues1986]
-/

@[expose] public section

open Set Order

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {p t : Set β}

/-- A set `p` of attributes is a *pseudo-intent* of the formal context `r` if it is not an intent
and contains the intent closure of every pseudo-intent properly contained in it. -/
def IsPseudoIntent [Finite β] (r : α → β → Prop) (p : Set β) : Prop :=
  ¬IsIntent r p ∧
    ∀ q, (_ : q ⊂ p) → IsPseudoIntent r q → upperPolar r (lowerPolar r q) ⊆ p
termination_by p.ncard
decreasing_by exact ncard_lt_ncard ‹_› (toFinite p)

variable [Finite β]

theorem isPseudoIntent_iff :
    IsPseudoIntent r p ↔ ¬IsIntent r p ∧
      ∀ q, q ⊂ p → IsPseudoIntent r q → upperPolar r (lowerPolar r q) ⊆ p := by
  rw [IsPseudoIntent]

theorem IsPseudoIntent.not_isIntent (hp : IsPseudoIntent r p) : ¬IsIntent r p :=
  (isPseudoIntent_iff.1 hp).1

theorem IsPseudoIntent.closure_subset {q : Set β} (hp : IsPseudoIntent r p) (hqp : q ⊂ p)
    (hq : IsPseudoIntent r q) : upperPolar r (lowerPolar r q) ⊆ p :=
  (isPseudoIntent_iff.1 hp).2 q hqp hq

/-- The *canonical base* of a formal context consists of the implications `p → p''` for all
pseudo-intents `p`. -/
def canonicalBase (r : α → β → Prop) : Set (Implication β) :=
  {i | IsPseudoIntent r i.premise ∧ i.conclusion = upperPolar r (lowerPolar r i.premise)}

theorem mem_canonicalBase {i : Implication β} :
    i ∈ canonicalBase r ↔
      IsPseudoIntent r i.premise ∧ i.conclusion = upperPolar r (lowerPolar r i.premise) :=
  Iff.rfl

theorem IsPseudoIntent.mem_canonicalBase (hp : IsPseudoIntent r p) :
    ⟨p, upperPolar r (lowerPolar r p)⟩ ∈ canonicalBase r :=
  ⟨hp, rfl⟩

/-- The canonical base is sound: all its implications hold in the context. -/
theorem isSound_canonicalBase (r : α → β → Prop) : Implication.IsSound r (canonicalBase r) :=
  fun _ hi => Implication.holds_iff_subset_closure.2 hi.2.subset

/-- A model of the canonical base which is not an intent would be a pseudo-intent. -/
theorem isIntent_of_isModel_canonicalBase (ht : Implication.IsModel (canonicalBase r) t) :
    IsIntent r t := by
  by_contra hnot
  have hp : IsPseudoIntent r t :=
    isPseudoIntent_iff.2 ⟨hnot, fun q hqt hq => ht _ hq.mem_canonicalBase hqt.subset⟩
  have ht' : upperPolar r (lowerPolar r t) ⊆ t := ht _ hp.mem_canonicalBase Subset.rfl
  exact hnot (isIntent_iff.2 (ht'.antisymm (subset_upperPolar_lowerPolar r t)))

/-- The canonical base is complete: it entails every implication holding in the context. -/
theorem isComplete_canonicalBase (r : α → β → Prop) :
    Implication.IsComplete r (canonicalBase r) :=
  Implication.isComplete_iff.2 fun _ => isIntent_of_isModel_canonicalBase

/-- The models of the canonical base are exactly the intents of the context. -/
theorem isModel_canonicalBase_iff : Implication.IsModel (canonicalBase r) t ↔ IsIntent r t :=
  Implication.isModel_iff_isIntent (isSound_canonicalBase r) (isComplete_canonicalBase r)

/-- An implication holds in a context iff it is entailed by the canonical base. -/
theorem entails_canonicalBase_iff {i : Implication β} :
    Implication.Entails (canonicalBase r) i ↔ Implication.Holds r i :=
  Implication.entails_iff_holds (isSound_canonicalBase r) (isComplete_canonicalBase r)

end FCA
