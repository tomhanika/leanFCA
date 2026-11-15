/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.CanonicalBase

/-!
# Pseudo-closed sets and the canonical base of a closure operator

The notion of a pseudo-intent only depends on the intent closure operator of a formal context.
This file develops it for an arbitrary closure operator `c` on the subsets of a finite type: a set
`p` is *pseudo-closed* if it is not closed, but contains the closure `c q` of every pseudo-closed
set `q ⊂ p`. The implications `p → c p`, for `p` pseudo-closed, form the *canonical base* of `c`;
its models are exactly the closed sets of `c`. In particular every set of implications `L` over a
finite attribute type is equivalent to the canonical base of its closure operator
`FCA.Implication.closure L`.

## Main definitions

* `FCA.IsPseudoClosed`: the predicate of being a pseudo-closed set of a closure operator.
* `FCA.pseudoClosedBase`: the canonical base of a closure operator.

## Main results

* `FCA.isModel_pseudoClosedBase_iff`: the models of the canonical base of `c` are the closed sets
  of `c`.
* `FCA.closure_pseudoClosedBase`: the closure operator of the canonical base of `c` is `c`.
* `FCA.entails_pseudoClosedBase_closure_iff`: a set of implications and the canonical base of its
  closure operator entail the same implications.
* `FCA.isPseudoClosed_intentClosure_iff`, `FCA.pseudoClosedBase_intentClosure`: pseudo-intents and
  the canonical base of a formal context are the special case of the intent closure operator.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Order

namespace FCA

variable {α β : Type*} {c : ClosureOperator (Set β)} {p t : Set β} {i : Implication β}

/-- A set `p` is *pseudo-closed* with respect to the closure operator `c` if it is not closed and
contains the closure of every pseudo-closed set properly contained in it. -/
def IsPseudoClosed [Finite β] (c : ClosureOperator (Set β)) (p : Set β) : Prop :=
  ¬c.IsClosed p ∧ ∀ q, (_ : q ⊂ p) → IsPseudoClosed c q → c q ⊆ p
termination_by p.ncard
decreasing_by exact ncard_lt_ncard ‹_› (toFinite p)

variable [Finite β]

theorem isPseudoClosed_iff :
    IsPseudoClosed c p ↔ ¬c.IsClosed p ∧ ∀ q, q ⊂ p → IsPseudoClosed c q → c q ⊆ p := by
  rw [IsPseudoClosed]

theorem IsPseudoClosed.not_isClosed (hp : IsPseudoClosed c p) : ¬c.IsClosed p :=
  (isPseudoClosed_iff.1 hp).1

theorem IsPseudoClosed.closure_subset {q : Set β} (hp : IsPseudoClosed c p) (hqp : q ⊂ p)
    (hq : IsPseudoClosed c q) : c q ⊆ p :=
  (isPseudoClosed_iff.1 hp).2 q hqp hq

/-- The *canonical base* of a closure operator `c` consists of the implications `p → c p` for all
pseudo-closed sets `p`. -/
def pseudoClosedBase (c : ClosureOperator (Set β)) : Set (Implication β) :=
  {i | IsPseudoClosed c i.premise ∧ i.conclusion = c i.premise}

theorem mem_pseudoClosedBase :
    i ∈ pseudoClosedBase c ↔ IsPseudoClosed c i.premise ∧ i.conclusion = c i.premise :=
  Iff.rfl

theorem IsPseudoClosed.mem_pseudoClosedBase (hp : IsPseudoClosed c p) :
    ⟨p, c p⟩ ∈ pseudoClosedBase c :=
  ⟨hp, rfl⟩

/-- Every closed set of `c` is a model of the canonical base of `c`. -/
theorem isModel_pseudoClosedBase_of_isClosed (ht : c.IsClosed t) :
    Implication.IsModel (pseudoClosedBase c) t := by
  rintro i ⟨-, hi⟩ hsub
  rw [hi]
  exact ClosureOperator.closure_min hsub ht

/-- A model of the canonical base which is not closed would be pseudo-closed. -/
theorem isClosed_of_isModel_pseudoClosedBase (ht : Implication.IsModel (pseudoClosedBase c) t) :
    c.IsClosed t := by
  by_contra hnot
  have hp : IsPseudoClosed c t :=
    isPseudoClosed_iff.2 ⟨hnot, fun q hqt hq => ht _ hq.mem_pseudoClosedBase hqt.subset⟩
  have ht' : c t ⊆ t := ht _ hp.mem_pseudoClosedBase Subset.rfl
  exact hnot (c.isClosed_iff_closure_le.2 ht')

/-- The models of the canonical base of a closure operator are exactly its closed sets. -/
theorem isModel_pseudoClosedBase_iff :
    Implication.IsModel (pseudoClosedBase c) t ↔ c.IsClosed t :=
  ⟨isClosed_of_isModel_pseudoClosedBase, isModel_pseudoClosedBase_of_isClosed⟩

/-- The closure operator of the canonical base of `c` is `c` itself. -/
theorem closure_pseudoClosedBase (c : ClosureOperator (Set β)) :
    Implication.closure (pseudoClosedBase c) = c :=
  ClosureOperator.ext_isClosed _ _ fun _ => isModel_pseudoClosedBase_iff

/-- The canonical base of `c` entails `s → t` iff `t ⊆ c s`. -/
theorem entails_pseudoClosedBase_iff :
    Implication.Entails (pseudoClosedBase c) i ↔ i.conclusion ⊆ c i.premise := by
  rw [Implication.entails_iff, closure_pseudoClosedBase]

/-- Every set of implications over a finite attribute type has the same models as the canonical
base of its closure operator. -/
theorem isModel_pseudoClosedBase_closure_iff {L : Set (Implication β)} :
    Implication.IsModel (pseudoClosedBase (Implication.closure L)) t ↔ Implication.IsModel L t :=
  isModel_pseudoClosedBase_iff.trans Implication.isClosed_closure_iff

/-- Every set of implications over a finite attribute type entails the same implications as the
canonical base of its closure operator. -/
theorem entails_pseudoClosedBase_closure_iff {L : Set (Implication β)} :
    Implication.Entails (pseudoClosedBase (Implication.closure L)) i ↔ Implication.Entails L i :=
  entails_pseudoClosedBase_iff.trans Implication.entails_iff.symm

/-- The canonical base of a closure operator is non-redundant: none of its implications is
entailed by the others. -/
theorem not_entails_pseudoClosedBase_diff_singleton (hi : i ∈ pseudoClosedBase c) :
    ¬Implication.Entails (pseudoClosedBase c \ {i}) i := by
  intro h
  have hmodel : Implication.IsModel (pseudoClosedBase c \ {i}) i.premise := by
    rintro j ⟨⟨hj, hc⟩, hne⟩ hsub
    rw [hc]
    refine hi.1.closure_subset (hsub.ssubset_of_ne fun heq => hne ?_) hj
    exact mem_singleton_iff.2 (Implication.ext heq (hc.trans ((congrArg c heq).trans hi.2.symm)))
  have hsub : c i.premise ⊆ i.premise := hi.2 ▸ h _ hmodel Subset.rfl
  exact hi.1.not_isClosed (c.isClosed_iff_closure_le.2 hsub)

/-! ### Pseudo-intents as pseudo-closed sets -/

/-- The pseudo-intents of a formal context are the pseudo-closed sets of its intent closure
operator. -/
theorem isPseudoClosed_intentClosure_iff {r : α → β → Prop} :
    IsPseudoClosed (intentClosure r) p ↔ IsPseudoIntent r p := by
  induction p using WellFoundedLT.induction with
  | ind p ih =>
    rw [isPseudoClosed_iff, isPseudoIntent_iff]
    refine and_congr (not_congr ((intentClosure r).isClosed_iff.trans isIntent_iff.symm))
      ⟨fun h q hq hq' => h q hq ((ih q hq).2 hq'), fun h q hq hq' => h q hq ((ih q hq).1 hq')⟩

/-- The canonical base of a formal context is the canonical base of its intent closure
operator. -/
theorem pseudoClosedBase_intentClosure (r : α → β → Prop) :
    pseudoClosedBase (intentClosure r) = canonicalBase r :=
  Set.ext fun _ => and_congr isPseudoClosed_intentClosure_iff Iff.rfl

end FCA
