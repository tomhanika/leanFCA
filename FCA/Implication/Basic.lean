/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Order.Concept

/-!
# Attribute implications

An *implication* over an attribute set `β` is a pair of sets `A B : Set β`, read as "every object
having all attributes in `A` also has all attributes in `B`". This file develops the semantics of
implications, both with respect to sets of attributes (models) and with respect to a formal
context, i.e. a relation `r : α → β → Prop`.

## Main definitions

* `FCA.Implication`: an implication `premise → conclusion` between sets of attributes.
* `FCA.Implication.Respects`: a set of attributes respects an implication.
* `FCA.Implication.IsModel`: a set of attributes respects every implication of a given set.
* `FCA.Implication.Holds`: an implication holds in a formal context.
* `FCA.Implication.closure`: the closure operator whose closed sets are the models of a set of
  implications.
* `FCA.Implication.Entails`: semantic entailment between a set of implications and an implication.
* `FCA.Implication.IsSound`, `FCA.Implication.IsComplete`: soundness and completeness of a set of
  implications with respect to a formal context.

## Main results

* `FCA.Implication.holds_iff_subset_closure`: `A → B` holds in a context iff `B ⊆ A''`.
* `FCA.Implication.entails_iff`: `L` entails `A → B` iff `B` is contained in the `L`-closure
  of `A`.
* `FCA.Implication.isComplete_iff`: `L` is complete iff every model of `L` is an intent.
* `FCA.Implication.closure_eq_intentClosure`: the closure operator of a sound and complete set of
  implications is the intent closure of the context.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Order

namespace FCA

/-- An implication `premise → conclusion` between sets of attributes. -/
@[ext]
structure Implication (β : Type*) where
  /-- The premise of an implication. -/
  premise : Set β
  /-- The conclusion of an implication. -/
  conclusion : Set β

namespace Implication

variable {α β : Type*} {r : α → β → Prop} {i : Implication β} {t : Set β}
  {L : Set (Implication β)}

/-! ### Models -/

/-- A set of attributes `t` *respects* the implication `i` if it contains the conclusion of `i`
whenever it contains the premise of `i`. -/
def Respects (t : Set β) (i : Implication β) : Prop :=
  i.premise ⊆ t → i.conclusion ⊆ t

/-- A set of attributes is a *model* of a set of implications if it respects all of them. -/
def IsModel (L : Set (Implication β)) (t : Set β) : Prop :=
  ∀ i ∈ L, Respects t i

theorem respects_univ (i : Implication β) : Respects univ i :=
  fun _ => subset_univ _

theorem isModel_univ (L : Set (Implication β)) : IsModel L univ :=
  fun i _ => respects_univ i

theorem IsModel.mono {L' : Set (Implication β)} (h : IsModel L t) (hL : L' ⊆ L) : IsModel L' t :=
  fun i hi => h i (hL hi)

/-- The models of a set of implications are closed under arbitrary intersections. -/
theorem IsModel.sInf {S : Set (Set β)} (hS : ∀ t ∈ S, IsModel L t) : IsModel L (sInf S) :=
  fun i hi hp => le_sInf fun t ht => hS t ht i hi (le_trans hp (sInf_le ht))

/-! ### Implications of a formal context -/

/-- An implication *holds* in the formal context `r` if the intent of every object respects it. -/
def Holds (r : α → β → Prop) (i : Implication β) : Prop :=
  ∀ a, Respects (upperPolar r {a}) i

theorem holds_iff_lowerPolar_subset :
    Holds r i ↔ lowerPolar r i.premise ⊆ lowerPolar r i.conclusion := by
  constructor
  · intro h a ha
    exact singleton_subset_iff.1 (subset_upperPolar_iff_subset_lowerPolar.1
      (h a (subset_upperPolar_iff_subset_lowerPolar.2 (singleton_subset_iff.2 ha))))
  · intro h a ha
    exact subset_upperPolar_iff_subset_lowerPolar.2 (singleton_subset_iff.2
      (h (singleton_subset_iff.1 (subset_upperPolar_iff_subset_lowerPolar.1 ha))))

/-- An implication `A → B` holds in a formal context iff `B` is contained in the intent closure
`A''` of `A`. -/
theorem holds_iff_subset_closure :
    Holds r i ↔ i.conclusion ⊆ upperPolar r (lowerPolar r i.premise) :=
  holds_iff_lowerPolar_subset.trans subset_upperPolar_iff_subset_lowerPolar.symm

/-- An implication holds in a formal context iff every intent respects it. -/
theorem holds_iff_forall_isIntent : Holds r i ↔ ∀ t, IsIntent r t → Respects t i :=
  ⟨fun h _ ht hp => (holds_iff_subset_closure.1 h).trans (ht.upperPolar_lowerPolar_subset hp),
    fun h _ => h _ isIntent_upperPolar⟩

/-- The implication `A → A''` holds in every formal context. -/
theorem holds_closure (r : α → β → Prop) (t : Set β) :
    Holds r ⟨t, upperPolar r (lowerPolar r t)⟩ :=
  holds_iff_subset_closure.2 Subset.rfl

/-! ### The closure operator of a set of implications -/

/-- The closure operator on sets of attributes induced by a set of implications `L`. Its closed
sets are exactly the models of `L`. -/
def closure (L : Set (Implication β)) : ClosureOperator (Set β) :=
  ClosureOperator.ofCompletePred (IsModel L) fun _ => IsModel.sInf

@[simp]
theorem isClosed_closure_iff : (closure L).IsClosed t ↔ IsModel L t :=
  Iff.rfl

theorem isModel_closure (L : Set (Implication β)) (t : Set β) : IsModel L (closure L t) :=
  isClosed_closure_iff.1 ((closure L).isClosed_closure t)

theorem subset_closure (L : Set (Implication β)) (t : Set β) : t ⊆ closure L t :=
  (closure L).le_closure t

theorem IsModel.closure_subset {s : Set β} (ht : IsModel L t) (h : s ⊆ t) : closure L s ⊆ t :=
  ClosureOperator.closure_min h (isClosed_closure_iff.2 ht)

/-! ### Entailment -/

/-- A set of implications `L` *entails* an implication `i` if every model of `L` respects `i`. -/
def Entails (L : Set (Implication β)) (i : Implication β) : Prop :=
  ∀ t, IsModel L t → Respects t i

theorem entails_of_mem (hi : i ∈ L) : Entails L i :=
  fun _ ht => ht i hi

theorem Entails.mono {L' : Set (Implication β)} (h : Entails L i) (hL : L ⊆ L') : Entails L' i :=
  fun t ht => h t (ht.mono hL)

/-- `L` entails `A → B` iff `B` is contained in the `L`-closure of `A`. -/
theorem entails_iff : Entails L i ↔ i.conclusion ⊆ closure L i.premise :=
  ⟨fun h => h _ (isModel_closure L _) (subset_closure L _),
    fun h _ ht hp => h.trans (ht.closure_subset hp)⟩

/-! ### Soundness and completeness -/

/-- A set of implications is *sound* for a formal context if all its implications hold in the
context. -/
def IsSound (r : α → β → Prop) (L : Set (Implication β)) : Prop :=
  ∀ i ∈ L, Holds r i

/-- A set of implications is *complete* for a formal context if it entails every implication
holding in the context. -/
def IsComplete (r : α → β → Prop) (L : Set (Implication β)) : Prop :=
  ∀ i, Holds r i → Entails L i

/-- A set of implications is sound iff every intent is a model of it. -/
theorem isSound_iff : IsSound r L ↔ ∀ t, IsIntent r t → IsModel L t :=
  ⟨fun h t ht i hi => holds_iff_forall_isIntent.1 (h i hi) t ht,
    fun h _ hi => holds_iff_forall_isIntent.2 fun t ht => h t ht _ hi⟩

/-- A set of implications is complete iff every model of it is an intent. -/
theorem isComplete_iff : IsComplete r L ↔ ∀ t, IsModel L t → IsIntent r t := by
  refine ⟨fun h t ht => ?_, fun h i hi t ht => holds_iff_forall_isIntent.1 hi t (h t ht)⟩
  have ht' : upperPolar r (lowerPolar r t) ⊆ t := h _ (holds_closure r t) t ht Subset.rfl
  exact isIntent_iff.2 (ht'.antisymm (subset_upperPolar_lowerPolar r t))

/-- If `L` is sound for a formal context, every implication entailed by `L` holds in it. -/
theorem IsSound.holds_of_entails (hL : IsSound r L) (hi : Entails L i) : Holds r i :=
  holds_iff_forall_isIntent.2 fun t ht => hi t (isSound_iff.1 hL t ht)

/-- For a sound and complete set of implications, entailment coincides with validity in the
context. -/
theorem entails_iff_holds (hs : IsSound r L) (hc : IsComplete r L) : Entails L i ↔ Holds r i :=
  ⟨hs.holds_of_entails, hc i⟩

/-- The models of a sound and complete set of implications are exactly the intents. -/
theorem isModel_iff_isIntent (hs : IsSound r L) (hc : IsComplete r L) :
    IsModel L t ↔ IsIntent r t :=
  ⟨isComplete_iff.1 hc t, isSound_iff.1 hs t⟩

/-- The closure operator of a sound and complete set of implications is the intent closure. -/
theorem closure_eq_intentClosure (hs : IsSound r L) (hc : IsComplete r L) :
    closure L = intentClosure r :=
  ClosureOperator.ext_isClosed _ _ fun _ =>
    (isModel_iff_isIntent hs hc).trans (isIntent_iff.trans (intentClosure r).isClosed_iff.symm)

end Implication

end FCA
