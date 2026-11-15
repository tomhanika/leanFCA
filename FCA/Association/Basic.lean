/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Finite.Basic
public import FCA.Implication.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Relation

/-!
# Association rules

An *association rule* (or *partial implication*) `A → B` of a formal context with finitely many
objects is an implication that is only required to hold for a certain fraction of the objects
having all attributes of `A`, its *confidence*, and that is only of interest if sufficiently many
objects have all attributes of `A ∪ B`, its *support*.

Association rules are represented by `FCA.Implication`; the context is a relation
`r : α → β → Prop` as everywhere in this library. Supports are counted with `Set.ncard`, so that
arbitrary sets of attributes are allowed and no decidability assumptions are needed; the lemma
`FCA.supportCount_coe` relates this to the executable `FCA.lowerPolarFinset`. The definitions make
sense for every context (with junk value `0` if there are infinitely many objects); the results
assume `Finite α`.

## Main definitions

* `FCA.supportCount r t`: the number of objects having all attributes of `t`.
* `FCA.support r t`: the fraction of objects having all attributes of `t`.
* `FCA.confidence r i`: the confidence `supp (A ∪ B) / supp A` of the rule `i = A → B`.
* `FCA.IsFrequent r θ t`: the set `t` of attributes has support at least `θ`.
* `FCA.iceberg r θ`: the *iceberg concept lattice*, the set of concepts with frequent intent.
* `FCA.luxenburgerBase r`: the rules between an intent and an intent covering it.

## Main results

* `FCA.supportCount_anti`, `FCA.support_anti`: support is antitone.
* `FCA.supportCount_closure`, `FCA.support_closure`: `t` and its closure `t''` have the same
  support.
* `FCA.Implication.holds_iff_supportCount_eq`, `FCA.Implication.holds_iff_confidence_eq_one`: the
  implications of a context are its association rules of confidence `1`.
* `FCA.confidence_closure`, `FCA.confidence_eq_confidence_closure`: confidence only depends on
  closures, and every rule has the same confidence as a rule between two comparable intents.
* `FCA.confidence_mul_confidence`: confidence is multiplicative along chains (Luxenburger).
* `FCA.IsFrequent.anti`, `FCA.isUpperSet_iceberg`: the frequent sets are closed under subsets, and
  the iceberg lattice is an upper set of the concept lattice.
* `FCA.transGen_luxenburgerBase`, `FCA.eq_confidence_of_luxenburgerBase`: completeness of the
  Luxenburger base. Any two comparable intents are connected by a chain of rules of the base, and
  hence the confidences of all rules between intents are determined by the confidences of the
  rules of the base and multiplicativity.

## Implementation notes

Ganter and Wille, and Stumme et al., restrict the Luxenburger base to the rules that reach given
thresholds of support and confidence. `FCA.luxenburgerBase` contains all rules between
neighbouring intents; the restricted bases are obtained by intersecting with the respective
conditions.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* M. Luxenburger, *Implications partielles dans un contexte*, Math. Inform. Sci. Humaines 113
  (1991)
* G. Stumme, R. Taouil, Y. Bastide, N. Pasquier, L. Lakhal, *Computing iceberg concept lattices
  with TITANIC*, Data Knowl. Eng. 42 (2002)
-/

@[expose] public section

open Set Order

namespace FCA

variable {α β : Type*} (r : α → β → Prop) {t u w : Set β} {i : Implication β} {θ θ' : ℚ}

/-! ### Support -/

/-- The *support count* of a set `t` of attributes: the number of objects having all attributes
of `t`. -/
noncomputable def supportCount (t : Set β) : ℕ :=
  (lowerPolar r t).ncard

/-- The *support* of a set `t` of attributes: the fraction of objects having all attributes of
`t`. -/
noncomputable def support (t : Set β) : ℚ :=
  supportCount r t / Nat.card α

/-- The support count can be computed by the executable derivation operator. -/
theorem supportCount_coe [Fintype α] [DecidableRel r] (t : Finset β) :
    supportCount r (t : Set β) = (lowerPolarFinset r t).card := by
  rw [supportCount, ← coe_lowerPolarFinset, ncard_coe_finset]

@[simp]
theorem supportCount_empty : supportCount r ∅ = Nat.card α := by
  rw [supportCount, lowerPolar_empty, ncard_univ]

theorem supportCount_union (t u : Set β) :
    supportCount r (t ∪ u) = (lowerPolar r t ∩ lowerPolar r u).ncard := by
  rw [supportCount, lowerPolar_union]

/-- The support count of the intent of a concept is the size of its extent. -/
theorem supportCount_intent (c : Concept α β r) : supportCount r c.intent = c.extent.ncard := by
  rw [supportCount, c.lowerPolar_intent]

/-- A set of attributes and its closure have the same support count. -/
@[simp]
theorem supportCount_closure (t : Set β) :
    supportCount r (upperPolar r (lowerPolar r t)) = supportCount r t := by
  rw [supportCount, lowerPolar_upperPolar_lowerPolar, supportCount]

/-- A set of attributes and its closure have the same support. -/
@[simp]
theorem support_closure (t : Set β) :
    support r (upperPolar r (lowerPolar r t)) = support r t := by
  rw [support, supportCount_closure, support]

theorem support_nonneg (t : Set β) : 0 ≤ support r t :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

section Finite

variable [Finite α]

variable {r} in
/-- Support count is antitone: larger sets of attributes are shared by fewer objects. -/
theorem supportCount_anti (h : t ⊆ u) : supportCount r u ≤ supportCount r t :=
  ncard_le_ncard (lowerPolar_anti r h)

theorem supportCount_le_card (t : Set β) : supportCount r t ≤ Nat.card α :=
  (ncard_le_ncard (subset_univ _)).trans_eq (ncard_univ α)

variable {r} in
/-- Support is antitone: larger sets of attributes are shared by fewer objects. -/
theorem support_anti (h : t ⊆ u) : support r u ≤ support r t :=
  div_le_div_of_nonneg_right (Nat.cast_le.2 (supportCount_anti h)) (Nat.cast_nonneg _)

theorem support_le_one (t : Set β) : support r t ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.2 (supportCount_le_card r t)) (Nat.cast_nonneg _)

@[simp]
theorem support_empty [Nonempty α] : support r ∅ = 1 := by
  rw [support, supportCount_empty]
  exact div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')

variable {r} in
/-- Support count is strictly antitone on intents. -/
theorem supportCount_lt_of_ssubset (ht : IsIntent r t) (hu : IsIntent r u) (h : t ⊂ u) :
    supportCount r u < supportCount r t := by
  refine ncard_lt_ncard ⟨lowerPolar_anti r h.subset, fun h' => h.not_subset ?_⟩
  have := upperPolar_anti r h'
  rwa [isIntent_iff.1 ht, isIntent_iff.1 hu] at this

variable {r} in
/-- An implication holds in a context iff adding its conclusion to its premise does not change
the support count. -/
theorem Implication.holds_iff_supportCount_eq :
    i.Holds r ↔ supportCount r (i.premise ∪ i.conclusion) = supportCount r i.premise := by
  rw [Implication.holds_iff_lowerPolar_subset, supportCount_union, supportCount]
  refine ⟨fun h => by rw [inter_eq_left.2 h], fun h => ?_⟩
  exact inter_eq_left.1 (eq_of_subset_of_ncard_le inter_subset_left h.ge)

variable {r} in
/-- An implication holds in a context iff adding its conclusion to its premise does not change
the support. -/
theorem Implication.holds_iff_support_eq [Nonempty α] :
    i.Holds r ↔ support r (i.premise ∪ i.conclusion) = support r i.premise := by
  have h : (Nat.card α : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [Implication.holds_iff_supportCount_eq, support, support, div_left_inj' h, Nat.cast_inj]

end Finite

/-! ### Confidence -/

/-- The *confidence* of the association rule `A → B`: the fraction of the objects having all
attributes of `A` that also have all attributes of `B`. It is `0` if no object has all attributes
of `A`. -/
noncomputable def confidence (i : Implication β) : ℚ :=
  supportCount r (i.premise ∪ i.conclusion) / supportCount r i.premise

theorem confidence_nonneg (i : Implication β) : 0 ≤ confidence r i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

variable {r} in
/-- The confidence of a rule only depends on the extents of its premise and its conclusion. -/
theorem confidence_congr {j : Implication β} (hp : lowerPolar r i.premise = lowerPolar r j.premise)
    (hc : lowerPolar r i.conclusion = lowerPolar r j.conclusion) :
    confidence r i = confidence r j := by
  simp only [confidence, supportCount, lowerPolar_union, hp, hc]

/-- The confidence of a rule only depends on the closures of its premise and its conclusion. -/
@[simp]
theorem confidence_closure (t u : Set β) :
    confidence r ⟨upperPolar r (lowerPolar r t), upperPolar r (lowerPolar r u)⟩ =
      confidence r ⟨t, u⟩ :=
  confidence_congr (lowerPolar_upperPolar_lowerPolar r t) (lowerPolar_upperPolar_lowerPolar r u)

/-- Adding the premise to the conclusion does not change the confidence. -/
@[simp]
theorem confidence_union_left (t u : Set β) : confidence r ⟨t, t ∪ u⟩ = confidence r ⟨t, u⟩ := by
  simp only [confidence, ← union_assoc, union_self]

/-- Every rule `A → B` has the same confidence as the rule `A'' → (A ∪ B)''` between two
comparable intents. -/
theorem confidence_eq_confidence_closure (i : Implication β) :
    confidence r i = confidence r ⟨upperPolar r (lowerPolar r i.premise),
      upperPolar r (lowerPolar r (i.premise ∪ i.conclusion))⟩ := by
  rw [confidence_closure, confidence_union_left]

variable {r} in
/-- The confidence of a rule whose premise is contained in its conclusion. -/
theorem confidence_of_subset (h : t ⊆ u) :
    confidence r ⟨t, u⟩ = supportCount r u / supportCount r t := by
  rw [confidence, union_eq_self_of_subset_left h]

section Finite

variable [Finite α]

theorem confidence_le_one (i : Implication β) : confidence r i ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.2 (supportCount_anti subset_union_left)) (Nat.cast_nonneg _)

variable {r} in
/-- The implications of a context are its association rules of confidence `1`, provided some
object has all attributes of the premise. -/
theorem Implication.holds_iff_confidence_eq_one (h : supportCount r i.premise ≠ 0) :
    i.Holds r ↔ confidence r i = 1 := by
  rw [Implication.holds_iff_supportCount_eq, confidence,
    div_eq_one_iff_eq (Nat.cast_ne_zero.2 h), Nat.cast_inj]

/-- The support of `A ∪ B` is the support of `A` times the confidence of `A → B`. -/
theorem support_mul_confidence (i : Implication β) :
    support r i.premise * confidence r i = support r (i.premise ∪ i.conclusion) := by
  rw [support, support, confidence]
  rcases eq_or_ne (supportCount r i.premise) 0 with h | h
  · have h' : supportCount r (i.premise ∪ i.conclusion) = 0 :=
      Nat.eq_zero_of_le_zero (h ▸ supportCount_anti subset_union_left)
    simp [h, h']
  · have : (supportCount r i.premise : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [div_mul_div_comm, mul_comm, mul_div_mul_right _ _ this]

variable {r} in
/-- **Luxenburger's multiplicativity**: the confidence of a rule `t → w` is the product of the
confidences of `t → u` and `u → w` for every `u` between `t` and `w`. -/
theorem confidence_mul_confidence (htu : t ⊆ u) (huw : u ⊆ w) :
    confidence r ⟨t, u⟩ * confidence r ⟨u, w⟩ = confidence r ⟨t, w⟩ := by
  rw [confidence_of_subset htu, confidence_of_subset huw, confidence_of_subset (htu.trans huw)]
  rcases eq_or_ne (supportCount r u) 0 with h | h
  · have h' : supportCount r w = 0 := Nat.eq_zero_of_le_zero (h ▸ supportCount_anti huw)
    simp [h, h']
  · have : (supportCount r u : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [div_mul_div_comm, mul_comm, mul_div_mul_right _ _ this]

end Finite

/-! ### Frequent sets and iceberg lattices -/

/-- A set of attributes is *frequent* with respect to the minimum support `θ` if its support is
at least `θ`. -/
def IsFrequent (θ : ℚ) (t : Set β) : Prop :=
  θ ≤ support r t

variable {r}

/-- A set of attributes is frequent iff its closure is. -/
@[simp]
theorem isFrequent_closure_iff :
    IsFrequent r θ (upperPolar r (lowerPolar r t)) ↔ IsFrequent r θ t := by
  rw [IsFrequent, support_closure, IsFrequent]

theorem IsFrequent.mono (h : IsFrequent r θ t) (hθ : θ' ≤ θ) : IsFrequent r θ' t :=
  hθ.trans h

/-- Every subset of a frequent set is frequent. -/
theorem IsFrequent.anti [Finite α] (h : IsFrequent r θ u) (htu : t ⊆ u) : IsFrequent r θ t :=
  h.trans (support_anti htu)

variable (r) in
/-- The frequent sets of attributes form a lower set. -/
theorem isLowerSet_setOf_isFrequent [Finite α] (θ : ℚ) : IsLowerSet {t | IsFrequent r θ t} :=
  fun _ _ htu hu => hu.anti htu

variable (r) in
/-- The empty set of attributes is frequent for every minimum support `θ ≤ 1`. -/
theorem isFrequent_empty [Finite α] [Nonempty α] (hθ : θ ≤ 1) : IsFrequent r θ ∅ :=
  hθ.trans_eq (support_empty r).symm

variable (r) in
/-- The *iceberg concept lattice* for the minimum support `θ`: the set of all concepts whose
intent is frequent. -/
def iceberg (θ : ℚ) : Set (Concept α β r) :=
  {c | IsFrequent r θ c.intent}

@[simp]
theorem mem_iceberg {c : Concept α β r} : c ∈ iceberg r θ ↔ IsFrequent r θ c.intent :=
  Iff.rfl

theorem mem_iceberg_iff {c : Concept α β r} :
    c ∈ iceberg r θ ↔ θ ≤ c.extent.ncard / Nat.card α := by
  rw [mem_iceberg, IsFrequent, support, supportCount_intent]

variable (r) in
/-- The iceberg concept lattice is an upper set of the concept lattice. -/
theorem isUpperSet_iceberg [Finite α] (θ : ℚ) : IsUpperSet (iceberg r θ) :=
  fun _ _ hcd hc => hc.anti (Concept.intent_subset_intent_iff.2 hcd)

/-- The iceberg concept lattice is closed under arbitrary nonempty suprema. -/
theorem sSup_mem_iceberg [Finite α] {C : Set (Concept α β r)} {c : Concept α β r} (hc : c ∈ C)
    (h : c ∈ iceberg r θ) : sSup C ∈ iceberg r θ :=
  isUpperSet_iceberg r θ (le_sSup hc) h

theorem iceberg_anti (r : α → β → Prop) : Antitone (iceberg r) :=
  fun _ _ hθ _ hc => hc.mono hθ

/-- The top concept belongs to the iceberg concept lattice for every minimum support `θ ≤ 1`. -/
theorem top_mem_iceberg [Finite α] [Nonempty α] (hθ : θ ≤ 1) : ⊤ ∈ iceberg r θ := by
  rw [mem_iceberg_iff]
  have h : (⊤ : Concept α β r).extent = univ := rfl
  rw [h, ncard_univ, div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
  exact hθ

/-! ### The Luxenburger base -/

variable (r) in
/-- The *Luxenburger base* of a context: the rules `t → u` where `t` and `u` are intents and `u`
covers `t` among the intents, i.e. the rules along the edges of the diagram of the concept
lattice. -/
def luxenburgerBase : Set (Implication β) :=
  {i | IsIntent r i.premise ∧ IsIntent r i.conclusion ∧ i.premise ⊂ i.conclusion ∧
    ∀ u, IsIntent r u → i.premise ⊆ u → u ⊆ i.conclusion → u = i.premise ∨ u = i.conclusion}

theorem mem_luxenburgerBase :
    i ∈ luxenburgerBase r ↔ IsIntent r i.premise ∧ IsIntent r i.conclusion ∧
      i.premise ⊂ i.conclusion ∧ ∀ u, IsIntent r u → i.premise ⊆ u → u ⊆ i.conclusion →
        u = i.premise ∨ u = i.conclusion :=
  Iff.rfl

/-- No rule of the Luxenburger base is an implication of the context. -/
theorem not_holds_of_mem_luxenburgerBase (hi : i ∈ luxenburgerBase r) : ¬i.Holds r := by
  intro h
  refine hi.2.2.1.not_subset ?_
  rw [← isIntent_iff.1 hi.1]
  exact Implication.holds_iff_subset_closure.1 h

/-- Any two intents `t ⊂ u` of a context with finitely many objects are connected by a chain of
rules of the Luxenburger base. -/
theorem transGen_luxenburgerBase [Finite α] (ht : IsIntent r t) (hu : IsIntent r u) (h : t ⊂ u) :
    Relation.TransGen (fun t u => (⟨t, u⟩ : Implication β) ∈ luxenburgerBase r) t u := by
  induction hn : supportCount r t - supportCount r u using Nat.strong_induction_on
    generalizing t u with
  | _ n ih =>
    subst hn
    by_cases hb : (⟨t, u⟩ : Implication β) ∈ luxenburgerBase r
    · exact .single hb
    · obtain ⟨w, hw, htw, hwu⟩ : ∃ w, IsIntent r w ∧ t ⊂ w ∧ w ⊂ u := by
        by_contra hw
        refine hb ⟨ht, hu, h, fun w hw' h₁ h₂ => ?_⟩
        by_contra hne
        rw [not_or] at hne
        exact hw ⟨w, hw', h₁.ssubset_of_ne (Ne.symm hne.1), h₂.ssubset_of_ne hne.2⟩
      have h₁ := supportCount_lt_of_ssubset ht hw htw
      have h₂ := supportCount_lt_of_ssubset hw hu hwu
      exact (ih _ (by lia) ht hw htw rfl).trans (ih _ (by lia) hw hu hwu rfl)

/-- **Completeness of the Luxenburger base**: the confidences of all rules between comparable
intents are determined by the confidences of the rules of the Luxenburger base. More precisely,
every assignment `c` of numbers to rules that agrees with the confidence on the Luxenburger base
and that is multiplicative along chains of intents agrees with the confidence on all rules
`t → u` between intents `t ⊂ u`.

By `FCA.confidence_eq_confidence_closure` every rule has the same confidence as a rule between
intents `t ⊆ u`, and by `FCA.Implication.holds_iff_confidence_eq_one` the case `t = u` is that of
the implications of the context. -/
theorem eq_confidence_of_luxenburgerBase [Finite α] (c : Set β → Set β → ℚ)
    (hbase : ∀ i ∈ luxenburgerBase r, c i.premise i.conclusion = confidence r i)
    (hmul : ∀ t u w, IsIntent r t → IsIntent r u → IsIntent r w → t ⊆ u → u ⊆ w →
      c t u * c u w = c t w)
    (ht : IsIntent r t) (hu : IsIntent r u) (h : t ⊂ u) : c t u = confidence r ⟨t, u⟩ := by
  have key : ∀ u, Relation.TransGen (fun t u => (⟨t, u⟩ : Implication β) ∈ luxenburgerBase r) t u →
      IsIntent r u ∧ t ⊂ u ∧ c t u = confidence r ⟨t, u⟩ := by
    intro u hu
    induction hu with
    | single hb => exact ⟨hb.2.1, hb.2.2.1, hbase _ hb⟩
    | tail _ hb ih =>
      obtain ⟨hv, htv, hc⟩ := ih
      refine ⟨hb.2.1, htv.trans hb.2.2.1, ?_⟩
      rw [← hmul _ _ _ ht hv hb.2.1 htv.subset hb.2.2.1.subset, hc, hbase _ hb,
        confidence_mul_confidence htv.subset hb.2.2.1.subset]
  exact (key u (transGen_luxenburgerBase ht hu h)).2.2

end FCA
