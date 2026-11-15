/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Order.Completion

/-!
# Standard scales

A *scale* is a formal context that is used to interpret the values of a many-valued attribute,
see `FCA.ManyValued.Basic`. As for every context in this library, a scale is a bare relation.
This file studies the elementary standard scales of Ganter and Wille, Section 1.4, on an arbitrary
type `α` of values.

* The **nominal scale** `(· = ·)`. Its extents are the empty set, the singletons and the whole
  set.
* The **ordinal scale** `(· ≤ ·)`. Its concepts are Mathlib's `DedekindCut α`, and all results are
  inherited from `Mathlib.Order.Completion`; in particular `DedekindCut.principalIso : α ≃o
  DedekindCut α` for a complete lattice `α`. We only add the description of the extents.
* The **interordinal scale** `FCA.interordinal`, the apposition of `(· ≤ ·)` and `(· ≥ ·)`. Its
  extents are the intersections of a lower and an upper cut, i.e. the closed intervals when `α`
  is a complete lattice.
* The **contranominal scale** `(· ≠ ·)`. Every set is an extent, and the concept lattice is the
  powerset lattice.
* The **dichotomic scale** `FCA.dichotomic`, the nominal scale on `Bool`. It is the only nominal
  scale that is also (up to renaming of attributes) contranominal; its concept lattice is the
  four-element Boolean lattice `Set Bool`.

## Main definitions

* `Concept.orderIsoSet`: if every set of objects is an extent, the concept lattice is
  order-isomorphic to the powerset of the objects.
* `FCA.interordinal`: the interordinal scale.
* `FCA.dichotomic`: the dichotomic scale.
* `FCA.contranominalIso`: `Concept α α (· ≠ ·) ≃o Set α`.
* `FCA.dichotomicIso`: `Concept Bool Bool dichotomic ≃o Set Bool`.

## Main results

* `FCA.isExtent_eq_iff`: the extents of the nominal scale on a nontrivial type.
* `FCA.isExtent_le_iff_exists_Iic`: the extents of the ordinal scale on a complete lattice.
* `FCA.isExtent_interordinal_iff`, `FCA.isExtent_interordinal_iff_exists_Icc`: the extents of the
  interordinal scale.
* `FCA.isExtent_ne`: every set is an extent of the contranominal scale.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Order

namespace Concept

variable {α β : Type*} {r : α → β → Prop}

/-- If every set of objects is an extent, then the concept lattice is order-isomorphic to the
powerset of the object set. -/
@[simps]
def orderIsoSet (h : ∀ s : Set α, IsExtent r s) : Concept α β r ≃o Set α where
  toFun := extent
  invFun s := ofObjects r s
  left_inv _ := ofObjects_extent
  right_inv s := extent_ofObjects_of_isExtent (h s)
  map_rel_iff' := extent_subset_extent_iff

end Concept

namespace FCA

variable {α : Type*}

/-! ### The nominal scale -/

section Nominal

variable {s : Set α} {a : α}

@[simp]
theorem upperPolar_eq_singleton (a : α) : upperPolar (· = ·) {a} = ({a} : Set α) := by
  ext b
  simp [mem_upperPolar_iff, eq_comm]

@[simp]
theorem lowerPolar_eq_singleton (a : α) : lowerPolar (· = ·) {a} = ({a} : Set α) := by
  ext b
  simp [mem_lowerPolar_iff]

theorem upperPolar_eq_of_nontrivial (hs : s.Nontrivial) : upperPolar (· = ·) s = ∅ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  exact eq_empty_of_forall_notMem fun c hc => hab ((hc ha).trans (hc hb).symm)

theorem lowerPolar_eq_of_nontrivial (hs : s.Nontrivial) : lowerPolar (· = ·) s = ∅ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  exact eq_empty_of_forall_notMem fun c hc => hab ((hc ha).symm.trans (hc hb))

/-- The derivation operators of the nominal scale produce subsingletons or the whole set. -/
theorem lowerPolar_eq_subsingleton_or_eq_univ (s : Set α) :
    (lowerPolar (· = ·) s).Subsingleton ∨ lowerPolar (· = ·) s = univ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact .inr (lowerPolar_empty _)
  · exact .inl fun b hb c hc => (hb ha).trans (hc ha).symm

/-- Singletons are extents of the nominal scale. -/
theorem isExtent_eq_singleton (a : α) : IsExtent (· = ·) ({a} : Set α) :=
  ⟨{a}, lowerPolar_eq_singleton a⟩

/-- In the nominal scale on a nontrivial type the empty set is an extent. -/
theorem isExtent_eq_empty [Nontrivial α] : IsExtent (· = ·) (∅ : Set α) :=
  ⟨univ, lowerPolar_eq_of_nontrivial nontrivial_univ⟩

/-- The extents of the nominal scale on a nontrivial type are precisely the empty set, the
singletons and the whole set. -/
theorem isExtent_eq_iff [Nontrivial α] :
    IsExtent (· = ·) s ↔ s = ∅ ∨ (∃ a, s = {a}) ∨ s = univ := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases lowerPolar_eq_subsingleton_or_eq_univ t with h | h
    · exact h.eq_empty_or_singleton.imp_right .inl
    · exact .inr (.inr h)
  · rintro (rfl | ⟨a, rfl⟩ | rfl)
    exacts [isExtent_eq_empty, isExtent_eq_singleton a, .univ]

/-- The extents of the nominal scale on a nontrivial type are precisely the subsingletons and the
whole set. -/
theorem isExtent_eq_iff_subsingleton_or [Nontrivial α] :
    IsExtent (· = ·) s ↔ s.Subsingleton ∨ s = univ := by
  rw [isExtent_eq_iff, ← or_assoc, Set.subsingleton_iff_eq_empty_or_singleton]

/-- The extent of a concept of the nominal scale with an object `a` in its extent and an attribute
in its intent is the singleton `{a}`. -/
theorem extent_eq_singleton_of_mem {c : Concept α α (· = ·)} (ha : a ∈ c.extent)
    (hc : c.intent.Nonempty) : c.extent = {a} := by
  obtain ⟨b, hb⟩ := hc
  refine Subset.antisymm (fun x hx => ?_) (singleton_subset_iff.2 ha)
  exact (c.rel_extent_intent hx hb).trans (c.rel_extent_intent ha hb).symm

end Nominal

/-! ### The ordinal scale -/

section Ordinal

/-- The extents of the ordinal scale are the sets that are the lower bounds of their upper
bounds. The concept lattice of the ordinal scale is the Dedekind–MacNeille completion
`DedekindCut α`. -/
theorem isExtent_le_iff [Preorder α] {s : Set α} :
    IsExtent (· ≤ ·) s ↔ lowerBounds (upperBounds s) = s :=
  isExtent_iff

/-- The extents of the ordinal scale on a complete lattice are the principal lower sets. For the
corresponding description of the concept lattice see `DedekindCut.principalIso`. -/
theorem isExtent_le_iff_exists_Iic [CompleteLattice α] {s : Set α} :
    IsExtent (· ≤ ·) s ↔ ∃ a, s = Iic a := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨sInf t, by ext; simp [mem_lowerBounds]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨{a}, by simp⟩

end Ordinal

/-! ### The interordinal scale -/

section Interordinal

/-- The *interordinal scale* on `α`: the attribute `Sum.inl b` stands for `· ≤ b` and the
attribute `Sum.inr b` stands for `· ≥ b`. -/
def interordinal [LE α] (a : α) : α ⊕ α → Prop :=
  Sum.elim (a ≤ ·) (· ≤ a)

variable [LE α] {a b : α}

@[simp]
theorem interordinal_inl : interordinal a (.inl b) ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem interordinal_inr : interordinal a (.inr b) ↔ b ≤ a :=
  Iff.rfl

instance [DecidableLE α] : DecidableRel (interordinal (α := α)) := fun a b =>
  match b with
  | .inl b => inferInstanceAs (Decidable (a ≤ b))
  | .inr b => inferInstanceAs (Decidable (b ≤ a))

theorem lowerPolar_interordinal (t : Set (α ⊕ α)) :
    lowerPolar interordinal t = lowerBounds (Sum.inl ⁻¹' t) ∩ upperBounds (Sum.inr ⁻¹' t) := by
  ext a
  simp only [mem_lowerPolar_iff, Sum.forall, interordinal_inl, interordinal_inr]
  rfl

theorem upperPolar_interordinal (s : Set α) :
    upperPolar interordinal s = Sum.inl '' upperBounds s ∪ Sum.inr '' lowerBounds s := by
  ext (b | b) <;> simp only [mem_upperPolar_iff, interordinal_inl, interordinal_inr, mem_union,
    mem_image, Sum.inl.injEq, Sum.inr.injEq, exists_eq_right, reduceCtorEq, and_false,
    exists_false, or_false, false_or] <;> rfl

/-- The extents of the interordinal scale are the intersections of the lower bounds of a set with
the upper bounds of a set. -/
theorem isExtent_interordinal_iff {s : Set α} :
    IsExtent interordinal s ↔ ∃ u v : Set α, s = lowerBounds u ∩ upperBounds v := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, _, lowerPolar_interordinal t⟩
  · rintro ⟨u, v, rfl⟩
    refine ⟨Sum.inl '' u ∪ Sum.inr '' v, ?_⟩
    rw [lowerPolar_interordinal, preimage_union, preimage_union,
      preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
    simp

/-- The extents of the interordinal scale on a complete lattice are the closed intervals. -/
theorem isExtent_interordinal_iff_exists_Icc {α : Type*} [CompleteLattice α] {s : Set α} :
    IsExtent interordinal s ↔ ∃ a b, s = Icc a b := by
  rw [isExtent_interordinal_iff]
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨sSup v, sInf u, by ext; simp [mem_lowerBounds, mem_upperBounds, and_comm]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨{b}, {a}, by ext; simp [and_comm]⟩

end Interordinal

/-! ### The contranominal scale -/

section Contranominal

@[simp]
theorem upperPolar_ne (s : Set α) : upperPolar (· ≠ ·) s = sᶜ := by
  ext b
  exact ⟨fun h hb => h hb rfl, fun h a ha hab => h (hab ▸ ha)⟩

@[simp]
theorem lowerPolar_ne (s : Set α) : lowerPolar (· ≠ ·) s = sᶜ := by
  ext b
  exact ⟨fun h hb => h hb rfl, fun h a ha hab => h (hab ▸ ha)⟩

/-- Every set is an extent of the contranominal scale. -/
theorem isExtent_ne (s : Set α) : IsExtent (· ≠ ·) s :=
  ⟨sᶜ, by simp⟩

/-- Every set is an intent of the contranominal scale. -/
theorem isIntent_ne (s : Set α) : IsIntent (· ≠ ·) s :=
  ⟨sᶜ, by simp⟩

/-- The intent of a concept of the contranominal scale is the complement of its extent. -/
theorem intent_eq_compl_extent (c : Concept α α (· ≠ ·)) : c.intent = c.extentᶜ := by
  rw [← c.upperPolar_extent, upperPolar_ne]

/-- The extent of a concept of the contranominal scale is the complement of its intent. -/
theorem extent_eq_compl_intent (c : Concept α α (· ≠ ·)) : c.extent = c.intentᶜ := by
  rw [← c.lowerPolar_intent, lowerPolar_ne]

/-- The concept lattice of the contranominal scale on `α` is the powerset lattice of `α`. -/
def contranominalIso : Concept α α (· ≠ ·) ≃o Set α :=
  Concept.orderIsoSet isExtent_ne

@[simp]
theorem contranominalIso_apply (c : Concept α α (· ≠ ·)) : contranominalIso c = c.extent :=
  rfl

@[simp]
theorem extent_contranominalIso_symm (s : Set α) : (contranominalIso.symm s).extent = s :=
  contranominalIso.apply_symm_apply s

@[simp]
theorem intent_contranominalIso_symm (s : Set α) : (contranominalIso.symm s).intent = sᶜ := by
  rw [intent_eq_compl_extent, extent_contranominalIso_symm]

end Contranominal

/-! ### The dichotomic scale -/

section Dichotomic

/-- The *dichotomic scale*: the nominal scale on the two truth values. -/
abbrev dichotomic : Bool → Bool → Prop :=
  (· = ·)

/-- The dichotomic scale is the contranominal scale with the attributes renamed by negation. -/
theorem dichotomic_iff_ne_not {a b : Bool} : dichotomic a b ↔ a ≠ !b := by
  cases a <;> cases b <;> simp

/-- Every set of truth values is an extent of the dichotomic scale. -/
theorem isExtent_dichotomic (s : Set Bool) : IsExtent dichotomic s := by
  rw [isExtent_eq_iff_subsingleton_or]
  by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
  · exact .inr (eq_univ_of_forall fun b => by cases b <;> assumption)
  all_goals
    refine .inl fun a ha b hb => ?_
    cases a <;> cases b <;> first | rfl | contradiction

/-- The concept lattice of the dichotomic scale is the four-element Boolean lattice. -/
def dichotomicIso : Concept Bool Bool dichotomic ≃o Set Bool :=
  Concept.orderIsoSet isExtent_dichotomic

@[simp]
theorem dichotomicIso_apply (c : Concept Bool Bool dichotomic) : dichotomicIso c = c.extent :=
  rfl

@[simp]
theorem extent_dichotomicIso_symm (s : Set Bool) : (dichotomicIso.symm s).extent = s :=
  dichotomicIso.apply_symm_apply s

end Dichotomic

end FCA
