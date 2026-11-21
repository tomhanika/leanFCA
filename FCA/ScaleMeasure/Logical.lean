/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.ScaleMeasure.Hierarchy

/-!
# Logical attributes and the conjunctive normal form of scale-measures

Scale contexts whose attributes are propositional formulas over the attributes of a context `r`
are interpretable in terms of `r`. This file formalises Section 3.1 and Proposition 23 of
Hanika and Hirth, *On the Lattice of Conceptual Measurements*.

## Main definitions

* `FCA.Formula β`: propositional formulas over attributes, with `FCA.Formula.Realize`.
* `FCA.Formula.extent r φ`: the objects of `r` satisfying `φ`.
* `FCA.logicalScale r`: the scale on the objects of `r` whose attributes are all formulas.
* `FCA.conjunctiveScale r`: the scale whose attributes are (possibly infinite) conjunctions of
  attributes, represented as sets of attributes.
* `FCA.ClosureSubsystem.conjunctiveNormalForm`: the conjunctive normal form of a scale-measure.

## Main results

* `FCA.Formula.extent_of_isConjunctive`, `FCA.Formula.extent_of_isDisjunctive`,
  `FCA.Formula.extent_not_var`: the derivations of logical attributes (Lemma 15).
* `FCA.isScaleMeasure_logicalScale_iff`: the identity is a measure into a scale of formulas iff
  the extent of each formula is an extent of the context (Proposition 16).
* `FCA.isScaleMeasure_logicalScale_of_isConjunctive`: conjunctive formulas always yield
  scale-measures (Corollary 17).
* `FCA.Formula.not_isExtent_extent_or`: disjunctions need not (Figure 4).
* `FCA.IsScaleMeasure.scaleEquiv_conjunctiveNormalForm`: every scale-measure is equivalent to
  its conjunctive normal form (Proposition 23).

## Implementation notes

The conjunction `⋀ Aᴵ` used in the conjunctive normal form may be infinite, and it is empty when
the objects in `A` share no attribute. `FCA.Formula` only has binary connectives, so conjunctions
are represented by sets of attributes in `FCA.conjunctiveScale`;
`FCA.Formula.extent_of_isConjunctive` shows that this agrees with conjunctive formulas.

## References

* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β γ δ : Type*} {r : α → β → Prop}

/-- Propositional formulas over a type `β` of attributes. -/
inductive Formula (β : Type*) : Type _
  /-- An attribute as a propositional variable. -/
  | var : β → Formula β
  /-- Conjunction. -/
  | and : Formula β → Formula β → Formula β
  /-- Disjunction. -/
  | or : Formula β → Formula β → Formula β
  /-- Negation. -/
  | not : Formula β → Formula β

namespace Formula

/-- A set `t` of attributes satisfies the formula `φ`. -/
def Realize (t : Set β) : Formula β → Prop
  | var b => b ∈ t
  | and φ ψ => Realize t φ ∧ Realize t ψ
  | or φ ψ => Realize t φ ∨ Realize t ψ
  | not φ => ¬Realize t φ

/-- The propositional variables of a formula. -/
def vars : Formula β → Set β
  | var b => {b}
  | and φ ψ => vars φ ∪ vars ψ
  | or φ ψ => vars φ ∪ vars ψ
  | not φ => vars φ

/-- A formula built from variables using conjunction only. -/
def IsConjunctive : Formula β → Prop
  | var _ => True
  | and φ ψ => IsConjunctive φ ∧ IsConjunctive ψ
  | or _ _ => False
  | not _ => False

/-- A formula built from variables using disjunction only. -/
def IsDisjunctive : Formula β → Prop
  | var _ => True
  | and _ _ => False
  | or φ ψ => IsDisjunctive φ ∧ IsDisjunctive ψ
  | not _ => False

theorem vars_nonempty (φ : Formula β) : φ.vars.Nonempty := by
  induction φ with
  | var b => exact singleton_nonempty b
  | and φ ψ ih _ => exact ih.mono subset_union_left
  | or φ ψ ih _ => exact ih.mono subset_union_left
  | not φ ih => exact ih

theorem realize_of_isConjunctive {φ : Formula β} (hφ : φ.IsConjunctive) {t : Set β} :
    φ.Realize t ↔ φ.vars ⊆ t := by
  induction φ with
  | var b => simp [Realize, vars]
  | and φ ψ ih₁ ih₂ => simp [Realize, vars, ih₁ hφ.1, ih₂ hφ.2]
  | or φ ψ => exact hφ.elim
  | not φ => exact hφ.elim

theorem realize_of_isDisjunctive {φ : Formula β} (hφ : φ.IsDisjunctive) {t : Set β} :
    φ.Realize t ↔ (φ.vars ∩ t).Nonempty := by
  induction φ with
  | var b => simp [Realize, vars]
  | and φ ψ => exact hφ.elim
  | or φ ψ ih₁ ih₂ => simp [Realize, vars, ih₁ hφ.1, ih₂ hφ.2, union_inter_distrib_right]
  | not φ => exact hφ.elim

/-- The set of objects of the context `r` whose intent satisfies `φ`. -/
def extent (r : α → β → Prop) (φ : Formula β) : Set α :=
  {a | φ.Realize (upperPolar r {a})}

@[simp]
theorem mem_extent {φ : Formula β} {a : α} : a ∈ φ.extent r ↔ φ.Realize (upperPolar r {a}) :=
  Iff.rfl

@[simp]
theorem extent_var (r : α → β → Prop) (b : β) : (var b).extent r = lowerPolar r {b} := by
  ext a
  simp [Realize]

@[simp]
theorem extent_and (r : α → β → Prop) (φ ψ : Formula β) :
    (and φ ψ).extent r = φ.extent r ∩ ψ.extent r :=
  rfl

@[simp]
theorem extent_or (r : α → β → Prop) (φ ψ : Formula β) :
    (or φ ψ).extent r = φ.extent r ∪ ψ.extent r :=
  rfl

@[simp]
theorem extent_not (r : α → β → Prop) (φ : Formula β) : (not φ).extent r = (φ.extent r)ᶜ :=
  rfl

/-- The extent of a conjunctive formula is the derivation of its variables. -/
theorem extent_of_isConjunctive {φ : Formula β} (hφ : φ.IsConjunctive) :
    φ.extent r = lowerPolar r φ.vars := by
  ext a
  rw [mem_extent, realize_of_isConjunctive hφ, subset_upperPolar_iff_subset_lowerPolar,
    singleton_subset_iff]

/-- The extent of a disjunctive formula is the union of the attribute extents of its
variables. -/
theorem extent_of_isDisjunctive {φ : Formula β} (hφ : φ.IsDisjunctive) :
    φ.extent r = ⋃ b ∈ φ.vars, lowerPolar r {b} := by
  ext a
  simp [realize_of_isDisjunctive hφ, Set.Nonempty]

/-- The extent of a negated attribute is the complement of its attribute extent. -/
theorem extent_not_var (r : α → β → Prop) (b : β) :
    (not (var b)).extent r = (lowerPolar r {b})ᶜ := by
  simp

/-- The extent of a conjunctive formula is an extent of the context. -/
theorem isExtent_extent_of_isConjunctive {φ : Formula β} (hφ : φ.IsConjunctive) :
    IsExtent r (φ.extent r) :=
  extent_of_isConjunctive hφ ▸ isExtent_lowerPolar

/-- In a nominal scale with three distinct values `a`, `b`, `c`, the disjunction `a ∨ b` does not
describe an extent. -/
theorem not_isExtent_extent_or {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬IsExtent (· = ·) ((or (var a) (var b)).extent (α := α) (· = ·)) := by
  intro h
  have hc : c ∈ (or (var a) (var b)).extent (α := α) (· = ·) := by
    rw [← h.eq]
    intro m hm
    have ha : a = m := hm (a := a) (by simp)
    have hb : b = m := hm (a := b) (by simp)
    exact absurd (ha.trans hb.symm) hab
  simp [hac.symm, hbc.symm] at hc

/-- In a nominal scale with two distinct values, the negation of an attribute does not describe
an extent as soon as its complement has two elements. -/
theorem not_isExtent_extent_not {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬IsExtent (· = ·) ((not (var a)).extent (α := α) (· = ·)) := by
  intro h
  have ha : a ∈ (not (var a)).extent (α := α) (· = ·) := by
    rw [← h.eq]
    intro m hm
    have hb : b = m := hm (a := b) (by simp [hab.symm])
    have hc : c = m := hm (a := c) (by simp [hac.symm])
    exact absurd (hb.trans hc.symm) hbc
  simp at ha

end Formula

/-! ### Logical scales -/

/-- The *logical scale* of a context: the objects of `r` with all propositional formulas over
the attributes of `r` as attributes. An object has the attribute `φ` if its intent
satisfies `φ`. -/
def logicalScale (r : α → β → Prop) : α → Formula β → Prop :=
  fun a φ ↦ φ.Realize (upperPolar r {a})

@[simp]
theorem lowerPolar_logicalScale_singleton (r : α → β → Prop) (φ : Formula β) :
    lowerPolar (logicalScale r) {φ} = φ.extent r := by
  ext a
  simp [logicalScale]

/-- The identity is a scale-measure into the scale given by a set `Φ` of formulas iff the extent
of every formula in `Φ` is an extent of the context. -/
theorem isScaleMeasure_logicalScale_iff {Φ : Set (Formula β)} :
    IsScaleMeasure r (restrictAttributes (logicalScale r) Φ) id ↔
      ∀ φ ∈ Φ, IsExtent r (φ.extent r) := by
  rw [isScaleMeasure_iff_forall_singleton]
  have (φ : Φ) : lowerPolar (restrictAttributes (logicalScale r) Φ) {φ} = φ.1.extent r := by
    ext a
    simp [restrictAttributes, logicalScale]
  simp [this]

/-- The identity is a scale-measure into the scale given by a single formula `φ` iff the extent
of `φ` is an extent of the context. -/
theorem isScaleMeasure_logicalScale_singleton_iff {φ : Formula β} :
    IsScaleMeasure r (restrictAttributes (logicalScale r) {φ}) id ↔ IsExtent r (φ.extent r) := by
  simp [isScaleMeasure_logicalScale_iff]

/-- Conjunctive formulas always yield scale-measures. -/
theorem isScaleMeasure_logicalScale_of_isConjunctive {Φ : Set (Formula β)}
    (hΦ : ∀ φ ∈ Φ, φ.IsConjunctive) :
    IsScaleMeasure r (restrictAttributes (logicalScale r) Φ) id :=
  isScaleMeasure_logicalScale_iff.2 fun φ hφ ↦ Formula.isExtent_extent_of_isConjunctive (hΦ φ hφ)

/-! ### Conjunctive scales and the conjunctive normal form -/

/-- The *conjunctive scale* of a context: its attributes are sets `X` of attributes of `r`, read
as the conjunction of the members of `X`. -/
def conjunctiveScale (r : α → β → Prop) : α → Set β → Prop :=
  fun a X ↦ a ∈ lowerPolar r X

@[simp]
theorem lowerPolar_conjunctiveScale_singleton (r : α → β → Prop) (X : Set β) :
    lowerPolar (conjunctiveScale r) {X} = lowerPolar r X := by
  ext a
  simp [conjunctiveScale]

/-- A conjunctive formula and its set of variables are the same conjunctive attribute. -/
theorem logicalScale_iff_conjunctiveScale {φ : Formula β} (hφ : φ.IsConjunctive) (a : α) :
    logicalScale r a φ ↔ conjunctiveScale r a φ.vars := by
  rw [conjunctiveScale, ← Formula.extent_of_isConjunctive hφ]
  rfl

/-- The identity is a scale-measure into every scale of conjunctive attributes. -/
theorem isScaleMeasure_conjunctiveScale (r : α → β → Prop) (f : δ → Set β) :
    IsScaleMeasure r (fun a n ↦ conjunctiveScale r a (f n)) id := by
  rw [isScaleMeasure_iff_forall_singleton]
  intro n
  have : lowerPolar (fun a n ↦ conjunctiveScale r a (f n)) {n} = lowerPolar r (f n) := by
    ext a
    simp [conjunctiveScale]
  rw [preimage_id, this]
  exact isExtent_lowerPolar

namespace ClosureSubsystem

variable {𝒜 : ClosureSubsystem (IsExtent r)}

/-- The *conjunctive normal form* of a closure system `𝒜` of extents of `r`: the scale with one
conjunctive attribute `⋀ Aᴵ` for every `A ∈ 𝒜`. -/
def conjunctiveNormalForm (𝒜 : ClosureSubsystem (IsExtent r)) : α → {A // A ∈ 𝒜} → Prop :=
  fun a A ↦ conjunctiveScale r a (upperPolar r A.1)

/-- The conjunctive normal form coincides with the canonical scale. -/
theorem conjunctiveNormalForm_eq_context (𝒜 : ClosureSubsystem (IsExtent r)) :
    𝒜.conjunctiveNormalForm = 𝒜.context := by
  ext a A
  rw [conjunctiveNormalForm, conjunctiveScale, (𝒜.isExtent A.2).eq]
  rfl

theorem isScaleMeasure_conjunctiveNormalForm (𝒜 : ClosureSubsystem (IsExtent r)) :
    IsScaleMeasure r 𝒜.conjunctiveNormalForm id :=
  isScaleMeasure_conjunctiveScale r _

@[simp]
theorem scaleExtents_conjunctiveNormalForm (𝒜 : ClosureSubsystem (IsExtent r)) :
    scaleExtents 𝒜.conjunctiveNormalForm id = 𝒜.carrier := by
  rw [conjunctiveNormalForm_eq_context, scaleExtents_context]

end ClosureSubsystem

/-- **Conjunctive normal form**: every scale-measure is equivalent to the identity measure into
a scale whose attributes are conjunctions of attributes of the measured context. -/
theorem IsScaleMeasure.scaleEquiv_conjunctiveNormalForm {s : γ → δ → Prop} {σ : α → γ}
    (h : IsScaleMeasure r s σ) :
    ScaleEquiv s σ h.closureSubsystem.conjunctiveNormalForm id :=
  (ClosureSubsystem.scaleExtents_conjunctiveNormalForm h.closureSubsystem).symm

end FCA
