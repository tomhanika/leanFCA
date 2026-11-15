/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Closure

/-!
# The lectic order

For a linearly ordered attribute type `β`, the *lectic order* on `Finset β` is the lexicographic
order on characteristic vectors: `A` is lectically smaller than `B` if the smallest element in
which `A` and `B` differ belongs to `B`. It is the linear order along which Ganter's NextClosure
algorithm enumerates the closed sets of a closure operator.

## Main definitions

* `FCA.LecticLTAt`: `A <ₗ[i] B` means `i ∈ B \ A` and `A`, `B` agree on all elements below `i`.
* `FCA.LecticLT`: `A <ₗ B`, the (strict) lectic order.
* `FCA.oplus`: `A ⊕ i = c ((A ∩ {j | j < i}) ∪ {i})` for a closure operator `c` on `Finset β`.

## Main results

* `FCA.LecticLT.instIsStrictTotalOrder`: the lectic order is a strict total order.
* `FCA.lecticLT_of_ssubset`: the lectic order extends proper inclusion.
* `FCA.wellFounded_lecticGT`: on a finite type, there are no infinite lectically ascending chains.
* `FCA.LecticLTAt.oplus_subset`, `FCA.LecticLTAt.lecticLTAt_oplus`: if `A <ₗ[i] B` and `B` is
  closed, then `A ⊕ i ⊆ B` and `A <ₗ[i] A ⊕ i`.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Finset

namespace FCA

variable {β : Type*} [LinearOrder β] {A B C : Finset β} {i j : β}

/-- `A <ₗ[i] B`: the set `A` is *lectically smaller than `B` at `i`*, i.e. `i` belongs to `B` but
not to `A`, and `A` and `B` contain the same elements below `i`. -/
def LecticLTAt (i : β) (A B : Finset β) : Prop :=
  i ∈ B ∧ i ∉ A ∧ ∀ j < i, j ∈ A ↔ j ∈ B

/-- `A <ₗ B`: the set `A` is *lectically smaller* than `B`, i.e. the smallest element in which
`A` and `B` differ belongs to `B`. -/
def LecticLT (A B : Finset β) : Prop :=
  ∃ i, LecticLTAt i A B

@[inherit_doc] scoped notation:50 A:51 " <ₗ[" i "] " B:51 => LecticLTAt i A B

@[inherit_doc] scoped infix:50 " <ₗ " => LecticLT

theorem lecticLTAt_iff_filter :
    A <ₗ[i] B ↔ i ∈ B ∧ i ∉ A ∧ A.filter (· < i) = B.filter (· < i) := by
  simp only [LecticLTAt, Finset.ext_iff, mem_filter, and_congr_left_iff]

instance LecticLTAt.instDecidable : Decidable (A <ₗ[i] B) :=
  decidable_of_iff _ lecticLTAt_iff_filter.symm

theorem lecticLT_iff_exists_mem : A <ₗ B ↔ ∃ i ∈ B, A <ₗ[i] B :=
  ⟨fun ⟨i, hi⟩ => ⟨i, hi.1, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩

instance LecticLT.instDecidable : Decidable (A <ₗ B) :=
  decidable_of_iff _ lecticLT_iff_exists_mem.symm

theorem LecticLTAt.lecticLT (h : A <ₗ[i] B) : A <ₗ B :=
  ⟨i, h⟩

theorem LecticLTAt.mem (h : A <ₗ[i] B) : i ∈ B :=
  h.1

theorem LecticLTAt.notMem (h : A <ₗ[i] B) : i ∉ A :=
  h.2.1

theorem LecticLTAt.mem_iff (h : A <ₗ[i] B) (hj : j < i) : j ∈ A ↔ j ∈ B :=
  h.2.2 j hj

/-- If `A <ₗ[i] B` and `A <ₗ[j] C` with `i < j`, then `C <ₗ[i] B`. -/
theorem LecticLTAt.of_lt (hB : A <ₗ[i] B) (hC : A <ₗ[j] C) (hij : i < j) : C <ₗ[i] B :=
  ⟨hB.mem, fun hi => hB.notMem ((hC.mem_iff hij).2 hi), fun _ hk =>
    (hC.mem_iff (hk.trans hij)).symm.trans (hB.mem_iff hk)⟩

/-- Lectic comparisons at positions compose: the result is witnessed at the smaller position. -/
theorem LecticLTAt.trans (hAB : A <ₗ[i] B) (hBC : B <ₗ[j] C) : A <ₗ[min i j] C := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [min_eq_left hij.le]
    exact ⟨(hBC.mem_iff hij).1 hAB.mem, hAB.notMem, fun _ hk =>
      (hAB.mem_iff hk).trans (hBC.mem_iff (hk.trans hij))⟩
  · exact absurd hAB.mem hBC.notMem
  · rw [min_eq_right hji.le]
    exact ⟨hBC.mem, fun hj => hBC.notMem ((hAB.mem_iff hji).1 hj), fun _ hk =>
      (hAB.mem_iff (hk.trans hji)).trans (hBC.mem_iff hk)⟩

/-- The position at which `A` is lectically smaller than `B` is unique. -/
theorem LecticLTAt.eq (hi : A <ₗ[i] B) (hj : A <ₗ[j] B) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact absurd ((hj.mem_iff hij).2 hi.mem) hi.notMem
  · rfl
  · exact absurd ((hi.mem_iff hji).2 hj.mem) hj.notMem

theorem LecticLT.trans (hAB : A <ₗ B) (hBC : B <ₗ C) : A <ₗ C :=
  let ⟨_, hi⟩ := hAB
  let ⟨_, hj⟩ := hBC
  (hi.trans hj).lecticLT

theorem lecticLT_irrefl (A : Finset β) : ¬A <ₗ A :=
  fun ⟨_, hi⟩ => hi.notMem hi.mem

theorem LecticLT.ne (h : A <ₗ B) : A ≠ B := by
  rintro rfl
  exact lecticLT_irrefl A h

theorem LecticLT.asymm (hAB : A <ₗ B) : ¬B <ₗ A :=
  fun hBA => lecticLT_irrefl A (hAB.trans hBA)

/-- Two distinct sets are lectically comparable at the smallest element in which they differ. -/
theorem exists_lecticLTAt_of_ne (h : A ≠ B) : ∃ i, A <ₗ[i] B ∨ B <ₗ[i] A := by
  have hne : (symmDiff A B).Nonempty := symmDiff_nonempty.2 h
  have hmin : ∀ j < (symmDiff A B).min' hne, j ∈ A ↔ j ∈ B := by
    intro j hj
    by_contra hcon
    have hjmem : j ∈ symmDiff A B := by
      rw [mem_symmDiff]
      tauto
    exact (min'_le _ j hjmem).not_gt hj
  rcases mem_symmDiff.1 (min'_mem _ hne) with hi | hi
  · exact ⟨_, Or.inr ⟨hi.1, hi.2, fun j hj => (hmin j hj).symm⟩⟩
  · exact ⟨_, Or.inl ⟨hi.1, hi.2, hmin⟩⟩

theorem lecticLT_trichotomy (A B : Finset β) : A <ₗ B ∨ A = B ∨ B <ₗ A := by
  by_cases h : A = B
  · exact Or.inr (Or.inl h)
  · obtain ⟨i, hi | hi⟩ := exists_lecticLTAt_of_ne h
    · exact Or.inl hi.lecticLT
    · exact Or.inr (Or.inr hi.lecticLT)

/-- The lectic order is a strict total order. -/
instance LecticLT.instIsStrictTotalOrder : IsStrictTotalOrder (Finset β) LecticLT where
  irrefl := lecticLT_irrefl
  trans _ _ _ := LecticLT.trans
  trichotomous A B hAB hBA := by
    rcases lecticLT_trichotomy A B with h | h | h
    · exact absurd h hAB
    · exact h
    · exact absurd h hBA

theorem not_lecticLT_of_subset (h : B ⊆ A) : ¬A <ₗ B :=
  fun ⟨_, hi⟩ => hi.notMem (h hi.mem)

/-- The lectic order extends proper inclusion. -/
theorem lecticLT_of_ssubset (h : A ⊂ B) : A <ₗ B := by
  rcases lecticLT_trichotomy A B with h' | h' | h'
  · exact h'
  · exact absurd h' h.ne
  · exact absurd h' (not_lecticLT_of_subset h.subset)

theorem eq_or_lecticLT_of_subset (h : A ⊆ B) : A = B ∨ A <ₗ B :=
  h.eq_or_ssubset.imp_right lecticLT_of_ssubset

/-- The full set is the lectically largest set. -/
theorem lecticLT_univ [Fintype β] (h : A ≠ univ) : A <ₗ univ :=
  lecticLT_of_ssubset (ssubset_univ_iff.2 h)

theorem not_univ_lecticLT [Fintype β] (A : Finset β) : ¬univ <ₗ A :=
  not_lecticLT_of_subset (subset_univ A)

/-- On a finite type there are no infinite lectically ascending chains. -/
theorem wellFounded_lecticGT [Finite β] : WellFounded (Function.swap (LecticLT (β := β))) := by
  cases nonempty_fintype β
  exact Finite.wellFounded_of_trans_of_irrefl _

/-! ### The operation `A ⊕ i` -/

variable (c : ClosureOperator (Finset β))

/-- The set `A ⊕ i = c ((A ∩ {j | j < i}) ∪ {i})` of Ganter's NextClosure algorithm. -/
def oplus (A : Finset β) (i : β) : Finset β :=
  c (insert i (A.filter (· < i)))

variable {c}

theorem mem_oplus_self (A : Finset β) (i : β) : i ∈ oplus c A i :=
  c.le_closure _ (mem_insert_self _ _)

theorem mem_oplus_of_mem_of_lt (hj : j ∈ A) (hji : j < i) : j ∈ oplus c A i :=
  c.le_closure _ (mem_insert_of_mem (mem_filter.2 ⟨hj, hji⟩))

theorem isClosed_oplus (A : Finset β) (i : β) : c.IsClosed (oplus c A i) :=
  c.isClosed_closure _

/-- If `A <ₗ[i] B` and `B` is closed, then `A ⊕ i ⊆ B`. -/
theorem LecticLTAt.oplus_subset (h : A <ₗ[i] B) (hB : c.IsClosed B) : oplus c A i ⊆ B := by
  refine ClosureOperator.closure_min (insert_subset h.mem fun j hj => ?_) hB
  obtain ⟨hjA, hji⟩ := mem_filter.1 hj
  exact (h.mem_iff hji).1 hjA

/-- If `A <ₗ[i] B` and `B` is closed, then `A <ₗ[i] A ⊕ i`. -/
theorem LecticLTAt.lecticLTAt_oplus (h : A <ₗ[i] B) (hB : c.IsClosed B) :
    A <ₗ[i] oplus c A i :=
  ⟨mem_oplus_self A i, h.notMem, fun _ hj =>
    ⟨fun hjA => mem_oplus_of_mem_of_lt hjA hj, fun hjO => (h.mem_iff hj).2 (h.oplus_subset hB hjO)⟩⟩

/-- If `A <ₗ[i] B` and `B` is closed, then `A ⊕ i` is lectically at most `B`. -/
theorem LecticLTAt.oplus_eq_or_lecticLT (h : A <ₗ[i] B) (hB : c.IsClosed B) :
    oplus c A i = B ∨ oplus c A i <ₗ B :=
  eq_or_lecticLT_of_subset (h.oplus_subset hB)

end FCA
