/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Algorithm.Lectic
public import FCA.Finite.Basic

/-!
# The NextClosure algorithm

Ganter's NextClosure algorithm enumerates the closed sets of a closure operator `c` on the subsets
of a finite linearly ordered type in lectic order. Given a set `A`, the lectically next closed set
is `A ⊕ i` for the largest `i` with `A <ₗ[i] A ⊕ i`.

## Main definitions

* `FCA.nextClosure`: `nextClosure c A` is the lectically smallest closed set that is lectically
  larger than `A`, or `none` if there is none.
* `FCA.closedFrom`: the closed sets found by iterating `nextClosure`, starting from a given set.
* `FCA.allClosed`: the list of all closed sets of `c`, in lectic order.
* `FCA.intentClosureOperatorFinset`: the intent closure of a finite context as a closure operator
  on finsets.
* `FCA.intentsList`, `FCA.conceptsList`: the intents and concepts of a finite formal context,
  computed by NextClosure.

## Main results

* `FCA.nextClosure_eq_some_iff`: correctness of `nextClosure`.
* `FCA.nextClosure_eq_none_iff`: `nextClosure c A = none` iff `A` is the full set.
* `FCA.mem_allClosed`, `FCA.pairwise_allClosed`: `allClosed c` lists exactly the closed sets of
  `c`, in strictly increasing lectic order.
* `FCA.mem_intentsList`: `intentsList r` lists exactly the intents of `r`.

## Implementation notes

The recursion of `FCA.closedFrom` terminates since the number of sets lectically larger than the
current one decreases. No fuel is needed.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [B. Ganter, *Two basic algorithms in concept analysis*][ganter1984]
-/

@[expose] public section

open Finset Order

namespace FCA

section NextClosure

variable {β : Type*} [Fintype β] [LinearOrder β] (c : ClosureOperator (Finset β))
  {A B C : Finset β}

/-- `nextClosure c A` is the lectically next closed set of the closure operator `c` after `A`:
the set `A ⊕ i` for the largest `i` such that `A <ₗ[i] A ⊕ i`. It is `none` if no such `i`
exists, which is the case iff `A` is the full set. -/
def nextClosure (A : Finset β) : Option (Finset β) :=
  if h : (univ.filter fun i => A <ₗ[i] oplus c A i).Nonempty then
    some (oplus c A ((univ.filter fun i => A <ₗ[i] oplus c A i).max' h))
  else none

variable {c}

theorem exists_lecticLTAt_of_nextClosure_eq_some (h : nextClosure c A = some B) :
    ∃ i, B = oplus c A i ∧ A <ₗ[i] B := by
  unfold nextClosure at h
  split at h
  · next hne =>
    obtain rfl := Option.some.inj h
    exact ⟨_, rfl, (mem_filter.1 (max'_mem _ hne)).2⟩
  · cases h

/-- The result of `nextClosure` is closed. -/
theorem isClosed_of_nextClosure_eq_some (h : nextClosure c A = some B) : c.IsClosed B := by
  obtain ⟨i, rfl, -⟩ := exists_lecticLTAt_of_nextClosure_eq_some h
  exact isClosed_oplus A i

/-- The result of `nextClosure` is lectically larger than its argument. -/
theorem lecticLT_of_nextClosure_eq_some (h : nextClosure c A = some B) : A <ₗ B := by
  obtain ⟨i, -, hi⟩ := exists_lecticLTAt_of_nextClosure_eq_some h
  exact hi.lecticLT

/-- If there is a closed set `C` lectically larger than `A`, then `nextClosure c A` returns a set
which is lectically at most `C`. -/
theorem exists_nextClosure_eq_some (hC : c.IsClosed C) (hAC : A <ₗ C) :
    ∃ B, nextClosure c A = some B ∧ (B = C ∨ B <ₗ C) := by
  obtain ⟨i, hi⟩ := hAC
  have hiS : i ∈ univ.filter fun i => A <ₗ[i] oplus c A i :=
    mem_filter.2 ⟨mem_univ i, hi.lecticLTAt_oplus hC⟩
  have hne : (univ.filter fun i => A <ₗ[i] oplus c A i).Nonempty := ⟨i, hiS⟩
  refine ⟨_, dite_eq_left hne, ?_⟩
  have hm := (mem_filter.1 (max'_mem _ hne)).2
  rcases (le_max' _ i hiS).lt_or_eq with hlt | heq
  · exact Or.inr (hi.of_lt hm hlt).lecticLT
  · rw [← heq]
    exact hi.oplus_eq_or_lecticLT hC

/-- No closed set lies lectically strictly between `A` and `nextClosure c A`. -/
theorem not_lecticLT_of_nextClosure_eq_some (h : nextClosure c A = some B) (hC : c.IsClosed C)
    (hAC : A <ₗ C) : ¬C <ₗ B := by
  obtain ⟨B', hB', hle⟩ := exists_nextClosure_eq_some hC hAC
  obtain rfl := Option.some.inj (h.symm.trans hB')
  rcases hle with rfl | hlt
  · exact lecticLT_irrefl _
  · exact hlt.asymm

/-- **Correctness of NextClosure**: `nextClosure c A = some B` iff `B` is the lectically smallest
closed set which is lectically larger than `A`. -/
theorem nextClosure_eq_some_iff :
    nextClosure c A = some B ↔
      c.IsClosed B ∧ A <ₗ B ∧ ∀ C, c.IsClosed C → A <ₗ C → ¬C <ₗ B := by
  refine ⟨fun h => ⟨isClosed_of_nextClosure_eq_some h, lecticLT_of_nextClosure_eq_some h,
    fun C => not_lecticLT_of_nextClosure_eq_some h⟩, fun ⟨hB, hAB, hmin⟩ => ?_⟩
  obtain ⟨B', hB', rfl | hlt⟩ := exists_nextClosure_eq_some hB hAB
  · exact hB'
  · exact absurd hlt (hmin B' (isClosed_of_nextClosure_eq_some hB')
      (lecticLT_of_nextClosure_eq_some hB'))

/-- `nextClosure` returns `none` iff there is no lectically larger closed set. -/
theorem nextClosure_eq_none_iff_forall :
    nextClosure c A = none ↔ ∀ C, c.IsClosed C → ¬A <ₗ C := by
  refine ⟨fun h C hC hAC => ?_, fun h => ?_⟩
  · obtain ⟨B, hB, -⟩ := exists_nextClosure_eq_some hC hAC
    cases h.symm.trans hB
  · by_contra hne
    obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.1 hne
    exact h B (isClosed_of_nextClosure_eq_some hB) (lecticLT_of_nextClosure_eq_some hB)

/-- `nextClosure` returns `none` exactly at the full set, the lectically largest closed set. -/
theorem nextClosure_eq_none_iff : nextClosure c A = none ↔ A = univ := by
  rw [nextClosure_eq_none_iff_forall]
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hne
    exact h univ c.isClosed_top (lecticLT_univ hne)
  · rintro rfl C -
    exact not_univ_lecticLT C

end NextClosure

section AllClosed

/-- The list of closed sets obtained by iterating `nextClosure`, starting from (and including)
the set `A`. -/
def closedFrom {β : Type*} [Fintype β] [LinearOrder β] (c : ClosureOperator (Finset β))
    (A : Finset β) : List (Finset β) :=
  A :: match _h : nextClosure c A with
    | none => []
    | some B => closedFrom c B
termination_by (univ.filter fun C => A <ₗ C).card
decreasing_by
  have hAB : A <ₗ B := lecticLT_of_nextClosure_eq_some ‹_›
  refine card_lt_card ((ssubset_iff_of_subset fun C hC => ?_).2 ⟨B, ?_, ?_⟩)
  · exact mem_filter.2 ⟨mem_univ C, hAB.trans (mem_filter.1 hC).2⟩
  · exact mem_filter.2 ⟨mem_univ B, hAB⟩
  · exact fun hB => lecticLT_irrefl B (mem_filter.1 hB).2

variable {β : Type*} [Fintype β] [LinearOrder β] {c : ClosureOperator (Finset β)}
  {A B : Finset β}

theorem closedFrom_of_eq_none (h : nextClosure c A = none) : closedFrom c A = [A] := by
  rw [closedFrom]
  split <;> simp_all

theorem closedFrom_of_eq_some (h : nextClosure c A = some B) :
    closedFrom c A = A :: closedFrom c B := by
  rw [closedFrom]
  split <;> simp_all

/-- `closedFrom c A` consists of `A` and all closed sets lectically larger than `A`. -/
theorem mem_closedFrom : B ∈ closedFrom c A ↔ B = A ∨ c.IsClosed B ∧ A <ₗ B := by
  induction A using (wellFounded_lecticGT (β := β)).induction with
  | _ A ih =>
    cases h : nextClosure c A with
    | none =>
      rw [closedFrom_of_eq_none h, List.mem_singleton]
      exact ⟨Or.inl, fun h' => h'.elim id fun h' =>
        absurd h'.2 (nextClosure_eq_none_iff_forall.1 h B h'.1)⟩
    | some N =>
      have hN := isClosed_of_nextClosure_eq_some h
      have hAN := lecticLT_of_nextClosure_eq_some h
      rw [closedFrom_of_eq_some h, List.mem_cons, ih N hAN]
      refine or_congr_right ⟨?_, fun ⟨hB, hAB⟩ => ?_⟩
      · rintro (rfl | ⟨hB, hNB⟩)
        · exact ⟨hN, hAN⟩
        · exact ⟨hB, hAN.trans hNB⟩
      · rcases lecticLT_trichotomy N B with h' | h' | h'
        · exact Or.inr ⟨hB, h'⟩
        · exact Or.inl h'.symm
        · exact absurd h' (not_lecticLT_of_nextClosure_eq_some h hB hAB)

/-- `closedFrom c A` is strictly increasing in the lectic order. -/
theorem pairwise_closedFrom (c : ClosureOperator (Finset β)) (A : Finset β) :
    (closedFrom c A).Pairwise LecticLT := by
  induction A using (wellFounded_lecticGT (β := β)).induction with
  | _ A ih =>
    cases h : nextClosure c A with
    | none =>
      rw [closedFrom_of_eq_none h]
      exact List.pairwise_singleton _ _
    | some N =>
      have hAN := lecticLT_of_nextClosure_eq_some h
      rw [closedFrom_of_eq_some h, List.pairwise_cons]
      refine ⟨fun B hB => ?_, ih N hAN⟩
      rcases mem_closedFrom.1 hB with rfl | ⟨-, hNB⟩
      · exact hAN
      · exact hAN.trans hNB

/-- The list of all closed sets of the closure operator `c`, in lectic order, computed by
iterating `nextClosure` starting from the closure of the empty set. -/
def allClosed (c : ClosureOperator (Finset β)) : List (Finset β) :=
  closedFrom c (c ∅)

/-- `allClosed c` contains exactly the closed sets of `c`. -/
@[simp]
theorem mem_allClosed : A ∈ allClosed c ↔ c.IsClosed A := by
  rw [allClosed, mem_closedFrom]
  refine ⟨?_, fun hA => ?_⟩
  · rintro (rfl | ⟨hA, -⟩)
    · exact c.isClosed_closure ∅
    · exact hA
  · have hsub : c ∅ ⊆ A := ClosureOperator.closure_min (empty_subset A) hA
    exact (eq_or_lecticLT_of_subset hsub).imp Eq.symm fun h => ⟨hA, h⟩

/-- `allClosed c` is strictly increasing in the lectic order. -/
theorem pairwise_allClosed (c : ClosureOperator (Finset β)) :
    (allClosed c).Pairwise LecticLT :=
  pairwise_closedFrom c _

theorem nodup_allClosed (c : ClosureOperator (Finset β)) : (allClosed c).Nodup :=
  (pairwise_allClosed c).imp LecticLT.ne

theorem toFinset_allClosed (c : ClosureOperator (Finset β)) :
    (allClosed c).toFinset = univ.filter fun A => c A = A := by
  ext A
  simp only [List.mem_toFinset, mem_allClosed, mem_filter, mem_univ, true_and]
  exact c.isClosed_iff

end AllClosed

/-! ### Intents and concepts of a finite context -/

section Context

variable {α β : Type*} (r : α → β → Prop) [DecidableRel r] [Fintype α] [Fintype β]

/-- The intent closure `t ↦ t''` of a finite formal context, as a closure operator on finsets
of attributes. -/
def intentClosureOperatorFinset : ClosureOperator (Finset β) where
  toFun := intentClosureFinset r
  monotone' s t hst b := by
    simp only [intentClosureFinset, mem_upperPolarFinset, mem_lowerPolarFinset]
    exact fun h a ha => h a fun b hb => ha b (hst hb)
  le_closure' s b hb := by
    simp only [intentClosureFinset, mem_upperPolarFinset, mem_lowerPolarFinset]
    exact fun a ha => ha b hb
  idempotent' s := by
    ext b
    simp only [intentClosureFinset, mem_upperPolarFinset, mem_lowerPolarFinset]
    exact ⟨fun h a ha => h a fun b hb => hb a ha, fun h a ha => ha b h⟩

@[simp]
theorem intentClosureOperatorFinset_apply (t : Finset β) :
    intentClosureOperatorFinset r t = intentClosureFinset r t :=
  rfl

variable {r} in
theorem isClosed_intentClosureOperatorFinset_iff {t : Finset β} :
    (intentClosureOperatorFinset r).IsClosed t ↔ IsIntent r (t : Set β) := by
  rw [ClosureOperator.isClosed_iff, isIntent_iff, ← coe_intentClosureFinset, coe_inj]
  rfl

variable [LinearOrder β]

/-- The list of all intents of a finite formal context with linearly ordered attributes, in
lectic order, computed by the NextClosure algorithm. -/
def intentsList : List (Finset β) :=
  allClosed (intentClosureOperatorFinset r)

variable {r} in
/-- `intentsList r` contains exactly the intents of `r`. -/
@[simp]
theorem mem_intentsList {t : Finset β} : t ∈ intentsList r ↔ IsIntent r (t : Set β) :=
  mem_allClosed.trans isClosed_intentClosureOperatorFinset_iff

theorem pairwise_intentsList : (intentsList r).Pairwise LecticLT :=
  pairwise_allClosed _

theorem nodup_intentsList : (intentsList r).Nodup :=
  nodup_allClosed _

theorem toFinset_intentsList : (intentsList r).toFinset = intents r := by
  ext t
  rw [List.mem_toFinset, mem_intentsList, mem_intents]

theorem length_intentsList : (intentsList r).length = (intents r).card := by
  rw [← toFinset_intentsList, List.toFinset_card_of_nodup (nodup_intentsList r)]

/-- The list of all concepts of a finite formal context, as pairs `(extent, intent)`, computed by
the NextClosure algorithm. -/
def conceptsList : List (Finset α × Finset β) :=
  (intentsList r).map fun t => (lowerPolarFinset r t, t)

theorem toFinset_conceptsList [DecidableEq α] : (conceptsList r).toFinset = concepts r := by
  ext p
  simp only [conceptsList, concepts, List.mem_toFinset, List.mem_map, mem_image,
    ← toFinset_intentsList]

theorem nodup_conceptsList : (conceptsList r).Nodup :=
  (nodup_intentsList r).map (fun _ _ h => congrArg Prod.snd h)

end Context

end FCA
