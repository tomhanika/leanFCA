/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Algorithm.ImplicationClosure
public import FCA.Algorithm.NextClosure
public import FCA.Implication.CanonicalBase

/-!
# Computing the canonical base

This file implements Ganter's algorithm for the canonical base of a finite formal context
`r : α → β → Prop` with linearly ordered attributes, and proves it correct.

The intents and pseudo-intents together form a closure system. Its closure operator is `L•` for
the canonical base `L`, where `L•` saturates a set `s` under the rule "add `q` whenever
`(p, q) ∈ L` and `p ⊂ s`". The algorithm walks through this closure system in lectic order using
NextClosure, collecting the pseudo-intents on the way. This is possible although `L` is only being
computed, because the lectically next closed set only depends on the pseudo-intents found so far.

## Main definitions

* `FCA.pseudoClosureOperator`: the closure operator `L•` of a list `L` of implications.
* `FCA.canonicalBaseList`: the canonical base of a finite context, as a list of pairs
  `(pseudo-intent, its intent closure)`, ordered lectically by premise.
* `FCA.pseudoIntentsList`: the list of pseudo-intents of a finite context, in lectic order.

## Main results

* `FCA.mem_canonicalBaseList`, `FCA.ofList_canonicalBaseList`: `canonicalBaseList r` is the
  canonical base `FCA.canonicalBase r`.
* `FCA.mem_pseudoIntentsList`: `pseudoIntentsList r` lists exactly the pseudo-intents.
* `FCA.decidableIsPseudoIntent`: being a pseudo-intent is decidable.
* `FCA.closureFinset_canonicalBaseList`: the implication closure of the computed base is the
  intent closure.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [B. Ganter, *Two basic algorithms in concept analysis*][ganter1984]
-/

@[expose] public section

open Finset Order

namespace FCA

section PseudoClosure

variable {β : Type*} [DecidableEq β] {L : List (Finset β × Finset β)} {s : Finset β}

/-- The closure operator `L•` of a list of implications: the smallest superset `t` of `s` such
that `q ⊆ t` for all `(p, q) ∈ L` with `p ⊂ t`. -/
def pseudoClosureOperator (L : List (Finset β × Finset β)) : ClosureOperator (Finset β) :=
  Implication.closeOperator (· ⊂ ·) L fun _ _ _ h h' => h.trans_subset h'

theorem isClosed_pseudoClosureOperator_iff :
    (pseudoClosureOperator L).IsClosed s ↔ ∀ p ∈ L, p.1 ⊂ s → p.2 ⊆ s :=
  Iff.rfl

end PseudoClosure

variable {α β : Type*} (r : α → β → Prop) [DecidableRel r] [Fintype α] [Fintype β]

/-! ### Pseudo-intents as finsets -/

section IsPseudoClosedFinset

/-- A finset of attributes is *pseudo-closed* if it contains the intent closure of every
pseudo-intent properly contained in it. The pseudo-closed sets are the intents and the
pseudo-intents. -/
def IsPseudoClosedFinset (P : Finset β) : Prop :=
  ∀ Q : Finset β, Q ⊂ P → IsPseudoIntent r (Q : Set β) → intentClosureFinset r Q ⊆ P

variable {r} {P : Finset β}

theorem isIntent_coe_iff : IsIntent r (P : Set β) ↔ intentClosureFinset r P = P := by
  rw [isIntent_iff, ← coe_intentClosureFinset, coe_inj]

/-- A finset is a pseudo-intent iff it is pseudo-closed but not an intent. -/
theorem isPseudoIntent_coe_iff :
    IsPseudoIntent r (P : Set β) ↔ intentClosureFinset r P ≠ P ∧ IsPseudoClosedFinset r P := by
  rw [isPseudoIntent_iff, isIntent_coe_iff]
  refine and_congr_right fun _ => ⟨fun h Q hQP hQ => ?_, fun h q hqP hq => ?_⟩
  · have := h Q (coe_ssubset.2 hQP) hQ
    rwa [← coe_intentClosureFinset, coe_subset] at this
  · obtain ⟨Q, rfl⟩ := (Set.toFinite q).exists_finset_coe
    rw [← coe_intentClosureFinset, coe_subset]
    exact h Q (coe_ssubset.1 hqP) hq

theorem IsPseudoClosedFinset.of_isPseudoIntent (h : IsPseudoIntent r (P : Set β)) :
    IsPseudoClosedFinset r P :=
  (isPseudoIntent_coe_iff.1 h).2

theorem IsPseudoClosedFinset.of_intentClosureFinset_eq (h : intentClosureFinset r P = P) :
    IsPseudoClosedFinset r P := fun Q hQP _ => by
  rw [← h]
  exact (intentClosureOperatorFinset r).monotone hQP.subset

end IsPseudoClosedFinset

/-! ### Ganter's algorithm -/

variable [LinearOrder β]

/-- Add the implication `A → A''` to the list `L` unless `A` is an intent. -/
def addPseudoIntent (L : List (Finset β × Finset β)) (A : Finset β) :
    List (Finset β × Finset β) :=
  if intentClosureFinset r A = A then L else (A, intentClosureFinset r A) :: L

/-- The main loop of Ganter's algorithm for the canonical base. Here `A` is the current
pseudo-closed set and `L` contains the implications `P → P''` for all pseudo-intents `P`
lectically smaller than `A`, in lectically decreasing order. -/
def canonicalBaseFrom {α β : Type*} (r : α → β → Prop) [DecidableRel r] [Fintype α] [Fintype β]
    [LinearOrder β] (L : List (Finset β × Finset β)) (A : Finset β) :
    List (Finset β × Finset β) :=
  match _h : nextClosure (pseudoClosureOperator (addPseudoIntent r L A)) A with
  | none => addPseudoIntent r L A
  | some B => canonicalBaseFrom r (addPseudoIntent r L A) B
termination_by (univ.filter fun C => A <ₗ C).card
decreasing_by
  have hAB : A <ₗ B := lecticLT_of_nextClosure_eq_some ‹_›
  refine card_lt_card ((ssubset_iff_of_subset fun C hC => ?_).2 ⟨B, ?_, ?_⟩)
  · exact mem_filter.2 ⟨mem_univ C, hAB.trans (mem_filter.1 hC).2⟩
  · exact mem_filter.2 ⟨mem_univ B, hAB⟩
  · exact fun hB => lecticLT_irrefl B (mem_filter.1 hB).2

/-- The canonical base of a finite formal context, computed by Ganter's algorithm, as a list of
pairs `(P, P'')` for the pseudo-intents `P`, in lectic order. -/
def canonicalBaseList : List (Finset β × Finset β) :=
  (canonicalBaseFrom r [] ∅).reverse

/-- The pseudo-intents of a finite formal context, in lectic order. -/
def pseudoIntentsList : List (Finset β) :=
  (canonicalBaseList r).map Prod.fst

variable {r} {L : List (Finset β × Finset β)} {A B : Finset β} {p : Finset β × Finset β}

theorem canonicalBaseFrom_of_eq_none
    (h : nextClosure (pseudoClosureOperator (addPseudoIntent r L A)) A = none) :
    canonicalBaseFrom r L A = addPseudoIntent r L A := by
  rw [canonicalBaseFrom]
  split <;> simp_all

theorem canonicalBaseFrom_of_eq_some
    (h : nextClosure (pseudoClosureOperator (addPseudoIntent r L A)) A = some B) :
    canonicalBaseFrom r L A = canonicalBaseFrom r (addPseudoIntent r L A) B := by
  rw [canonicalBaseFrom]
  split <;> simp_all

/-- If `L` consists of the implications of all pseudo-intents lectically smaller than the
pseudo-closed set `A`, then `addPseudoIntent r L A` consists of those of all pseudo-intents
lectically smaller than or equal to `A`. -/
theorem mem_addPseudoIntent (hA : IsPseudoClosedFinset r A)
    (hL : ∀ p, p ∈ L ↔
      IsPseudoIntent r (p.1 : Set β) ∧ p.2 = intentClosureFinset r p.1 ∧ p.1 <ₗ A) :
    p ∈ addPseudoIntent r L A ↔
      IsPseudoIntent r (p.1 : Set β) ∧ p.2 = intentClosureFinset r p.1 ∧
        (p.1 <ₗ A ∨ p.1 = A) := by
  rw [addPseudoIntent]
  split_ifs with hint
  · rw [hL]
    refine and_congr_right fun hp => and_congr_right fun _ => ⟨Or.inl, ?_⟩
    rintro (h | rfl)
    · exact h
    · exact absurd hint (isPseudoIntent_coe_iff.1 hp).1
  · rw [List.mem_cons, hL]
    constructor
    · rintro (rfl | ⟨h₁, h₂, h₃⟩)
      · exact ⟨isPseudoIntent_coe_iff.2 ⟨hint, hA⟩, rfl, Or.inr rfl⟩
      · exact ⟨h₁, h₂, Or.inl h₃⟩
    · rintro ⟨h₁, h₂, h₃ | h₃⟩
      · exact Or.inr ⟨h₁, h₂, h₃⟩
      · exact Or.inl (Prod.ext h₃ (h₂.trans (congrArg _ h₃)))

/-- The invariant of Ganter's algorithm yields its correctness. -/
theorem mem_canonicalBaseFrom (hA : IsPseudoClosedFinset r A)
    (hL : ∀ p, p ∈ L ↔
      IsPseudoIntent r (p.1 : Set β) ∧ p.2 = intentClosureFinset r p.1 ∧ p.1 <ₗ A) :
    p ∈ canonicalBaseFrom r L A ↔
      IsPseudoIntent r (p.1 : Set β) ∧ p.2 = intentClosureFinset r p.1 := by
  induction A using (wellFounded_lecticGT (β := β)).induction generalizing L with
  | _ A ih =>
    have hL' := fun p => mem_addPseudoIntent (p := p) hA hL
    -- every pseudo-closed set is closed with respect to the implications found so far
    have hclosed : ∀ S, IsPseudoClosedFinset r S →
        (pseudoClosureOperator (addPseudoIntent r L A)).IsClosed S := by
      intro S hS q hq hqS
      obtain ⟨hq₁, hq₂, -⟩ := (hL' q).1 hq
      rw [hq₂]
      exact hS q.1 hqS hq₁
    cases h : nextClosure (pseudoClosureOperator (addPseudoIntent r L A)) A with
    | none =>
      rw [canonicalBaseFrom_of_eq_none h, hL']
      obtain rfl := nextClosure_eq_none_iff.1 h
      refine and_congr_right fun _ => and_iff_left_of_imp fun _ => ?_
      by_cases hp : p.1 = univ
      · exact Or.inr hp
      · exact Or.inl (lecticLT_univ hp)
    | some N =>
      have hN := isClosed_of_nextClosure_eq_some h
      have hAN := lecticLT_of_nextClosure_eq_some h
      -- no pseudo-intent lies lectically strictly between `A` and `N`
      have hbetween : ∀ Q : Finset β, IsPseudoIntent r (Q : Set β) → Q <ₗ N →
          Q <ₗ A ∨ Q = A := by
        intro Q hQ hQN
        rcases lecticLT_trichotomy Q A with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exact absurd hQN (not_lecticLT_of_nextClosure_eq_some h
            (hclosed Q (.of_isPseudoIntent hQ)) h')
      rw [canonicalBaseFrom_of_eq_some h]
      refine ih N hAN (fun Q hQN hQ => ?_) fun q => ?_
      · have hmem : (Q, intentClosureFinset r Q) ∈ addPseudoIntent r L A :=
          (hL' _).2 ⟨hQ, rfl, hbetween Q hQ (lecticLT_of_ssubset hQN)⟩
        exact hN _ hmem hQN
      · rw [hL']
        refine and_congr_right fun hq => and_congr_right fun _ => ⟨?_, hbetween q.1 hq⟩
        rintro (h' | h')
        · exact h'.trans hAN
        · exact h' ▸ hAN

theorem pairwise_canonicalBaseFrom (hL : L.Pairwise fun p q => q.1 <ₗ p.1)
    (hA : ∀ p ∈ L, p.1 <ₗ A) : (canonicalBaseFrom r L A).Pairwise fun p q => q.1 <ₗ p.1 := by
  induction A using (wellFounded_lecticGT (β := β)).induction generalizing L with
  | _ A ih =>
    have hL' : (addPseudoIntent r L A).Pairwise (fun p q => q.1 <ₗ p.1) ∧
        ∀ p ∈ addPseudoIntent r L A, p.1 <ₗ A ∨ p.1 = A := by
      rw [addPseudoIntent]
      split_ifs
      · exact ⟨hL, fun p hp => Or.inl (hA p hp)⟩
      · refine ⟨List.pairwise_cons.2 ⟨hA, hL⟩, fun p hp => ?_⟩
        rcases List.mem_cons.1 hp with rfl | hp
        · exact Or.inr rfl
        · exact Or.inl (hA p hp)
    cases h : nextClosure (pseudoClosureOperator (addPseudoIntent r L A)) A with
    | none =>
      rw [canonicalBaseFrom_of_eq_none h]
      exact hL'.1
    | some N =>
      have hAN := lecticLT_of_nextClosure_eq_some h
      rw [canonicalBaseFrom_of_eq_some h]
      exact ih N hAN hL'.1 fun p hp => (hL'.2 p hp).elim (·.trans hAN) (· ▸ hAN)

/-- `canonicalBaseList r` consists of the implications `P → P''` for the pseudo-intents `P`. -/
theorem mem_canonicalBaseList :
    p ∈ canonicalBaseList r ↔
      IsPseudoIntent r (p.1 : Set β) ∧ p.2 = intentClosureFinset r p.1 := by
  rw [canonicalBaseList, List.mem_reverse]
  refine mem_canonicalBaseFrom (fun Q hQ => absurd hQ (not_ssubset_empty Q)) fun q => ?_
  simp [not_lecticLT_of_subset (empty_subset q.1)]

/-- The premises of `canonicalBaseList r` are strictly increasing in the lectic order. -/
theorem pairwise_canonicalBaseList (r : α → β → Prop) [DecidableRel r] :
    (canonicalBaseList r).Pairwise fun p q => p.1 <ₗ q.1 :=
  List.pairwise_reverse.2 (pairwise_canonicalBaseFrom List.Pairwise.nil (by simp))

theorem pairwise_pseudoIntentsList (r : α → β → Prop) [DecidableRel r] :
    (pseudoIntentsList r).Pairwise LecticLT :=
  List.pairwise_map.2 (pairwise_canonicalBaseList r)

theorem nodup_pseudoIntentsList (r : α → β → Prop) [DecidableRel r] :
    (pseudoIntentsList r).Nodup :=
  (pairwise_pseudoIntentsList r).imp LecticLT.ne

/-- **Correctness of Ganter's algorithm**: the computed list of implications is the canonical
base. -/
theorem ofList_canonicalBaseList (r : α → β → Prop) [DecidableRel r] :
    Implication.ofList (canonicalBaseList r) = canonicalBase r := by
  ext i
  rw [Implication.mem_ofList, mem_canonicalBase]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp₁, hp₂⟩ := mem_canonicalBaseList.1 hp
    exact ⟨hp₁, by rw [hp₂, coe_intentClosureFinset]⟩
  · rintro ⟨hi₁, hi₂⟩
    obtain ⟨P, hP⟩ := (Set.toFinite i.premise).exists_finset_coe
    refine ⟨(P, intentClosureFinset r P), mem_canonicalBaseList.2 ⟨by rwa [hP], rfl⟩, ?_⟩
    ext1
    · exact hP.symm
    · rw [hi₂, coe_intentClosureFinset, hP]

/-- `pseudoIntentsList r` contains exactly the pseudo-intents of `r`. -/
@[simp]
theorem mem_pseudoIntentsList {P : Finset β} :
    P ∈ pseudoIntentsList r ↔ IsPseudoIntent r (P : Set β) := by
  rw [pseudoIntentsList, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_canonicalBaseList.1 hp).1
  · exact fun h => ⟨(P, intentClosureFinset r P), mem_canonicalBaseList.2 ⟨h, rfl⟩, rfl⟩

/-- Being a pseudo-intent of a finite context with linearly ordered attributes is decidable. -/
instance decidableIsPseudoIntent {P : Finset β} : Decidable (IsPseudoIntent r (P : Set β)) :=
  decidable_of_iff _ mem_pseudoIntentsList

/-- The implication closure with respect to the computed canonical base is the intent closure. -/
theorem closureFinset_canonicalBaseList (r : α → β → Prop) [DecidableRel r] (s : Finset β) :
    Implication.closureFinset (canonicalBaseList r) s = intentClosureFinset r s := by
  rw [← coe_inj, Implication.coe_closureFinset, ofList_canonicalBaseList,
    Implication.closure_eq_intentClosure (isSound_canonicalBase r) (isComplete_canonicalBase r),
    coe_intentClosureFinset]
  rfl

end FCA
