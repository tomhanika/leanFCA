/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Closure

/-!
# Computing the closure under a finite list of implications

This file provides an executable closure of a finset of attributes under a finite list of
implications, given as pairs `(premise, conclusion)` of finsets, by naive fixpoint iteration.

The iteration is parametrised by a relation `R` deciding when an implication *fires*: the
implication `(p, q)` adds `q` to the current set `s` whenever `R p s`. For `R = (· ⊆ ·)` this
yields the usual closure `FCA.Implication.closure`; for `R = (· ⊂ ·)` it yields the operator
`L•` used in the computation of the canonical base.

## Main definitions

* `FCA.Implication.closeStep`: one round of applying all implications that fire.
* `FCA.Implication.closeWith`: the fixpoint iteration. It runs at most as many rounds as there
  are implications.
* `FCA.Implication.closeOperator`: `closeWith` as a closure operator on finsets.
* `FCA.Implication.closureFinset`: the closure of a finset under a list of implications.
* `FCA.Implication.ofList`: the set of implications given by a list of pairs of finsets.

## Main results

* `FCA.Implication.closeWith_eq_self_iff`, `FCA.Implication.closeWith_subset`: `closeWith R L s`
  is the smallest superset of `s` respecting all implications of `L` (in the sense of `R`).
* `FCA.Implication.coe_closureFinset`: `closureFinset` computes `FCA.Implication.closure`.
-/

@[expose] public section

open Finset

namespace FCA

namespace Implication

variable {β : Type*} [DecidableEq β]

section CloseWith

variable (R : Finset β → Finset β → Prop) [DecidableRel R] (L : List (Finset β × Finset β))
  {s t : Finset β} {x : β}

/-- One round of the fixpoint iteration: add to `s` the conclusions of all implications in `L`
whose premise `p` fires, i.e. satisfies `R p s`. -/
def closeStep (s : Finset β) : Finset β :=
  L.foldr (fun p acc => if R p.1 s then p.2 ∪ acc else acc) s

variable {R L}

theorem mem_closeStep : x ∈ closeStep R L s ↔ x ∈ s ∨ ∃ p ∈ L, R p.1 s ∧ x ∈ p.2 := by
  induction L with
  | nil => simp [closeStep]
  | cons p L ih =>
    have h : closeStep R (p :: L) s = if R p.1 s then p.2 ∪ closeStep R L s else closeStep R L s :=
      rfl
    rw [h]
    split_ifs with hp
    · rw [mem_union, ih]
      simp only [List.mem_cons, exists_eq_or_imp, hp, true_and]
      tauto
    · rw [ih]
      simp only [List.mem_cons, exists_eq_or_imp, hp, false_and, false_or]

variable (R L) in
theorem subset_closeStep (s : Finset β) : s ⊆ closeStep R L s :=
  fun _ hx => mem_closeStep.2 (Or.inl hx)

theorem subset_closeStep_of_mem {p : Finset β × Finset β} (hp : p ∈ L) (hR : R p.1 s) :
    p.2 ⊆ closeStep R L s :=
  fun _ hx => mem_closeStep.2 (Or.inr ⟨p, hp, hR, hx⟩)

theorem closeStep_eq_self_iff : closeStep R L s = s ↔ ∀ p ∈ L, R p.1 s → p.2 ⊆ s := by
  refine ⟨fun h p hp hR => ?_, fun h => (subset_closeStep R L s).antisymm' fun x hx => ?_⟩
  · have := subset_closeStep_of_mem hp hR
    rwa [h] at this
  · rcases mem_closeStep.1 hx with hx | ⟨p, hp, hR, hx⟩
    · exact hx
    · exact h p hp hR hx

variable (R L) in
/-- The fixpoint iteration with fuel: apply `closeStep` until a fixpoint is reached, but at most
`n` times. -/
def closeIter : ℕ → Finset β → Finset β
  | 0, s => s
  | n + 1, s => if closeStep R L s = s then s else closeIter n (closeStep R L s)

variable (R L) in
theorem subset_closeIter (n : ℕ) (s : Finset β) : s ⊆ closeIter R L n s := by
  induction n generalizing s with
  | zero => exact Subset.rfl
  | succ n ih =>
    rw [closeIter]
    split_ifs
    · exact Subset.rfl
    · exact (subset_closeStep R L s).trans (ih _)

theorem closeIter_subset (hR : ∀ p s t, R p s → s ⊆ t → R p t)
    (ht : ∀ p ∈ L, R p.1 t → p.2 ⊆ t) (n : ℕ) (hst : s ⊆ t) : closeIter R L n s ⊆ t := by
  induction n generalizing s with
  | zero => exact hst
  | succ n ih =>
    rw [closeIter]
    split_ifs
    · exact hst
    · refine ih fun x hx => ?_
      rcases mem_closeStep.1 hx with hx | ⟨p, hp, hps, hx⟩
      · exact hst hx
      · exact ht p hp (hR _ _ _ hps hst) hx

/-- Each round of the iteration that is not a fixpoint satisfies a new conclusion, so the
iteration stabilises once the fuel exceeds the number of unsatisfied conclusions. -/
theorem closeIter_respects (n : ℕ) (hn : (L.toFinset.filter fun p => ¬p.2 ⊆ s).card ≤ n) :
    ∀ p ∈ L, R p.1 (closeIter R L n s) → p.2 ⊆ closeIter R L n s := by
  induction n generalizing s with
  | zero =>
    intro p hp _
    by_contra hps
    exact notMem_empty p (card_eq_zero.1 (Nat.le_zero.1 hn) ▸
      mem_filter.2 ⟨List.mem_toFinset.2 hp, hps⟩)
  | succ n ih =>
    rw [closeIter]
    split_ifs with hfix
    · exact closeStep_eq_self_iff.1 hfix
    · refine ih (Nat.le_of_lt_succ (lt_of_lt_of_le (card_lt_card ?_) hn))
      obtain ⟨p, hp, hR, hps⟩ : ∃ p ∈ L, R p.1 s ∧ ¬p.2 ⊆ s := by
        by_contra hcon
        exact hfix (closeStep_eq_self_iff.2 fun p hp hR => by_contra fun h => hcon ⟨p, hp, hR, h⟩)
      refine (ssubset_iff_of_subset fun q hq => ?_).2 ⟨p, ?_, ?_⟩
      · exact mem_filter.2 ⟨(mem_filter.1 hq).1, fun hqs =>
          (mem_filter.1 hq).2 (hqs.trans (subset_closeStep R L s))⟩
      · exact mem_filter.2 ⟨List.mem_toFinset.2 hp, hps⟩
      · exact fun hmem => (mem_filter.1 hmem).2 (subset_closeStep_of_mem hp hR)

variable (R L) in
/-- The closure of `s` under the implications of `L`, where an implication `(p, q)` fires on a
set `s` if `R p s`: the smallest superset `t` of `s` with `q ⊆ t` whenever `R p t`. It is
computed by iterating `closeStep` until a fixpoint is reached, which takes at most `L.length`
rounds. -/
def closeWith (s : Finset β) : Finset β :=
  closeIter R L L.length s

variable (R L) in
theorem subset_closeWith (s : Finset β) : s ⊆ closeWith R L s :=
  subset_closeIter R L _ s

variable (R L) in
theorem closeWith_respects (s : Finset β) :
    ∀ p ∈ L, R p.1 (closeWith R L s) → p.2 ⊆ closeWith R L s :=
  closeIter_respects _ ((card_filter_le _ _).trans (List.toFinset_card_le L))

theorem closeWith_subset (hR : ∀ p s t, R p s → s ⊆ t → R p t)
    (ht : ∀ p ∈ L, R p.1 t → p.2 ⊆ t) (hst : s ⊆ t) : closeWith R L s ⊆ t :=
  closeIter_subset hR ht _ hst

theorem closeWith_eq_self_iff : closeWith R L s = s ↔ ∀ p ∈ L, R p.1 s → p.2 ⊆ s := by
  refine ⟨fun h => h ▸ closeWith_respects R L s, fun h => ?_⟩
  have hfix := closeStep_eq_self_iff.2 h
  rw [closeWith]
  cases L.length with
  | zero => rfl
  | succ n => rw [closeIter, ite_eq_left hfix]

variable (R L) in
/-- `closeWith R L` as a closure operator on finsets, provided that firing is monotone in the
set. Its closed sets are the sets `s` with `q ⊆ s` for all `(p, q) ∈ L` with `R p s`. -/
def closeOperator (hR : ∀ p s t, R p s → s ⊆ t → R p t) : ClosureOperator (Finset β) where
  toFun := closeWith R L
  monotone' _ t hst :=
    closeWith_subset hR (closeWith_respects R L t) (hst.trans (subset_closeWith R L t))
  le_closure' := subset_closeWith R L
  idempotent' s := closeWith_eq_self_iff.2 (closeWith_respects R L s)
  IsClosed s := ∀ p ∈ L, R p.1 s → p.2 ⊆ s
  isClosed_iff := closeWith_eq_self_iff.symm

@[simp]
theorem closeOperator_apply (hR : ∀ p s t, R p s → s ⊆ t → R p t) (s : Finset β) :
    closeOperator R L hR s = closeWith R L s :=
  rfl

theorem isClosed_closeOperator_iff (hR : ∀ p s t, R p s → s ⊆ t → R p t) :
    (closeOperator R L hR).IsClosed s ↔ ∀ p ∈ L, R p.1 s → p.2 ⊆ s :=
  Iff.rfl

end CloseWith

/-! ### The closure under a list of implications -/

variable {L : List (Finset β × Finset β)} {s : Finset β}

/-- The set of implications given by a list of pairs `(premise, conclusion)` of finsets. -/
def ofList (L : List (Finset β × Finset β)) : Set (Implication β) :=
  {i | ∃ p ∈ L, i = ⟨p.1, p.2⟩}

omit [DecidableEq β] in
theorem mem_ofList {i : Implication β} : i ∈ ofList L ↔ ∃ p ∈ L, i = ⟨p.1, p.2⟩ :=
  Iff.rfl

omit [DecidableEq β] in
theorem isModel_ofList_iff {t : Set β} :
    IsModel (ofList L) t ↔ ∀ p ∈ L, (p.1 : Set β) ⊆ t → (p.2 : Set β) ⊆ t :=
  ⟨fun h p hp => h _ ⟨p, hp, rfl⟩, by
    rintro h _ ⟨p, hp, rfl⟩
    exact h p hp⟩

omit [DecidableEq β] in
theorem isModel_ofList_coe_iff :
    IsModel (ofList L) (s : Set β) ↔ ∀ p ∈ L, p.1 ⊆ s → p.2 ⊆ s := by
  simp only [isModel_ofList_iff, coe_subset]

/-- The closure of the finset `s` under the list `L` of implications, computed by naive fixpoint
iteration. -/
def closureFinset (L : List (Finset β × Finset β)) (s : Finset β) : Finset β :=
  closeWith (· ⊆ ·) L s

variable (L) in
theorem subset_closureFinset (s : Finset β) : s ⊆ closureFinset L s :=
  subset_closeWith _ L s

variable (L) in
theorem isModel_closureFinset (s : Finset β) :
    IsModel (ofList L) (closureFinset L s : Set β) :=
  isModel_ofList_coe_iff.2 (closeWith_respects _ L s)

theorem closureFinset_eq_self_iff : closureFinset L s = s ↔ IsModel (ofList L) (s : Set β) :=
  closeWith_eq_self_iff.trans isModel_ofList_coe_iff.symm

/-- `closureFinset` computes the closure operator `FCA.Implication.closure`. -/
@[simp]
theorem coe_closureFinset (L : List (Finset β × Finset β)) (s : Finset β) :
    (closureFinset L s : Set β) = closure (ofList L) (s : Set β) := by
  classical
  refine Set.Subset.antisymm ?_ ((isModel_closureFinset L s).closure_subset
    (coe_subset.2 (subset_closureFinset L s)))
  have hmodel := isModel_closure (ofList L) (s : Set β)
  have hsub : closureFinset L s ⊆
      (closureFinset L s).filter (· ∈ closure (ofList L) (s : Set β)) := by
    refine closeWith_subset (fun _ _ _ h h' => h.trans h') (fun p hp hpt x hx => ?_)
      fun x hx => mem_filter.2 ⟨subset_closureFinset L s hx, subset_closure _ _ (mem_coe.2 hx)⟩
    refine mem_filter.2 ⟨closeWith_respects _ L s p hp (hpt.trans (filter_subset _ _)) hx, ?_⟩
    exact isModel_ofList_iff.1 hmodel p hp (fun y hy => (mem_filter.1 (hpt hy)).2) hx
  exact fun x hx => (mem_filter.1 (hsub hx)).2

/-- The closure under a list of implications as a closure operator on finsets. -/
def closureOperatorFinset (L : List (Finset β × Finset β)) : ClosureOperator (Finset β) :=
  closeOperator (· ⊆ ·) L fun _ _ _ h h' => h.trans h'

@[simp]
theorem closureOperatorFinset_apply (L : List (Finset β × Finset β)) (s : Finset β) :
    closureOperatorFinset L s = closureFinset L s :=
  rfl

theorem isClosed_closureOperatorFinset_iff :
    (closureOperatorFinset L).IsClosed s ↔ IsModel (ofList L) (s : Set β) :=
  isModel_ofList_coe_iff.symm

end Implication

end FCA
