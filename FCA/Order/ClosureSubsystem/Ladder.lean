/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Structure
public import Mathlib.Data.Fintype.EquivFin

/-!
# Ladders: when the lattice of closure subsystems is join-semidistributive

For a closure system `p`, a *ladder* is a pair of sequences `X`, `A` of closed sets such that
`X` is strictly increasing, `A n ∩ X (n + 1) = X n` for all `n`, and the intersection of all
`A n` is different from `X 0`. This file shows that the lattice `ClosureSubsystem p` is
join-semidistributive if and only if `p` has no ladder.

A ladder is an infinite strictly increasing sequence of closed sets, so there is none under the
ascending chain condition. There is also none if the closed sets form a chain. On the other
hand, the powerset of every infinite type has a ladder.

This characterisation is due to Adaricheva, who states it for the lattice of complete
subsemilattices of a complete semilattice: that lattice is semidistributive if and only if a
certain infinite semilattice, the ladder above, does not embed. The question of when the lattice
of closure systems is join-semidistributive was later raised again by Ronse.

## Main definitions

* `FCA.IsLadder p X A`: the sequences `X` and `A` of closed sets form a ladder.
* `FCA.IsLadder.rungs`: the closure system of `univ` and the sets `X n` with `n` in a given set
  of natural numbers.

## Main results

* `FCA.ClosureSubsystem.isJoinSemidistrib_iff_not_isLadder`: `ClosureSubsystem p` is
  join-semidistributive if and only if `p` has no ladder.
* `FCA.IsLadder.not_isNoetherianClosureSystem`: there is no ladder under the ascending chain
  condition.
* `FCA.IsLadder.not_total`: there is no ladder if the closed sets form a chain.
* `FCA.ClosureSubsystem.not_isJoinSemidistrib_of_infinite`: the lattice of all closure systems on
  an infinite type is not join-semidistributive.

## References

* [K. V. Adaricheva, *Semidistributive and coalgebraic lattices of
  subsemilattices*][adaricheva1988]
* [C. Ronse, *The poset of closure systems on an infinite poset: detachability and
  semimodularity*][ronse2010]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α : Type*} {p : Set α → Prop}

/-- A *ladder* of a closure system: sequences `X` and `A` of closed sets such that `X` is
strictly increasing, `A n ∩ X (n + 1) = X n`, and the intersection of all `A n` is not `X 0`. -/
structure IsLadder (p : Set α → Prop) (X A : ℕ → Set α) : Prop where
  /-- The sets `X n` are closed. -/
  isClosed_left : ∀ n, p (X n)
  /-- The sets `A n` are closed. -/
  isClosed_right : ∀ n, p (A n)
  /-- The sequence `X` is strictly increasing. -/
  ssubset_succ : ∀ n, X n ⊂ X (n + 1)
  /-- Each `X n` is cut out of `X (n + 1)` by `A n`. -/
  inter_succ : ∀ n, A n ∩ X (n + 1) = X n
  /-- The intersection of all `A n` is not `X 0`. -/
  iInter_ne : ⋂ n, A n ≠ X 0

namespace IsLadder

variable {X A : ℕ → Set α}

theorem strictMono (h : IsLadder p X A) : StrictMono X :=
  strictMono_nat_of_lt_succ h.ssubset_succ

theorem ne_univ (h : IsLadder p X A) (n : ℕ) : X n ≠ univ := fun heq ↦
  (h.ssubset_succ n).not_subset (heq ▸ subset_univ _)

theorem subset_right (h : IsLadder p X A) (n : ℕ) : X n ⊆ A n := by
  rw [← h.inter_succ n]
  exact inter_subset_left

theorem subset_iInter (h : IsLadder p X A) : X 0 ⊆ ⋂ n, A n :=
  Set.subset_iInter fun n ↦ (h.strictMono.monotone (Nat.zero_le n)).trans (h.subset_right n)

/-- There is no ladder under the ascending chain condition. -/
theorem not_isNoetherianClosureSystem (h : IsLadder p X A) : ¬IsNoetherianClosureSystem p :=
  fun hN ↦ by
    obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := hN.wf.has_min
      (range fun n ↦ (⟨X n, h.isClosed_left n⟩ : {A : Set α // p A})) (range_nonempty _)
    exact hmin _ ⟨n + 1, rfl⟩ (h.ssubset_succ n)

/-- There is no ladder if the closed sets form a chain. -/
theorem not_total (h : IsLadder p X A) : ¬∀ A B, p A → p B → A ⊆ B ∨ B ⊆ A := by
  intro htot
  have h0 : A 0 ⊆ X 0 := by
    rcases htot _ _ (h.isClosed_right 0) (h.isClosed_left 1) with hsub | hsub
    · rw [← h.inter_succ 0]
      exact subset_inter subset_rfl hsub
    · refine absurd ?_ (h.ssubset_succ 0).ne'
      rw [← h.inter_succ 0, inter_eq_right.2 hsub]
  exact h.iInter_ne (Subset.antisymm ((iInter_subset A 0).trans h0) h.subset_iInter)

variable [IsClosureSystem p]

/-- The closure system of `univ` and the sets `X n` of a ladder with `n ∈ E`. -/
def rungs (h : IsLadder p X A) (E : Set ℕ) : ClosureSubsystem p where
  carrier := {B | B = univ ∨ ∃ n ∈ E, B = X n}
  sInter_mem' S hS := by
    classical
    by_cases hex : ∃ n, X n ∈ S
    · have heq : ⋂₀ S = X (Nat.find hex) := by
        refine Subset.antisymm (sInter_subset_of_mem (Nat.find_spec hex))
          (subset_sInter fun B hB ↦ ?_)
        rcases hS hB with rfl | ⟨n, -, rfl⟩
        · exact subset_univ _
        · exact h.strictMono.monotone (Nat.find_min' hex hB)
      rw [heq]
      exact hS (Nat.find_spec hex)
    · refine .inl (sInter_eq_univ.2 fun B hB ↦ (hS hB).elim id ?_)
      rintro ⟨n, -, rfl⟩
      exact absurd ⟨n, hB⟩ hex
  isClosed' B hB := by
    rcases hB with rfl | ⟨n, -, rfl⟩
    · exact IsClosureSystem.univ_mem
    · exact h.isClosed_left n

theorem mem_rungs (h : IsLadder p X A) {E : Set ℕ} {B : Set α} :
    B ∈ h.rungs E ↔ B = univ ∨ ∃ n ∈ E, B = X n :=
  Iff.rfl

theorem mem_rungs_iff (h : IsLadder p X A) {E : Set ℕ} {n : ℕ} : X n ∈ h.rungs E ↔ n ∈ E := by
  refine ⟨fun hn ↦ ?_, fun hn ↦ .inr ⟨n, hn, rfl⟩⟩
  rcases hn with hn | ⟨m, hm, hnm⟩
  · exact absurd hn (h.ne_univ n)
  · exact h.strictMono.injective hnm ▸ hm

/-- For disjoint sets `E` and `E'`, the closure systems `rungs E` and `rungs E'` have only `univ`
in common. -/
theorem rungs_inf_rungs (h : IsLadder p X A) {E E' : Set ℕ} (hE : Disjoint E E') :
    h.rungs E ⊓ h.rungs E' = ⊥ := by
  refine eq_bot_iff.2 (ClosureSubsystem.le_def.2 fun B hB ↦ ClosureSubsystem.mem_bot.2 ?_)
  obtain ⟨h₁, h₂⟩ := ClosureSubsystem.mem_inf.1 hB
  rcases h₁ with rfl | ⟨n, hn, rfl⟩
  · rfl
  · exact absurd (h.mem_rungs_iff.1 h₂) (disjoint_left.1 hE hn)

/-- If the successor of every member of `E` lies in `E'`, then `rungs E` is contained in the join
of `rungs E'` with the closure system generated by the sets `A n`. -/
theorem rungs_le_sup (h : IsLadder p X A) {E E' : Set ℕ} (hE : ∀ n ∈ E, n + 1 ∈ E') :
    h.rungs E ≤ ClosureSubsystem.generate p (range A) ⊔ h.rungs E' := by
  refine ClosureSubsystem.le_def.2 fun B hB ↦ ?_
  rcases hB with rfl | ⟨n, hn, rfl⟩
  · exact ClosureSubsystem.univ_mem _
  · exact ClosureSubsystem.mem_sup.2 ⟨A n,
      ClosureSubsystem.generate_le_iff.1 le_rfl (A n) ⟨n, rfl⟩ (h.isClosed_right n),
      X (n + 1), .inr ⟨n + 1, hE n hn, rfl⟩, h.inter_succ n⟩

/-- The set `X 0` of a ladder is not an intersection of sets `A n`. -/
theorem notMem_generate (h : IsLadder p X A) : X 0 ∉ ClosureSubsystem.generate p (range A) := by
  intro hmem
  obtain ⟨T, hT, -, heq⟩ := ClosureSubsystem.mem_generate.1 hmem
  refine h.iInter_ne (Subset.antisymm ?_ h.subset_iInter)
  rw [← heq]
  refine subset_sInter fun B hB ↦ ?_
  obtain ⟨n, rfl⟩ := hT hB
  exact iInter_subset A n

/-- A closure system with a ladder has a lattice of closure subsystems which is not
join-semidistributive. -/
theorem not_isJoinSemidistrib (h : IsLadder p X A) :
    ¬IsJoinSemidistrib (ClosureSubsystem p) := by
  intro _
  have hE : Disjoint {n : ℕ | n % 2 = 0} {n : ℕ | n % 2 = 1} :=
    disjoint_left.2 fun n (h₀ : n % 2 = 0) (h₁ : n % 2 = 1) ↦ by omega
  have h₀₁ : h.rungs {n | n % 2 = 0} ≤
      ClosureSubsystem.generate p (range A) ⊔ h.rungs {n | n % 2 = 1} :=
    h.rungs_le_sup fun n (hn : n % 2 = 0) ↦ show (n + 1) % 2 = 1 by omega
  have h₁₀ : h.rungs {n | n % 2 = 1} ≤
      ClosureSubsystem.generate p (range A) ⊔ h.rungs {n | n % 2 = 0} :=
    h.rungs_le_sup fun n (hn : n % 2 = 1) ↦ show (n + 1) % 2 = 0 by omega
  have heq : ClosureSubsystem.generate p (range A) ⊔ h.rungs {n | n % 2 = 0} =
      ClosureSubsystem.generate p (range A) ⊔ h.rungs {n | n % 2 = 1} :=
    le_antisymm (sup_le le_sup_left h₀₁) (sup_le le_sup_left h₁₀)
  have hsd := _root_.FCA.sup_eq_sup_inf_of_sup_eq_sup heq
  rw [h.rungs_inf_rungs hE, sup_bot_eq] at hsd
  refine h.notMem_generate ?_
  rw [← hsd]
  exact ClosureSubsystem.le_def.1 le_sup_right
    ((h.mem_rungs_iff (E := {n | n % 2 = 0}) (n := 0)).2 rfl)

end IsLadder

namespace ClosureSubsystem

variable [IsClosureSystem p] {𝒜 ℬ 𝒞 : ClosureSubsystem p}

/-- A failure of join-semidistributivity in the lattice of closure subsystems yields a ladder. -/
theorem exists_isLadder_of_sup_ne (h : 𝒜 ⊔ ℬ = 𝒜 ⊔ 𝒞) (hne : 𝒜 ⊔ ℬ ≠ 𝒜 ⊔ ℬ ⊓ 𝒞) :
    ∃ X A, IsLadder p X A := by
  have h𝒜 : ∀ {A : Set α}, A ∈ 𝒜 → A ∈ 𝒜 ⊔ ℬ ⊓ 𝒞 := fun hA ↦ le_def.1 le_sup_left hA
  -- every bad set in `ℬ` or `𝒞` is cut out of a strictly larger bad set by a member of `𝒜`
  have step : ∀ s : {Y : Set α // Y ∉ 𝒜 ⊔ ℬ ⊓ 𝒞 ∧ (Y ∈ ℬ ∨ Y ∈ 𝒞)},
      ∃ A : Set α, ∃ t : {Y : Set α // Y ∉ 𝒜 ⊔ ℬ ⊓ 𝒞 ∧ (Y ∈ ℬ ∨ Y ∈ 𝒞)},
        A ∈ 𝒜 ∧ A ∩ t.1 = s.1 ∧ s.1 ≠ t.1 := by
    rintro ⟨Y, hY, hB | hC⟩
    · have hmem : Y ∈ 𝒜 ⊔ 𝒞 := h ▸ le_def.1 le_sup_right hB
      obtain ⟨A, hA, C, hC, rfl⟩ := mem_sup.1 hmem
      refine ⟨A, ⟨C, fun hCG ↦ hY (inter_mem (h𝒜 hA) hCG), .inr hC⟩, hA, rfl, fun heq ↦ hY ?_⟩
      refine le_def.1 le_sup_right (mem_inf.2 ⟨hB, ?_⟩)
      rw [show A ∩ C = C from heq]
      exact hC
    · have hmem : Y ∈ 𝒜 ⊔ ℬ := h.symm ▸ le_def.1 le_sup_right hC
      obtain ⟨A, hA, B, hB, rfl⟩ := mem_sup.1 hmem
      refine ⟨A, ⟨B, fun hBG ↦ hY (inter_mem (h𝒜 hA) hBG), .inl hB⟩, hA, rfl, fun heq ↦ hY ?_⟩
      refine le_def.1 le_sup_right (mem_inf.2 ⟨?_, hC⟩)
      rw [show A ∩ B = B from heq]
      exact hB
  choose a t ha heq hne' using step
  -- a first bad set
  have hnle : ¬𝒜 ⊔ ℬ ≤ 𝒜 ⊔ ℬ ⊓ 𝒞 := fun hle ↦
    hne (le_antisymm hle (sup_le_sup_left inf_le_left _))
  rw [le_def] at hnle
  push Not at hnle
  obtain ⟨D, hD, hDG⟩ := hnle
  obtain ⟨A', hA', B, hB, rfl⟩ := mem_sup.1 hD
  let s₀ : {Y : Set α // Y ∉ 𝒜 ⊔ ℬ ⊓ 𝒞 ∧ (Y ∈ ℬ ∨ Y ∈ 𝒞)} :=
    ⟨B, fun hBG ↦ hDG (inter_mem (h𝒜 hA') hBG), .inl hB⟩
  have hsucc : ∀ n, a (t^[n] s₀) ∩ (t^[n + 1] s₀).1 = (t^[n] s₀).1 := fun n ↦ by
    rw [iterate_succ_apply']
    exact heq _
  refine ⟨fun n ↦ (t^[n] s₀).1, fun n ↦ a (t^[n] s₀), fun n ↦ ?_, fun n ↦ 𝒜.isClosed (ha _),
    fun n ↦ ?_, hsucc, fun h0 ↦ ?_⟩
  · exact (t^[n] s₀).2.2.elim ℬ.isClosed 𝒞.isClosed
  · refine ((hsucc n).symm.subset.trans inter_subset_right).ssubset_of_ne ?_
    rw [iterate_succ_apply']
    exact hne' _
  · refine s₀.2.1 (h𝒜 ?_)
    have hmem : ⋂₀ range (fun n ↦ a (t^[n] s₀)) ∈ 𝒜 :=
      𝒜.sInter_mem (by rintro _ ⟨n, rfl⟩; exact ha _)
    rw [sInter_range] at hmem
    exact h0 ▸ hmem

/-- The lattice of closure subsystems of a closure system is join-semidistributive if and only
if the closure system has no ladder. -/
theorem isJoinSemidistrib_iff_not_isLadder :
    IsJoinSemidistrib (ClosureSubsystem p) ↔ ¬∃ X A, IsLadder p X A := by
  refine ⟨fun hsd ⟨X, A, h⟩ ↦ h.not_isJoinSemidistrib hsd, fun hno ↦ ⟨fun 𝒜 ℬ 𝒞 h ↦ ?_⟩⟩
  by_contra hne
  exact hno (exists_isLadder_of_sup_ne h hne)

/-- The powerset of an infinite type has a ladder. -/
theorem exists_isLadder_of_infinite (α : Type*) [Infinite α] :
    ∃ X A, IsLadder (fun _ : Set α ↦ True) X A := by
  obtain ⟨f, hf⟩ := Infinite.natEmbedding α
  refine ⟨fun n ↦ {x | ∃ k, 1 ≤ k ∧ k ≤ n ∧ f k = x}, fun n ↦ {f (n + 1)}ᶜ,
    fun _ ↦ True.intro, fun _ ↦ True.intro, fun n ↦ ?_, fun n ↦ ?_, fun h0 ↦ ?_⟩
  · refine ⟨fun x ⟨k, h₁, h₂, hk⟩ ↦ ⟨k, h₁, h₂.trans n.le_succ, hk⟩, fun hsub ↦ ?_⟩
    obtain ⟨k, -, hk, hfk⟩ := hsub ⟨n + 1, by omega, le_rfl, rfl⟩
    have := hf hfk
    omega
  · ext x
    constructor
    · rintro ⟨hx, k, h₁, h₂, rfl⟩
      refine ⟨k, h₁, ?_, rfl⟩
      have hk : k ≠ n + 1 := fun hk ↦ hx (by rw [hk]; rfl)
      omega
    · rintro ⟨k, h₁, h₂, rfl⟩
      refine ⟨fun hk ↦ ?_, k, h₁, h₂.trans n.le_succ, rfl⟩
      have := hf (mem_singleton_iff.1 hk)
      omega
  · have hmem : f 0 ∈ ⋂ n : ℕ, ({f (n + 1)}ᶜ : Set α) := mem_iInter.2 fun n hn ↦ by
      have := hf (mem_singleton_iff.1 hn)
      omega
    rw [h0] at hmem
    obtain ⟨k, h₁, h₂, -⟩ := hmem
    omega

/-- The lattice of all closure systems on an infinite type is not join-semidistributive. -/
theorem not_isJoinSemidistrib_of_infinite (α : Type*) [Infinite α] :
    ¬IsJoinSemidistrib (ClosureSubsystem fun _ : Set α ↦ True) := by
  obtain ⟨X, A, h⟩ := exists_isLadder_of_infinite α
  exact h.not_isJoinSemidistrib

end ClosureSubsystem

end FCA
