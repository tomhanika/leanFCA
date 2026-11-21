/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Structure
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Bounds.Basic

/-!
# The ascending chain condition cannot be dropped

For closure systems whose closed sets satisfy the ascending chain condition, the lattice of
closure subsystems is join-semidistributive and join-pseudocomplemented. This file shows that
both properties fail in general.

On `Option ℕ` let `𝒜` consist of the sets containing `none`, and for a set `E` of natural numbers
let `segments E` consist of `univ` and the initial segments `{0, …, n}` with `n ∈ E`. If `E` is
unbounded, the join of `𝒜` and `segments E` consists of the sets which contain `none` or are
finite, whatever `E` is. For the even and the odd numbers the two closure systems `segments E`
meet in the least closure system, whose join with `𝒜` is just `𝒜`.

## Main results

* `FCA.ClosureSubsystem.not_isJoinSemidistrib_of_forall`: the lattice of closure subsystems of a
  closure system on `Option ℕ` containing these sets is not join-semidistributive.
* `FCA.ClosureSubsystem.not_isJoinSemidistrib_option_nat`: in particular the lattice of all
  closure systems on `Option ℕ` is not join-semidistributive.
* `FCA.ClosureSubsystem.not_isJoinPseudocomplemented_noneOrFinite`: the lattice of closure
  subsystems of the closure system of the sets which contain `none` or are finite is not
  join-pseudocomplemented.
-/

@[expose] public section

open Set Function Order

namespace FCA

namespace ClosureSubsystem

/-- The initial segment `{0, …, n}` of the natural numbers inside `Option ℕ`. -/
def initialSeg (n : ℕ) : Set (Option ℕ) :=
  some '' {k | k ≤ n}

theorem some_mem_initialSeg {n k : ℕ} : some k ∈ initialSeg n ↔ k ≤ n := by
  simp [initialSeg]

theorem none_notMem_initialSeg (n : ℕ) : none ∉ initialSeg n := by
  simp [initialSeg]

theorem finite_initialSeg (n : ℕ) : (initialSeg n).Finite :=
  (finite_le_nat n).image _

theorem initialSeg_subset {m n : ℕ} (h : m ≤ n) : initialSeg m ⊆ initialSeg n :=
  image_mono fun _ hk ↦ le_trans hk h

theorem initialSeg_injective : Injective initialSeg := fun _ _ h ↦
  le_antisymm (some_mem_initialSeg.1 (h ▸ some_mem_initialSeg.2 le_rfl))
    (some_mem_initialSeg.1 (h ▸ some_mem_initialSeg.2 le_rfl))

/-- The sets which contain `none` or are finite. -/
def NoneOrFinite (A : Set (Option ℕ)) : Prop :=
  none ∈ A ∨ A.Finite

instance : IsClosureSystem NoneOrFinite where
  sInter_mem S hS := by
    by_cases h : ∀ A ∈ S, none ∈ A
    · exact .inl (mem_sInter.2 h)
    · push Not at h
      obtain ⟨A, hA, hnone⟩ := h
      exact .inr (((hS A hA).resolve_left hnone).subset (sInter_subset_of_mem hA))

variable {p : Set (Option ℕ) → Prop} [IsClosureSystem p]

/-- The closure system of the sets containing `none`. -/
def containingNone (hp : ∀ A, NoneOrFinite A → p A) : ClosureSubsystem p where
  carrier := {A | none ∈ A}
  sInter_mem' _ hS := mem_sInter.2 fun _ hA ↦ hS hA
  isClosed' A hA := hp A (.inl hA)

/-- The closure system of `univ` and the initial segments `{0, …, n}` with `n ∈ E`. -/
def segments (hp : ∀ A, NoneOrFinite A → p A) (E : Set ℕ) : ClosureSubsystem p where
  carrier := {A | A = univ ∨ ∃ n ∈ E, A = initialSeg n}
  sInter_mem' S hS := by
    classical
    by_cases h : ∃ n, initialSeg n ∈ S
    · have heq : ⋂₀ S = initialSeg (Nat.find h) := by
        refine Subset.antisymm (sInter_subset_of_mem (Nat.find_spec h))
          (subset_sInter fun A hA ↦ ?_)
        rcases hS hA with rfl | ⟨n, -, rfl⟩
        · exact subset_univ _
        · exact initialSeg_subset (Nat.find_min' h hA)
      rw [heq]
      exact hS (Nat.find_spec h)
    · refine .inl (sInter_eq_univ.2 fun A hA ↦ (hS hA).elim id ?_)
      rintro ⟨n, -, rfl⟩
      exact absurd ⟨n, hA⟩ h
  isClosed' A hA := by
    rcases hA with rfl | ⟨n, -, rfl⟩
    · exact hp _ (.inl (mem_univ _))
    · exact hp _ (.inr (finite_initialSeg n))

variable {hp : ∀ A, NoneOrFinite A → p A} {E E' : Set ℕ} {A : Set (Option ℕ)}

/-- For an unbounded set `E`, the join of `containingNone` and `segments E` consists of the sets
which contain `none` or are finite; it does not depend on `E`. -/
theorem mem_containingNone_sup_segments (hE : ∀ n, ∃ m ∈ E, n ≤ m) :
    A ∈ containingNone hp ⊔ segments hp E ↔ NoneOrFinite A := by
  rw [mem_sup]
  constructor
  · rintro ⟨A₁, h₁, A₂, h₂ | ⟨n, -, rfl⟩, rfl⟩
    · subst h₂
      exact .inl ⟨h₁, mem_univ _⟩
    · exact .inr ((finite_initialSeg n).subset inter_subset_right)
  · intro hA
    by_cases hnone : none ∈ A
    · exact ⟨A, hnone, univ, .inl rfl, inter_univ A⟩
    · have hfin : (some ⁻¹' A).Finite :=
        (hA.resolve_left hnone).preimage (Option.some_injective ℕ).injOn
      obtain ⟨N, hN⟩ := Set.Finite.bddAbove hfin
      obtain ⟨m, hm, hNm⟩ := hE N
      refine ⟨insert none A, mem_insert _ _, initialSeg m, .inr ⟨m, hm, rfl⟩, ?_⟩
      ext x
      cases x with
      | none => simp [hnone, none_notMem_initialSeg]
      | some k =>
        simp only [mem_inter_iff, mem_insert_iff, reduceCtorEq, false_or, some_mem_initialSeg]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (hN h).trans hNm⟩⟩

theorem containingNone_sup_segments_eq (hE : ∀ n, ∃ m ∈ E, n ≤ m) (hE' : ∀ n, ∃ m ∈ E', n ≤ m) :
    containingNone hp ⊔ segments hp E = containingNone hp ⊔ segments hp E' :=
  ClosureSubsystem.ext (Set.ext fun _ ↦
    (mem_containingNone_sup_segments hE).trans (mem_containingNone_sup_segments hE').symm)

/-- For disjoint sets `E` and `E'`, the closure systems `segments E` and `segments E'` have only
`univ` in common. -/
theorem segments_inf_segments (h : Disjoint E E') : segments hp E ⊓ segments hp E' = ⊥ := by
  refine eq_bot_iff.2 (le_def.2 fun A hA ↦ mem_bot.2 ?_)
  obtain ⟨h₁, h₂⟩ := mem_inf.1 hA
  rcases h₁ with rfl | ⟨n, hn, rfl⟩
  · rfl
  · rcases h₂ with h₂ | ⟨m, hm, h₂⟩
    · exact h₂
    · exact absurd hm (disjoint_left.1 h (initialSeg_injective h₂ ▸ hn))

/-- The initial segment `{0}` is not in the join of `containingNone` with any closure system
below two closure systems `segments E` for disjoint sets `E`. -/
theorem initialSeg_notMem_containingNone_sup (h : Disjoint E E') {𝒟 : ClosureSubsystem p}
    (h𝒟 : 𝒟 ≤ segments hp E) (h𝒟' : 𝒟 ≤ segments hp E') :
    initialSeg 0 ∉ containingNone hp ⊔ 𝒟 := by
  intro hmem
  obtain ⟨A₁, h₁, A₂, h₂, heq⟩ := mem_sup.1 hmem
  have hbot : A₂ ∈ (⊥ : ClosureSubsystem p) := by
    rw [← segments_inf_segments (hp := hp) h]
    exact mem_inf.2 ⟨le_def.1 h𝒟 h₂, le_def.1 h𝒟' h₂⟩
  rw [mem_bot.1 hbot, inter_univ] at heq
  exact none_notMem_initialSeg 0 (heq ▸ h₁)

theorem exists_even_ge (n : ℕ) : ∃ m ∈ {m : ℕ | Even m}, n ≤ m := by
  rcases Nat.even_or_odd n with h | h
  · exact ⟨n, h, le_rfl⟩
  · exact ⟨n + 1, h.add_one, n.le_succ⟩

theorem exists_odd_ge (n : ℕ) : ∃ m ∈ {m : ℕ | Odd m}, n ≤ m := by
  rcases Nat.even_or_odd n with h | h
  · exact ⟨n + 1, h.add_one, n.le_succ⟩
  · exact ⟨n, h, le_rfl⟩

theorem disjoint_even_odd : Disjoint {m : ℕ | Even m} {m : ℕ | Odd m} :=
  disjoint_left.2 fun _ h h' ↦ Nat.not_even_iff_odd.2 h' h

/-- If a closure system on `Option ℕ` contains all sets which contain `none` or are finite, its
lattice of closure subsystems is not join-semidistributive. -/
theorem not_isJoinSemidistrib_of_forall (hp : ∀ A, NoneOrFinite A → p A) :
    ¬IsJoinSemidistrib (ClosureSubsystem p) := by
  intro _
  have h := _root_.FCA.sup_eq_sup_inf_of_sup_eq_sup
    (containingNone_sup_segments_eq (hp := hp) exists_even_ge exists_odd_ge)
  refine initialSeg_notMem_containingNone_sup (hp := hp) disjoint_even_odd inf_le_left
    inf_le_right ?_
  rw [← h]
  exact (mem_containingNone_sup_segments exists_even_ge).2 (.inr (finite_initialSeg 0))

/-- The lattice of all closure systems on a countably infinite set is not
join-semidistributive. -/
theorem not_isJoinSemidistrib_option_nat :
    ¬IsJoinSemidistrib (ClosureSubsystem fun _ : Set (Option ℕ) ↦ True) :=
  not_isJoinSemidistrib_of_forall fun _ _ ↦ True.intro

/-- The closure system of the sets which contain `none` or are finite has a closure subsystem
without a join-pseudocomplement. -/
theorem not_isJoinPseudocomplemented_noneOrFinite :
    ¬IsJoinPseudocomplemented (ClosureSubsystem NoneOrFinite) := by
  intro _
  have hp : ∀ A, NoneOrFinite A → NoneOrFinite A := fun _ h ↦ h
  obtain ⟨c, hc⟩ := IsJoinPseudocomplemented.exists_isJoinPseudocompl (containingNone hp)
  have htop : ∀ {E : Set ℕ}, (∀ n, ∃ m ∈ E, n ≤ m) → containingNone hp ⊔ segments hp E = ⊤ :=
    fun hE ↦ top_unique (le_def.2 fun A hA ↦
      (mem_containingNone_sup_segments hE).2 (mem_top.1 hA))
  refine initialSeg_notMem_containingNone_sup (hp := hp) disjoint_even_odd
    (hc.le_iff.2 (htop exists_even_ge)) (hc.le_iff.2 (htop exists_odd_ge)) ?_
  rw [hc.sup_eq_top]
  exact mem_top.2 (.inr (finite_initialSeg 0))

end ClosureSubsystem

end FCA
