/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Ordinal
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Card

/-!
# Truncated powersets: ordinal covers are not monotone

For a finite type `α` and a natural number `k`, the sets with at most `k` elements together with
`univ` form a closure system on `α`, the *truncation* of the powerset at `k`. Its `⋂`-irreducible
closed sets include all `k`-element sets, which are pairwise incomparable. Hence a cover of the
truncation by chains needs at least `(|α|).choose k` chains, whereas the whole powerset is covered
by `|α|` chains.

Consequently the ordinal scaling dimension is not monotone in the lattice of closure systems,
in contrast to the order dimension.

## Main definitions

* `FCA.ClosureSubsystem.truncation α k`: the closure system of the sets with at most `k` elements
  and `univ`.

## Main results

* `FCA.ClosureSubsystem.choose_le_card_of_hasOrdinalCover_truncation`: a cover of the truncation
  at `k < |α|` by `ι` ordinal closure systems requires `(|α|).choose k ≤ |ι|`.
* `FCA.ClosureSubsystem.hasOrdinalCover_top_powerset`: the powerset of `α` has ordinal scaling
  dimension at most `|α|`.
* `FCA.ClosureSubsystem.exists_le_hasOrdinalCover_not_hasOrdinalCover`: there are closure systems
  `𝒜 ≤ ℬ` such that `ℬ` is covered by four ordinal closure systems and `𝒜` is not.
-/

@[expose] public section

open Set Function Order

namespace FCA

namespace ClosureSubsystem

variable {α ι : Type*}

/-- The closure system of all sets with at most `k` elements, together with `univ`. -/
def truncation (α : Type*) [Finite α] (k : ℕ) : ClosureSubsystem fun _ : Set α ↦ True where
  carrier := {A | A.ncard ≤ k ∨ A = univ}
  sInter_mem' S hS := by
    by_cases h : ∃ A ∈ S, A.ncard ≤ k
    · obtain ⟨A, hA, hAk⟩ := h
      exact .inl ((ncard_le_ncard (sInter_subset_of_mem hA)).trans hAk)
    · refine .inr (sInter_eq_univ.2 fun A hA ↦ (hS hA).resolve_left fun hAk ↦ h ⟨A, hA, hAk⟩)
  isClosed' _ _ := True.intro

@[simp]
theorem mem_truncation [Finite α] {k : ℕ} {A : Set α} :
    A ∈ truncation α k ↔ A.ncard ≤ k ∨ A = univ :=
  Iff.rfl

/-- In the truncation at `k < |α|`, every `k`-element set is `⋂`-irreducible. -/
theorem mem_irreducibles_truncation [Finite α] {k : ℕ} {A : Set α} (hA : A.ncard = k)
    (hk : k < Nat.card α) : A ∈ (truncation α k).irreducibles := by
  refine ⟨.inl hA.le, fun h ↦ ?_⟩
  have huniv : ⋂₀ {B | B ∈ truncation α k ∧ A ⊂ B} = univ :=
    sInter_eq_univ.2 fun B hB ↦ hB.1.resolve_left fun hBk ↦
      absurd (ncard_lt_ncard hB.2) (by omega)
  rw [huniv] at h
  rw [← h, ncard_univ] at hA
  omega

/-- A cover of the truncation at `k < |α|` by `ι` ordinal closure systems needs at least
`(|α|).choose k` of them: the `k`-element sets are irreducible and pairwise incomparable. -/
theorem choose_le_card_of_hasOrdinalCover_truncation [Fintype α] [Fintype ι] {k : ℕ}
    (hk : k < Fintype.card α) (h : (truncation α k).HasOrdinalCover ι) :
    (Fintype.card α).choose k ≤ Fintype.card ι := by
  classical
  obtain ⟨g, hg, hgu⟩ := h.exists_chains
  have hmem : ∀ s : {s : Finset α // s.card = k}, ∃ i, ((s : Finset α) : Set α) ∈ g i := by
    intro s
    have : ((s : Finset α) : Set α) ∈ (truncation α k).irreducibles :=
      mem_irreducibles_truncation (by rw [ncard_coe_finset, s.2])
        (by rwa [Nat.card_eq_fintype_card])
    rw [← hgu] at this
    exact mem_iUnion.1 this
  choose f hf using hmem
  have hinj : Injective f := by
    intro s t hst
    have hs := hf s
    have ht := hf t
    rw [← hst] at ht
    have hcomp := (hg (f s)).total hs ht
    have hcard : (s : Finset α).card = (t : Finset α).card := by rw [s.2, t.2]
    rcases hcomp with h | h
    · exact Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.coe_subset.1 h) hcard.ge)
    · exact Subtype.ext (Finset.eq_of_subset_of_card_le (Finset.coe_subset.1 h) hcard.le).symm
  simpa [Fintype.card_finset_len] using Fintype.card_le_of_injective f hinj

/-- The `⋂`-irreducible sets of the powerset are the complements of singletons. -/
theorem irreducibles_top_powerset :
    (⊤ : ClosureSubsystem fun _ : Set α ↦ True).irreducibles =
      range fun a : α ↦ ({a}ᶜ : Set α) := by
  ext A
  constructor
  · rintro ⟨-, hA⟩
    have hsub : A ⊆ ⋂₀ {B | B ∈ (⊤ : ClosureSubsystem fun _ : Set α ↦ True) ∧ A ⊂ B} :=
      subset_sInter fun B hB ↦ hB.2.subset
    obtain ⟨x, hx, hxA⟩ := not_subset.1 fun h ↦ hA (Subset.antisymm h hsub)
    refine ⟨x, Subset.antisymm (fun y hy ↦ ?_) fun y hy hyx ↦ hxA (hyx ▸ hy)⟩
    by_contra hyA
    have hmem : insert y A ∈ {B | B ∈ (⊤ : ClosureSubsystem fun _ : Set α ↦ True) ∧ A ⊂ B} :=
      ⟨mem_top.2 True.intro, ssubset_insert hyA⟩
    rcases hx _ hmem with h | h
    · exact hy h.symm
    · exact hxA h
  · rintro ⟨a, rfl⟩
    refine ⟨mem_top.2 True.intro, fun h ↦ ?_⟩
    have hmem : (univ : Set α) ∈
        {B | B ∈ (⊤ : ClosureSubsystem fun _ : Set α ↦ True) ∧ ({a}ᶜ : Set α) ⊂ B} :=
      ⟨mem_top.2 True.intro, ssubset_univ_iff.2 fun h ↦ by simpa using congrArg (a ∈ ·) h⟩
    have hsub : ⋂₀ {B | B ∈ (⊤ : ClosureSubsystem fun _ : Set α ↦ True) ∧ ({a}ᶜ : Set α) ⊂ B} ⊆
        ({a}ᶜ : Set α) := h.subset
    refine hsub (mem_sInter.2 fun B hB ↦ ?_) rfl
    by_contra haB
    exact hB.2.ne (Subset.antisymm hB.2.subset fun y hy hya ↦ haB (hya ▸ hy))

/-- The powerset of a finite type `α` is covered by `|α|` ordinal closure systems. -/
theorem hasOrdinalCover_top_powerset [Finite α] :
    (⊤ : ClosureSubsystem fun _ : Set α ↦ True).HasOrdinalCover α :=
  hasOrdinalCover_iff_irreducibles.2 ⟨fun a ↦ {({a}ᶜ : Set α)}, fun _ ↦ IsChain.singleton, by
    rw [irreducibles_top_powerset]
    ext A
    simp [eq_comm]⟩

/-- The ordinal scaling dimension is not monotone: the powerset of a four-element set is
covered by four ordinal closure systems, but its truncation at two is not. -/
theorem exists_le_hasOrdinalCover_not_hasOrdinalCover :
    ∃ 𝒜 ℬ : ClosureSubsystem fun _ : Set (Fin 4) ↦ True,
      𝒜 ≤ ℬ ∧ ℬ.HasOrdinalCover (Fin 4) ∧ ¬𝒜.HasOrdinalCover (Fin 4) :=
  ⟨truncation (Fin 4) 2, ⊤, le_top, hasOrdinalCover_top_powerset, fun h ↦ by
    have := choose_le_card_of_hasOrdinalCover_truncation (k := 2) (by simp) h
    simp [Nat.choose] at this⟩

end ClosureSubsystem

end FCA
