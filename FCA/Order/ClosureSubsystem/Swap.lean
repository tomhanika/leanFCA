/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Reconstruction

/-!
# Swapping two blocks of closed sets

The lattice of closure subsystems of a closure system `p` on a finite type has, in general, more
automorphisms than the lattice of closed sets of `p`. This file constructs such automorphisms.

Let `𝒳` and `𝒴` be two sets of proper closed sets, every member of `𝒳` strictly contained in
every member of `𝒴`, and let `θ` be an order isomorphism between them. If both blocks are closed
under intersections of incomparable sets, every other proper closed set is related in the same
way to all members of the two blocks or lies between them, and no member of a block is the
intersection of two incomparable sets outside the blocks, then the bijection which exchanges `𝒳`
and `𝒴` along `θ` and fixes all other proper closed sets preserves comparability and
intersections of incomparable sets. It therefore induces an automorphism of the lattice of
closure subsystems, although it reverses inclusions between the two blocks.

By a theorem of Shevrin, all isomorphisms between the lattices of subsemilattices of two
semilattices arise from permutations of ordinal components of this kind. This file proves only
the constructive direction.

## Main definitions

* `FCA.IsSwappable 𝒳 𝒴 θ`: the hypotheses above.
* `FCA.IsSwappable.swapEquiv`: the bijection of the proper closed sets exchanging `𝒳` and `𝒴`.
* `FCA.IsSwappable.swapOrderIso`: the induced automorphism of the lattice of closure subsystems.

## Main results

* `FCA.IsSwappable.isInterEquiv_swapEquiv`: the bijection `swapEquiv` preserves comparability and
  intersections of incomparable sets.
* `FCA.IsSwappable.ssubset_swapEquiv`, `FCA.IsSwappable.not_forall_subset_swapEquiv`: it is not
  monotone if `𝒳` is nonempty.
* `FCA.IsSwappable.not_exists_orderIso`: the automorphism `swapOrderIso` is not induced by an
  order automorphism of the closed sets.
* `FCA.isSwappable_singleton`: two comparable proper closed sets which are comparable to all
  closed sets and are not intersections of incomparable closed sets can be exchanged.

## References

* [L. N. Shevrin, *Fundamental questions in the theory of projectivities of
  semilattices*][shevrin1965]
* [J. Morgado, *Quasi-isomorphisms between complete lattices*][morgado1961]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α : Type*} {p : Set α → Prop}

/-- The intersection of two proper closed sets, as a proper closed set. -/
def ProperClosed.inter [IsClosureSystem p] (A A' : ProperClosed p) : ProperClosed p :=
  ⟨A.1 ∩ A'.1, IsClosureSystem.inter_mem A.2.1 A'.2.1,
    fun hu ↦ A.2.2 (univ_subset_iff.1 (hu.symm.subset.trans inter_subset_left))⟩

@[simp]
theorem ProperClosed.coe_inter [IsClosureSystem p] (A A' : ProperClosed p) :
    (ProperClosed.inter A A' : Set α) = A.1 ∩ A'.1 :=
  rfl

/-- Two blocks `𝒳` and `𝒴` of proper closed sets can be exchanged along the bijection `θ`. -/
structure IsSwappable (𝒳 𝒴 : Set (ProperClosed p)) (θ : 𝒳 ≃ 𝒴) : Prop where
  /-- Every member of `𝒳` is strictly contained in every member of `𝒴`. -/
  ssubset : ∀ x ∈ 𝒳, ∀ y ∈ 𝒴, (x : Set α) ⊂ y
  /-- The block `𝒳` is closed under intersections of incomparable sets. -/
  inter_mem_left : ∀ x ∈ 𝒳, ∀ x' ∈ 𝒳, ∀ c : ProperClosed p, ¬(x : Set α) ⊆ x' →
    ¬(x' : Set α) ⊆ x → (c : Set α) = x.1 ∩ x'.1 → c ∈ 𝒳
  /-- The block `𝒴` is closed under intersections of incomparable sets. -/
  inter_mem_right : ∀ y ∈ 𝒴, ∀ y' ∈ 𝒴, ∀ c : ProperClosed p, ¬(y : Set α) ⊆ y' →
    ¬(y' : Set α) ⊆ y → (c : Set α) = y.1 ∩ y'.1 → c ∈ 𝒴
  /-- Every proper closed set outside the blocks is related in the same way to all members of
  the blocks, or lies between the two blocks. -/
  uniform_or_between : ∀ z : ProperClosed p, z ∉ 𝒳 ∪ 𝒴 →
    (∀ u ∈ 𝒳 ∪ 𝒴, ∀ v ∈ 𝒳 ∪ 𝒴,
      ((z : Set α) ⊆ u ↔ (z : Set α) ⊆ v) ∧ ((u : Set α) ⊆ z ↔ (v : Set α) ⊆ z)) ∨
    ((∀ x ∈ 𝒳, (x : Set α) ⊆ z) ∧ ∀ y ∈ 𝒴, (z : Set α) ⊆ y)
  /-- The intersection of two incomparable sets outside the blocks is outside the blocks. -/
  inter_notMem : ∀ z ∉ 𝒳 ∪ 𝒴, ∀ z' ∉ 𝒳 ∪ 𝒴, ∀ c : ProperClosed p, ¬(z : Set α) ⊆ z' →
    ¬(z' : Set α) ⊆ z → (c : Set α) = z.1 ∩ z'.1 → c ∉ 𝒳 ∪ 𝒴
  /-- The bijection `θ` is an order isomorphism. -/
  map_subset_map_iff : ∀ x x' : 𝒳, (θ x).1.1 ⊆ (θ x').1.1 ↔ x.1.1 ⊆ x'.1.1

open Classical in
/-- The map exchanging the blocks `𝒳` and `𝒴` along `θ` and fixing all other proper closed
sets. -/
noncomputable def swapFun (𝒳 𝒴 : Set (ProperClosed p)) (θ : 𝒳 ≃ 𝒴) (z : ProperClosed p) :
    ProperClosed p :=
  if hx : z ∈ 𝒳 then θ ⟨z, hx⟩ else if hy : z ∈ 𝒴 then θ.symm ⟨z, hy⟩ else z

theorem swapFun_of_mem_left {𝒳 𝒴 : Set (ProperClosed p)} {θ : 𝒳 ≃ 𝒴} {z : ProperClosed p}
    (hx : z ∈ 𝒳) : swapFun 𝒳 𝒴 θ z = θ ⟨z, hx⟩ := by
  simp [swapFun, hx]

/-- If the intersections of incomparable members of `𝒯` lie in `𝒯`, and `ψ` is an involution
exchanging `𝒮` and `𝒯` which preserves and reflects inclusion on each of them, then `ψ` maps
the intersection of two incomparable members of `𝒮` to the intersection of their images. -/
private theorem coe_map_eq_inter_of_blocks [IsClosureSystem p]
    {ψ : ProperClosed p → ProperClosed p} (hinv : Involutive ψ) {𝒮 𝒯 : Set (ProperClosed p)}
    (hST : ∀ z ∈ 𝒮, ψ z ∈ 𝒯) (hTS : ∀ z ∈ 𝒯, ψ z ∈ 𝒮)
    (hS : ∀ z ∈ 𝒮, ∀ z' ∈ 𝒮, ((ψ z : Set α) ⊆ ψ z' ↔ (z : Set α) ⊆ z'))
    (hT : ∀ z ∈ 𝒯, ∀ z' ∈ 𝒯, ((ψ z : Set α) ⊆ ψ z' ↔ (z : Set α) ⊆ z'))
    (hinter : ∀ y ∈ 𝒯, ∀ y' ∈ 𝒯, ∀ c : ProperClosed p, ¬(y : Set α) ⊆ y' →
      ¬(y' : Set α) ⊆ y → (c : Set α) = y.1 ∩ y'.1 → c ∈ 𝒯)
    {A A' C : ProperClosed p} (hA : A ∈ 𝒮) (hA' : A' ∈ 𝒮) (hC : C ∈ 𝒮)
    (hAA' : ¬(A : Set α) ⊆ A') (hA'A : ¬(A' : Set α) ⊆ A) (hCeq : (C : Set α) = A.1 ∩ A'.1) :
    (ψ C : Set α) = (ψ A).1 ∩ (ψ A').1 := by
  have hD : ProperClosed.inter (ψ A) (ψ A') ∈ 𝒯 :=
    hinter _ (hST A hA) _ (hST A' hA') _ (fun h ↦ hAA' ((hS A hA A' hA').1 h))
      (fun h ↦ hA'A ((hS A' hA' A hA).1 h)) rfl
  refine Subset.antisymm (subset_inter ?_ ?_) ?_
  · exact (hS C hC A hA).2 (hCeq ▸ inter_subset_left)
  · exact (hS C hC A' hA').2 (hCeq ▸ inter_subset_right)
  · have h₁ : (ψ (ProperClosed.inter (ψ A) (ψ A')) : Set α) ⊆ A := by
      have := (hT _ hD _ (hST A hA)).2 inter_subset_left
      rwa [hinv A] at this
    have h₂ : (ψ (ProperClosed.inter (ψ A) (ψ A')) : Set α) ⊆ A' := by
      have := (hT _ hD _ (hST A' hA')).2 inter_subset_right
      rwa [hinv A'] at this
    have h₃ : (ψ (ProperClosed.inter (ψ A) (ψ A')) : Set α) ⊆ C :=
      hCeq ▸ subset_inter h₁ h₂
    have := (hS _ (hTS _ hD) C hC).2 h₃
    rwa [hinv] at this

namespace IsSwappable

variable {𝒳 𝒴 : Set (ProperClosed p)} {θ : 𝒳 ≃ 𝒴}
  {z u A A' C : ProperClosed p}

theorem notMem_right (h : IsSwappable 𝒳 𝒴 θ) (hx : z ∈ 𝒳) : z ∉ 𝒴 :=
  fun hy ↦ (h.ssubset z hx z hy).ne rfl

theorem swapFun_of_mem_right (h : IsSwappable 𝒳 𝒴 θ) (hy : z ∈ 𝒴) :
    swapFun 𝒳 𝒴 θ z = θ.symm ⟨z, hy⟩ := by
  have hx : z ∉ 𝒳 := fun hx ↦ h.notMem_right hx hy
  simp [swapFun, hx, hy]

theorem swapFun_of_notMem (hz : z ∉ 𝒳 ∪ 𝒴) : swapFun 𝒳 𝒴 θ z = z := by
  have hx : z ∉ 𝒳 := fun hx ↦ hz (.inl hx)
  have hy : z ∉ 𝒴 := fun hy ↦ hz (.inr hy)
  simp [swapFun, hx, hy]

theorem swapFun_mem_right (hx : z ∈ 𝒳) : swapFun 𝒳 𝒴 θ z ∈ 𝒴 := by
  rw [swapFun_of_mem_left hx]
  exact (θ _).2

theorem swapFun_mem_left (h : IsSwappable 𝒳 𝒴 θ) (hy : z ∈ 𝒴) : swapFun 𝒳 𝒴 θ z ∈ 𝒳 := by
  rw [h.swapFun_of_mem_right hy]
  exact (θ.symm _).2

theorem swapFun_mem_union (h : IsSwappable 𝒳 𝒴 θ) (hu : u ∈ 𝒳 ∪ 𝒴) :
    swapFun 𝒳 𝒴 θ u ∈ 𝒳 ∪ 𝒴 :=
  hu.elim (fun hx ↦ .inr (swapFun_mem_right hx)) fun hy ↦ .inl (h.swapFun_mem_left hy)

/-- Exchanging the blocks twice is the identity. -/
theorem involutive_swapFun (h : IsSwappable 𝒳 𝒴 θ) : Involutive (swapFun 𝒳 𝒴 θ) := by
  intro z
  by_cases hx : z ∈ 𝒳
  · rw [swapFun_of_mem_left hx, h.swapFun_of_mem_right (θ _).2]
    simp
  · by_cases hy : z ∈ 𝒴
    · rw [h.swapFun_of_mem_right hy, swapFun_of_mem_left (θ.symm _).2]
      simp
    · have hz : z ∉ 𝒳 ∪ 𝒴 := fun hu ↦ hu.elim hx hy
      rw [swapFun_of_notMem hz, swapFun_of_notMem hz]

theorem swapFun_subset_swapFun_iff_left (h : IsSwappable 𝒳 𝒴 θ) (hA : A ∈ 𝒳) (hA' : A' ∈ 𝒳) :
    (swapFun 𝒳 𝒴 θ A : Set α) ⊆ swapFun 𝒳 𝒴 θ A' ↔ (A : Set α) ⊆ A' := by
  rw [swapFun_of_mem_left hA, swapFun_of_mem_left hA']
  exact h.map_subset_map_iff ⟨A, hA⟩ ⟨A', hA'⟩

theorem swapFun_subset_swapFun_iff_right (h : IsSwappable 𝒳 𝒴 θ) (hA : A ∈ 𝒴) (hA' : A' ∈ 𝒴) :
    (swapFun 𝒳 𝒴 θ A : Set α) ⊆ swapFun 𝒳 𝒴 θ A' ↔ (A : Set α) ⊆ A' := by
  rw [h.swapFun_of_mem_right hA, h.swapFun_of_mem_right hA']
  simpa using (h.map_subset_map_iff (θ.symm ⟨A, hA⟩) (θ.symm ⟨A', hA'⟩)).symm

/-- A set outside the blocks which is comparable to a member of the blocks is comparable to its
image. -/
theorem comparable_swapFun_of_notMem (h : IsSwappable 𝒳 𝒴 θ) (hz : z ∉ 𝒳 ∪ 𝒴)
    (hu : u ∈ 𝒳 ∪ 𝒴) (hc : (z : Set α) ⊆ u ∨ (u : Set α) ⊆ z) :
    (z : Set α) ⊆ swapFun 𝒳 𝒴 θ u ∨ (swapFun 𝒳 𝒴 θ u : Set α) ⊆ z := by
  have hψ := h.swapFun_mem_union hu
  rcases h.uniform_or_between z hz with hun | hbe
  · exact hc.imp (hun u hu _ hψ).1.1 (hun u hu _ hψ).2.1
  · rcases hψ with hx | hy
    · exact .inr (hbe.1 _ hx)
    · exact .inl (hbe.2 _ hy)

/-- The exchange of the blocks maps comparable sets to comparable sets. -/
theorem comparable_swapFun (h : IsSwappable 𝒳 𝒴 θ)
    (hc : (A : Set α) ⊆ A' ∨ (A' : Set α) ⊆ A) :
    (swapFun 𝒳 𝒴 θ A : Set α) ⊆ swapFun 𝒳 𝒴 θ A' ∨
      (swapFun 𝒳 𝒴 θ A' : Set α) ⊆ swapFun 𝒳 𝒴 θ A := by
  by_cases hA : A ∈ 𝒳 ∪ 𝒴 <;> by_cases hA' : A' ∈ 𝒳 ∪ 𝒴
  · rcases hA with hA | hA <;> rcases hA' with hA' | hA'
    · exact hc.imp (h.swapFun_subset_swapFun_iff_left hA hA').2
        (h.swapFun_subset_swapFun_iff_left hA' hA).2
    · exact .inr (h.ssubset _ (h.swapFun_mem_left hA') _ (swapFun_mem_right hA)).subset
    · exact .inl (h.ssubset _ (h.swapFun_mem_left hA) _ (swapFun_mem_right hA')).subset
    · exact hc.imp (h.swapFun_subset_swapFun_iff_right hA hA').2
        (h.swapFun_subset_swapFun_iff_right hA' hA).2
  · rw [swapFun_of_notMem hA']
    exact (h.comparable_swapFun_of_notMem hA' hA hc.symm).symm
  · rw [swapFun_of_notMem hA]
    exact h.comparable_swapFun_of_notMem hA hA' hc
  · rwa [swapFun_of_notMem hA, swapFun_of_notMem hA']

/-- The intersection of a member of the blocks with an incomparable set outside the blocks is
outside the blocks. -/
theorem notMem_of_coe_eq_inter (h : IsSwappable 𝒳 𝒴 θ) (hu : u ∈ 𝒳 ∪ 𝒴) (hz : z ∉ 𝒳 ∪ 𝒴)
    (huz : ¬(u : Set α) ⊆ z) (hzu : ¬(z : Set α) ⊆ u) (hC : (C : Set α) = u.1 ∩ z.1) :
    C ∉ 𝒳 ∪ 𝒴 := by
  intro hCU
  rcases h.uniform_or_between z hz with hun | hbe
  · exact huz ((hun C hCU u hu).2.1 (hC ▸ inter_subset_right))
  · exact hu.elim (fun hx ↦ huz (hbe.1 u hx)) fun hy ↦ hzu (hbe.2 u hy)

/-- The intersection of a member of the blocks with an incomparable set outside the blocks is
contained in the image of that member. -/
theorem inter_subset_swapFun [IsClosureSystem p] (h : IsSwappable 𝒳 𝒴 θ) (hu : u ∈ 𝒳 ∪ 𝒴)
    (hz : z ∉ 𝒳 ∪ 𝒴) (huz : ¬(u : Set α) ⊆ z) (hzu : ¬(z : Set α) ⊆ u) :
    u.1 ∩ z.1 ⊆ (swapFun 𝒳 𝒴 θ u : Set α) := by
  have hcU : ProperClosed.inter u z ∉ 𝒳 ∪ 𝒴 := h.notMem_of_coe_eq_inter hu hz huz hzu rfl
  have hψ := h.swapFun_mem_union hu
  rcases h.uniform_or_between _ hcU with hcun | hcbe
  · exact (hcun u hu _ hψ).1.1 inter_subset_left
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ 𝒳 :=
      hu.elim (fun hx ↦ ⟨u, hx⟩) fun hy ↦ ⟨_, h.swapFun_mem_left hy⟩
    have hxz : (x : Set α) ⊆ z := (hcbe.1 x hx).trans inter_subset_right
    rcases h.uniform_or_between z hz with hun | hbe
    · exact absurd ((hun x (.inl hx) u hu).2.1 hxz) huz
    · exact absurd (hu.elim (fun hx ↦ .inl (hbe.1 u hx)) fun hy ↦ .inr (hbe.2 u hy) :
        (u : Set α) ⊆ z ∨ (z : Set α) ⊆ u) (not_or.2 ⟨huz, hzu⟩)

/-- The intersection of a member of the blocks with an incomparable set outside the blocks does
not change when the member is replaced by its image. -/
theorem swapFun_inter_of_notMem [IsClosureSystem p] (h : IsSwappable 𝒳 𝒴 θ) (hu : u ∈ 𝒳 ∪ 𝒴)
    (hz : z ∉ 𝒳 ∪ 𝒴) (huz : ¬(u : Set α) ⊆ z) (hzu : ¬(z : Set α) ⊆ u) :
    (swapFun 𝒳 𝒴 θ u).1 ∩ z.1 = u.1 ∩ z.1 := by
  have hψ := h.swapFun_mem_union hu
  have hnc : ¬((z : Set α) ⊆ swapFun 𝒳 𝒴 θ u ∨ (swapFun 𝒳 𝒴 θ u : Set α) ⊆ z) := by
    intro hc
    have := h.comparable_swapFun_of_notMem hz hψ hc
    rw [h.involutive_swapFun u] at this
    exact this.elim hzu huz
  rw [not_or] at hnc
  refine Subset.antisymm (subset_inter ?_ inter_subset_right)
    (subset_inter (h.inter_subset_swapFun hu hz huz hzu) inter_subset_right)
  have := h.inter_subset_swapFun hψ hz hnc.2 hnc.1
  rwa [h.involutive_swapFun u] at this

/-- The exchange of the blocks maps the intersection of two incomparable sets to the
intersection of their images. -/
theorem coe_swapFun_eq_inter [IsClosureSystem p] (h : IsSwappable 𝒳 𝒴 θ)
    (hAA' : ¬(A : Set α) ⊆ A') (hA'A : ¬(A' : Set α) ⊆ A) (hC : (C : Set α) = A.1 ∩ A'.1) :
    (swapFun 𝒳 𝒴 θ C : Set α) = (swapFun 𝒳 𝒴 θ A).1 ∩ (swapFun 𝒳 𝒴 θ A').1 := by
  by_cases hA : A ∈ 𝒳 ∪ 𝒴 <;> by_cases hA' : A' ∈ 𝒳 ∪ 𝒴
  · rcases hA with hA | hA <;> rcases hA' with hA' | hA'
    · exact coe_map_eq_inter_of_blocks h.involutive_swapFun (fun _ ↦ swapFun_mem_right)
        (fun _ ↦ h.swapFun_mem_left) (fun _ hz _ hz' ↦ h.swapFun_subset_swapFun_iff_left hz hz')
        (fun _ hz _ hz' ↦ h.swapFun_subset_swapFun_iff_right hz hz') h.inter_mem_right hA hA'
        (h.inter_mem_left A hA A' hA' C hAA' hA'A hC) hAA' hA'A hC
    · exact absurd (h.ssubset A hA A' hA').subset hAA'
    · exact absurd (h.ssubset A' hA' A hA).subset hA'A
    · exact coe_map_eq_inter_of_blocks h.involutive_swapFun (fun _ ↦ h.swapFun_mem_left)
        (fun _ ↦ swapFun_mem_right) (fun _ hz _ hz' ↦ h.swapFun_subset_swapFun_iff_right hz hz')
        (fun _ hz _ hz' ↦ h.swapFun_subset_swapFun_iff_left hz hz') h.inter_mem_left hA hA'
        (h.inter_mem_right A hA A' hA' C hAA' hA'A hC) hAA' hA'A hC
  · rw [swapFun_of_notMem hA', swapFun_of_notMem (h.notMem_of_coe_eq_inter hA hA' hAA' hA'A hC),
      hC, h.swapFun_inter_of_notMem hA hA' hAA' hA'A]
  · rw [inter_comm] at hC
    rw [swapFun_of_notMem hA, swapFun_of_notMem (h.notMem_of_coe_eq_inter hA' hA hA'A hAA' hC),
      hC, inter_comm (A : Set α), h.swapFun_inter_of_notMem hA' hA hA'A hAA']
  · rw [swapFun_of_notMem hA, swapFun_of_notMem hA',
      swapFun_of_notMem (h.inter_notMem A hA A' hA' C hAA' hA'A hC), hC]

/-- The bijection of the proper closed sets which exchanges the blocks `𝒳` and `𝒴` along `θ`
and fixes all other proper closed sets. -/
noncomputable def swapEquiv (h : IsSwappable 𝒳 𝒴 θ) : Equiv.Perm (ProperClosed p) :=
  Function.Involutive.toPerm _ h.involutive_swapFun

@[simp]
theorem swapEquiv_apply (h : IsSwappable 𝒳 𝒴 θ) (z : ProperClosed p) :
    h.swapEquiv z = swapFun 𝒳 𝒴 θ z :=
  rfl

theorem swapEquiv_of_mem_left (h : IsSwappable 𝒳 𝒴 θ) (hx : z ∈ 𝒳) :
    h.swapEquiv z = θ ⟨z, hx⟩ :=
  swapFun_of_mem_left hx

theorem swapEquiv_of_mem_right (h : IsSwappable 𝒳 𝒴 θ) (hy : z ∈ 𝒴) :
    h.swapEquiv z = θ.symm ⟨z, hy⟩ :=
  h.swapFun_of_mem_right hy

theorem swapEquiv_of_notMem (h : IsSwappable 𝒳 𝒴 θ) (hz : z ∉ 𝒳 ∪ 𝒴) : h.swapEquiv z = z :=
  swapFun_of_notMem hz

/-- **Exchanging two blocks.** The bijection `swapEquiv` preserves comparability and
intersections of incomparable sets. -/
theorem isInterEquiv_swapEquiv [IsClosureSystem p] (h : IsSwappable 𝒳 𝒴 θ) :
    IsInterEquiv h.swapEquiv where
  comparable_iff A A' := by
    refine ⟨fun hc ↦ ?_, h.comparable_swapFun⟩
    have := h.comparable_swapFun hc
    simp only [swapEquiv_apply] at this
    rwa [h.involutive_swapFun A, h.involutive_swapFun A'] at this
  map_inter _ _ _ hAA' hA'A hC := h.coe_swapFun_eq_inter hAA' hA'A hC

/-- The bijection `swapEquiv` maps every member of `𝒳` to a strictly larger set … -/
theorem ssubset_swapEquiv (h : IsSwappable 𝒳 𝒴 θ) (hx : z ∈ 𝒳) :
    (z : Set α) ⊂ h.swapEquiv z :=
  h.ssubset z hx _ (swapFun_mem_right hx)

/-- … which it maps back to the smaller one. -/
theorem swapEquiv_swapEquiv (h : IsSwappable 𝒳 𝒴 θ) (z : ProperClosed p) :
    h.swapEquiv (h.swapEquiv z) = z :=
  h.involutive_swapFun z

/-- The bijection `swapEquiv` does not preserve inclusion, unless `𝒳` is empty. -/
theorem not_forall_subset_swapEquiv (h : IsSwappable 𝒳 𝒴 θ) (hne : 𝒳.Nonempty) :
    ¬∀ A A' : ProperClosed p, (A : Set α) ⊆ A' → (h.swapEquiv A : Set α) ⊆ h.swapEquiv A' := by
  obtain ⟨x, hx⟩ := hne
  intro hmono
  have := hmono x (h.swapEquiv x) (h.ssubset_swapEquiv hx).subset
  rw [h.swapEquiv_swapEquiv] at this
  exact (h.ssubset_swapEquiv hx).not_subset this

/-- The automorphism of the lattice of closure subsystems induced by exchanging two blocks of
closed sets. -/
noncomputable def swapOrderIso [IsClosureSystem p] [Finite α] (h : IsSwappable 𝒳 𝒴 θ) :
    ClosureSubsystem p ≃o ClosureSubsystem p :=
  ClosureSubsystem.orderIsoOfInterEquiv h.swapEquiv h.isInterEquiv_swapEquiv

/-- The automorphism `swapOrderIso` acts on the atoms by the bijection `swapEquiv`. -/
theorem properClosedEquivOfOrderIso_swapOrderIso [IsClosureSystem p] [Finite α]
    (h : IsSwappable 𝒳 𝒴 θ) :
    ClosureSubsystem.properClosedEquivOfOrderIso h.swapOrderIso = h.swapEquiv :=
  ClosureSubsystem.properClosedEquivOfOrderIso_orderIsoOfInterEquiv h.isInterEquiv_swapEquiv

/-- The automorphism `swapOrderIso` maps the closure system `{univ, A}` to
`{univ, swapEquiv A}`. -/
theorem swapOrderIso_pair [IsClosureSystem p] [Finite α] (h : IsSwappable 𝒳 𝒴 θ)
    (A : ProperClosed p) :
    h.swapOrderIso (ClosureSubsystem.pair A A.2.1) =
      ClosureSubsystem.pair (h.swapEquiv A : Set α) (h.swapEquiv A).2.1 :=
  ClosureSubsystem.orderIsoOfInterEquiv_pair h.isInterEquiv_swapEquiv A

/-- If `𝒳` is nonempty, the automorphism `swapOrderIso` of the lattice of closure subsystems is
not induced by an order automorphism of the closed sets: no order automorphism of the closed
sets acts on the proper closed sets as `swapEquiv`. -/
theorem not_exists_orderIso (h : IsSwappable 𝒳 𝒴 θ) (hne : 𝒳.Nonempty) :
    ¬∃ e : {A : Set α // p A} ≃o {A : Set α // p A},
      ∀ A : ProperClosed p, (e ⟨A, A.2.1⟩ : Set α) = h.swapEquiv A := by
  rintro ⟨e, he⟩
  refine h.not_forall_subset_swapEquiv hne fun A A' hAA' ↦ ?_
  rw [← he A, ← he A']
  exact e.monotone (show (⟨A, A.2.1⟩ : {A : Set α // p A}) ≤ ⟨A', A'.2.1⟩ from hAA')

end IsSwappable

/-- Two proper closed sets `A ⊂ B` which are comparable to all proper closed sets and are not
intersections of two incomparable proper closed sets can be exchanged. In a chain of closed
sets, any two proper closed sets can thus be exchanged. -/
theorem isSwappable_singleton [IsClosureSystem p] {A B : ProperClosed p}
    (hAB : (A : Set α) ⊂ B)
    (hA : ∀ z : ProperClosed p, (z : Set α) ⊆ A ∨ (A : Set α) ⊆ z)
    (hB : ∀ z : ProperClosed p, (z : Set α) ⊆ B ∨ (B : Set α) ⊆ z)
    (hA' : ∀ z z' : ProperClosed p, ¬(z : Set α) ⊆ z' → ¬(z' : Set α) ⊆ z →
      (A : Set α) ≠ z.1 ∩ z'.1)
    (hB' : ∀ z z' : ProperClosed p, ¬(z : Set α) ⊆ z' → ¬(z' : Set α) ⊆ z →
      (B : Set α) ≠ z.1 ∩ z'.1) :
    IsSwappable {A} {B} (Equiv.ofUnique _ _) where
  ssubset x hx y hy := by
    rw [mem_singleton_iff.1 hx, mem_singleton_iff.1 hy]
    exact hAB
  inter_mem_left x hx x' hx' _ hxx' := by
    rw [mem_singleton_iff.1 hx, mem_singleton_iff.1 hx'] at hxx'
    exact absurd Subset.rfl hxx'
  inter_mem_right y hy y' hy' _ hyy' := by
    rw [mem_singleton_iff.1 hy, mem_singleton_iff.1 hy'] at hyy'
    exact absurd Subset.rfl hyy'
  uniform_or_between z hz := by
    have hzA : z ≠ A := fun h ↦ hz (.inl h)
    have hzB : z ≠ B := fun h ↦ hz (.inr h)
    have key : ∀ u ∈ ({A} ∪ {B} : Set (ProperClosed p)), u = A ∨ u = B := fun u hu ↦ hu
    by_cases h₁ : (z : Set α) ⊆ A
    · -- `z` is below both
      have hlt : ∀ u ∈ ({A} ∪ {B} : Set (ProperClosed p)),
          (z : Set α) ⊆ u ∧ ¬(u : Set α) ⊆ z := by
        intro u hu
        rcases key u hu with rfl | rfl
        · exact ⟨h₁, fun h ↦ hzA (Subtype.ext (Subset.antisymm h₁ h))⟩
        · exact ⟨h₁.trans hAB.subset, fun h ↦ hAB.not_subset (h.trans h₁)⟩
      exact .inl fun u hu v hv ↦ ⟨iff_of_true (hlt u hu).1 (hlt v hv).1,
        iff_of_false (hlt u hu).2 (hlt v hv).2⟩
    · have h₂ : (A : Set α) ⊆ z := (hA z).resolve_left h₁
      by_cases h₃ : (z : Set α) ⊆ B
      · refine .inr ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
        · rwa [mem_singleton_iff.1 hx]
        · rwa [mem_singleton_iff.1 hy]
      · have h₄ : (B : Set α) ⊆ z := (hB z).resolve_left h₃
        have hgt : ∀ u ∈ ({A} ∪ {B} : Set (ProperClosed p)),
            ¬(z : Set α) ⊆ u ∧ (u : Set α) ⊆ z := by
          intro u hu
          rcases key u hu with rfl | rfl
          · exact ⟨h₁, h₂⟩
          · exact ⟨h₃, h₄⟩
        exact .inl fun u hu v hv ↦ ⟨iff_of_false (hgt u hu).1 (hgt v hv).1,
          iff_of_true (hgt u hu).2 (hgt v hv).2⟩
  inter_notMem z _ z' _ c hzz' hz'z hc hcU := by
    rcases hcU with hcA | hcB
    · exact hA' z z' hzz' hz'z (mem_singleton_iff.1 hcA ▸ hc)
    · exact hB' z z' hzz' hz'z (mem_singleton_iff.1 hcB ▸ hc)
  map_subset_map_iff x x' := by
    have hx : (x : ProperClosed p) = A := x.2
    have hx' : (x' : ProperClosed p) = A := x'.2
    have hy : ∀ y : ({B} : Set (ProperClosed p)), (y : ProperClosed p) = B := fun y ↦ y.2
    rw [hx, hx', hy, hy]
    exact iff_of_true Subset.rfl Subset.rfl

end FCA
