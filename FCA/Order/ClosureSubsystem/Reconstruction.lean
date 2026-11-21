/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Structure

/-!
# What the lattice of closure subsystems remembers

For a closure system `p` on a finite type, the lattice `ClosureSubsystem p` of closure systems
contained in `p` does not determine the lattice of closed sets of `p`. This file describes exactly
what it does determine: two such lattices are isomorphic if and only if there is a bijection
between the closed sets other than the whole set that preserves comparability and the
intersections of incomparable sets. This is due to Morgado, who calls such bijections
quasi-isomorphisms and treats complete lattices, and independently to Shevrin, in the form of a
description of the semilattices with isomorphic lattices of subsemilattices.

If every closed set of `p` is an intersection of maximal proper closed sets, such a bijection is
an order isomorphism, so that the lattice of closure subsystems determines the lattice of closed
sets. This is also due to Morgado, for all complete lattices.

## Main definitions

* `FCA.ProperClosed p`: the closed sets of `p` other than the whole set.
* `FCA.IsInterEquiv φ`: the bijection `φ` between proper closed sets preserves comparability and
  intersections of incomparable sets.
* `FCA.ClosureSubsystem.orderIsoOfInterEquiv`: the isomorphism of lattices of closure subsystems
  induced by such a bijection.
* `FCA.ClosureSubsystem.properClosedEquivOfOrderIso`: the bijection between proper closed sets
  induced by an isomorphism of lattices of closure subsystems, through its action on atoms.
* `FCA.IsClosedCoatom p`, `FCA.IsClosedCoatomistic p`: maximal proper closed sets, and closure
  systems all of whose closed sets are intersections of such.

## Main results

* `FCA.ClosureSubsystem.nonempty_orderIso_iff`: for finite types, `ClosureSubsystem p` and
  `ClosureSubsystem q` are isomorphic if and only if there is a bijection `φ` between the proper
  closed sets with `IsInterEquiv φ`.
* `FCA.IsInterEquiv.subset_iff`: for a coatomistic closure system on a finite type, such a
  bijection is an order embedding.
* `FCA.ClosureSubsystem.nonempty_closed_orderIso`: if `p` is a coatomistic closure system on a
  finite type and `ClosureSubsystem p` is isomorphic to `ClosureSubsystem q`, then the closed sets
  of `p` and `q` are order isomorphic.

## References

* [J. Morgado, *Quasi-isomorphisms between complete lattices*][morgado1961]
* [J. Morgado, *Some remarks on quasi-isomorphisms between finite lattices*][morgado1961b]
* [L. N. Shevrin, *Fundamental questions in the theory of projectivities of
  semilattices*][shevrin1965]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β : Type*} {p : Set α → Prop} {q : Set β → Prop}

/-- The closed sets of a closure system other than the whole set. -/
abbrev ProperClosed (p : Set α → Prop) : Type _ :=
  {A : Set α // p A ∧ A ≠ univ}

/-- A bijection between the proper closed sets of two closure systems that preserves
comparability and maps the intersection of two incomparable sets to the intersection of their
images. -/
structure IsInterEquiv (φ : ProperClosed p ≃ ProperClosed q) : Prop where
  /-- Two sets are comparable if and only if their images are. -/
  comparable_iff : ∀ A A' : ProperClosed p,
    ((φ A : Set β) ⊆ φ A' ∨ (φ A' : Set β) ⊆ φ A) ↔ ((A : Set α) ⊆ A' ∨ (A' : Set α) ⊆ A)
  /-- The intersection of two incomparable sets is mapped to the intersection of their images. -/
  map_inter : ∀ A A' C : ProperClosed p, ¬(A : Set α) ⊆ A' → ¬(A' : Set α) ⊆ A →
    (C : Set α) = A.1 ∩ A'.1 → (φ C : Set β) = (φ A).1 ∩ (φ A').1

namespace IsInterEquiv

variable {φ : ProperClosed p ≃ ProperClosed q}

/-- The inverse of an intersection-preserving bijection is intersection-preserving. -/
protected theorem symm [IsClosureSystem p] (h : IsInterEquiv φ) : IsInterEquiv φ.symm where
  comparable_iff B B' := by
    simpa using (h.comparable_iff (φ.symm B) (φ.symm B')).symm
  map_inter B B' D hB hB' hD := by
    have hc : ¬((φ.symm B : Set α) ⊆ φ.symm B' ∨ (φ.symm B' : Set α) ⊆ φ.symm B) := by
      rw [← h.comparable_iff]
      simpa using not_or.2 ⟨hB, hB'⟩
    rw [not_or] at hc
    let C : ProperClosed p := ⟨(φ.symm B).1 ∩ (φ.symm B').1,
      IsClosureSystem.inter_mem (φ.symm B).2.1 (φ.symm B').2.1,
      fun hu ↦ (φ.symm B).2.2 (univ_subset_iff.1 (hu.symm.subset.trans inter_subset_left))⟩
    have hC := h.map_inter _ _ C hc.1 hc.2 rfl
    simp only [Equiv.apply_symm_apply] at hC
    have hCD : φ C = D := Subtype.ext (hC.trans hD.symm)
    rw [← hCD, Equiv.symm_apply_apply]

private theorem comparable_of_imp [IsClosureSystem q] (ψ : ProperClosed p ≃ ProperClosed q)
    (H : ∀ A A' C : ProperClosed p,
      ((ψ C : Set β) = ψ A ∨ (ψ C : Set β) = ψ A' ∨ (ψ C : Set β) = (ψ A).1 ∩ (ψ A').1) →
        ((C : Set α) = A ∨ (C : Set α) = A' ∨ (C : Set α) = A.1 ∩ A'.1))
    {A A' : ProperClosed p} (hc : (A : Set α) ⊆ A' ∨ (A' : Set α) ⊆ A) :
    (ψ A : Set β) ⊆ ψ A' ∨ (ψ A' : Set β) ⊆ ψ A := by
  let D : ProperClosed q := ⟨(ψ A).1 ∩ (ψ A').1, IsClosureSystem.inter_mem (ψ A).2.1 (ψ A').2.1,
    fun hu ↦ (ψ A).2.2 (univ_subset_iff.1 (hu.symm.subset.trans inter_subset_left))⟩
  have hD := H A A' (ψ.symm D) (by simp [D])
  have hD' : (ψ.symm D : Set α) = A ∨ (ψ.symm D : Set α) = A' := by
    rcases hD with h | h | h
    · exact .inl h
    · exact .inr h
    · rcases hc with hc | hc
      · exact .inl (h.trans (inter_eq_left.2 hc))
      · exact .inr (h.trans (inter_eq_right.2 hc))
  rcases hD' with h | h
  · have h' : D = ψ A := by
      rw [← (Subtype.ext h : ψ.symm D = A), Equiv.apply_symm_apply]
    exact .inl (inter_eq_left.1 (congrArg Subtype.val h'))
  · have h' : D = ψ A' := by
      rw [← (Subtype.ext h : ψ.symm D = A'), Equiv.apply_symm_apply]
    exact .inr (inter_eq_right.1 (congrArg Subtype.val h'))

/-- A bijection `φ` between proper closed sets is intersection-preserving as soon as, for all
`A`, `A'` and `C`, the set `C` is one of `A`, `A'`, `A ∩ A'` if and only if `φ C` is one of
`φ A`, `φ A'`, `φ A ∩ φ A'`. -/
theorem of_mem_iff [IsClosureSystem p] [IsClosureSystem q]
    (H : ∀ A A' C : ProperClosed p,
      ((C : Set α) = A ∨ (C : Set α) = A' ∨ (C : Set α) = A.1 ∩ A'.1) ↔
        ((φ C : Set β) = φ A ∨ (φ C : Set β) = φ A' ∨ (φ C : Set β) = (φ A).1 ∩ (φ A').1)) :
    IsInterEquiv φ where
  comparable_iff A A' := by
    refine ⟨fun hc ↦ ?_, comparable_of_imp φ fun A A' C ↦ (H A A' C).2⟩
    simpa using comparable_of_imp φ.symm
      (fun B B' D ↦ by simpa using (H (φ.symm B) (φ.symm B') (φ.symm D)).1) hc
  map_inter A A' C hA hA' hC := by
    rcases (H A A' C).1 (.inr (.inr hC)) with h | h | h
    · have h' : C = A := φ.injective (Subtype.ext h)
      exact absurd (inter_eq_left.1 (hC.symm.trans (congrArg Subtype.val h'))) hA
    · have h' : C = A' := φ.injective (Subtype.ext h)
      exact absurd (inter_eq_right.1 (hC.symm.trans (congrArg Subtype.val h'))) hA'
    · exact h

end IsInterEquiv

namespace ClosureSubsystem

/-! ### From a bijection of closed sets to an isomorphism of lattices -/

/-- On a finite type, a family of closed sets that contains the whole set and is closed under
binary intersections is a closure system. -/
def ofInterMem [Finite α] (C : Set (Set α)) (huniv : univ ∈ C)
    (hinter : ∀ A ∈ C, ∀ B ∈ C, A ∩ B ∈ C) (hp : ∀ A ∈ C, p A) : ClosureSubsystem p where
  carrier := C
  sInter_mem' S hS := by
    induction S, S.toFinite using Set.Finite.induction_on with
    | empty => simpa using huniv
    | insert _ _ ih =>
      rw [sInter_insert]
      exact hinter _ (hS (mem_insert _ _)) _ (ih ((subset_insert _ _).trans hS))
  isClosed' := hp

variable [IsClosureSystem p] [IsClosureSystem q] {φ : ProperClosed p ≃ ProperClosed q}
  {𝒜 ℬ : ClosureSubsystem p}

/-- The image of a closure system under an intersection-preserving bijection of proper closed
sets. -/
def mapInterEquiv [Finite β] (φ : ProperClosed p ≃ ProperClosed q) (h : IsInterEquiv φ)
    (𝒜 : ClosureSubsystem p) : ClosureSubsystem q :=
  ofInterMem {B | B = univ ∨ ∃ A : ProperClosed p, (A : Set α) ∈ 𝒜 ∧ (φ A : Set β) = B}
    (.inl rfl)
    (by
      rintro _ (rfl | ⟨A, hA, rfl⟩) _ (rfl | ⟨A', hA', rfl⟩)
      · exact .inl (inter_self _)
      · rw [univ_inter]
        exact .inr ⟨A', hA', rfl⟩
      · rw [inter_univ]
        exact .inr ⟨A, hA, rfl⟩
      · by_cases hc : (A : Set α) ⊆ A' ∨ (A' : Set α) ⊆ A
        · rcases (h.comparable_iff A A').2 hc with h' | h'
          · rw [inter_eq_left.2 h']
            exact .inr ⟨A, hA, rfl⟩
          · rw [inter_eq_right.2 h']
            exact .inr ⟨A', hA', rfl⟩
        · rw [not_or] at hc
          exact .inr ⟨⟨A.1 ∩ A'.1, IsClosureSystem.inter_mem A.2.1 A'.2.1,
            fun hu ↦ A.2.2 (univ_subset_iff.1 (hu.symm.subset.trans inter_subset_left))⟩,
            𝒜.inter_mem hA hA', h.map_inter _ _ _ hc.1 hc.2 rfl⟩)
    (by
      rintro _ (rfl | ⟨A, -, rfl⟩)
      exacts [IsClosureSystem.univ_mem, (φ A).2.1])

theorem mem_mapInterEquiv [Finite β] {h : IsInterEquiv φ} {B : Set β} :
    B ∈ mapInterEquiv φ h 𝒜 ↔
      B = univ ∨ ∃ A : ProperClosed p, (A : Set α) ∈ 𝒜 ∧ (φ A : Set β) = B :=
  Iff.rfl

@[simp]
theorem coe_mem_mapInterEquiv [Finite β] {h : IsInterEquiv φ} {A : ProperClosed p} :
    (φ A : Set β) ∈ mapInterEquiv φ h 𝒜 ↔ (A : Set α) ∈ 𝒜 := by
  refine ⟨fun hA ↦ ?_, fun hA ↦ .inr ⟨A, hA, rfl⟩⟩
  rcases hA with hA | ⟨A', hA', hAA'⟩
  · exact absurd hA (φ A).2.2
  · rwa [← φ.injective (Subtype.ext hAA')]

theorem mapInterEquiv_symm_mapInterEquiv [Finite α] [Finite β] (h : IsInterEquiv φ)
    (𝒜 : ClosureSubsystem p) : mapInterEquiv φ.symm h.symm (mapInterEquiv φ h 𝒜) = 𝒜 := by
  refine ClosureSubsystem.ext (Set.ext fun C ↦ ⟨?_, fun hC ↦ ?_⟩)
  · rintro (rfl | ⟨B, hB, rfl⟩)
    · exact 𝒜.univ_mem
    · rw [← φ.apply_symm_apply B] at hB
      exact coe_mem_mapInterEquiv.1 hB
  · by_cases hu : C = univ
    · exact .inl hu
    · exact .inr ⟨φ ⟨C, 𝒜.isClosed hC, hu⟩, coe_mem_mapInterEquiv.2 hC, by simp⟩

theorem mapInterEquiv_le_mapInterEquiv_iff [Finite β] {h : IsInterEquiv φ} :
    mapInterEquiv φ h 𝒜 ≤ mapInterEquiv φ h ℬ ↔ 𝒜 ≤ ℬ := by
  refine ⟨fun hle ↦ le_def.2 fun A hA ↦ ?_, fun hle ↦ le_def.2 ?_⟩
  · by_cases hu : A = univ
    · exact hu ▸ ℬ.univ_mem
    · exact (coe_mem_mapInterEquiv (A := ⟨A, 𝒜.isClosed hA, hu⟩)).1
        (le_def.1 hle (coe_mem_mapInterEquiv.2 hA))
  · rintro _ (rfl | ⟨A, hA, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨A, le_def.1 hle hA, rfl⟩

/-- An intersection-preserving bijection between the proper closed sets of two closure systems
on finite types induces an isomorphism between their lattices of closure subsystems. -/
def orderIsoOfInterEquiv [Finite α] [Finite β] (φ : ProperClosed p ≃ ProperClosed q)
    (h : IsInterEquiv φ) : ClosureSubsystem p ≃o ClosureSubsystem q where
  toFun := mapInterEquiv φ h
  invFun := mapInterEquiv φ.symm h.symm
  left_inv := mapInterEquiv_symm_mapInterEquiv h
  right_inv := mapInterEquiv_symm_mapInterEquiv h.symm
  map_rel_iff' := mapInterEquiv_le_mapInterEquiv_iff (h := h)

@[simp]
theorem coe_mem_orderIsoOfInterEquiv [Finite α] [Finite β] {h : IsInterEquiv φ}
    {A : ProperClosed p} : (φ A : Set β) ∈ orderIsoOfInterEquiv φ h 𝒜 ↔ (A : Set α) ∈ 𝒜 :=
  coe_mem_mapInterEquiv (h := h)

/-- The isomorphism induced by `φ` maps the atom `{G, A}` to the atom `{G, φ A}`. -/
theorem orderIsoOfInterEquiv_pair [Finite α] [Finite β] (h : IsInterEquiv φ)
    (A : ProperClosed p) :
    orderIsoOfInterEquiv φ h (pair A A.2.1) = pair (φ A : Set β) (φ A).2.1 := by
  refine le_antisymm (le_def.2 ?_) (pair_le_iff.2 (coe_mem_orderIsoOfInterEquiv.2 self_mem_pair))
  intro B hB
  obtain rfl | ⟨A', hA', rfl⟩ := (mem_mapInterEquiv (h := h)).1 hB
  · exact .inl rfl
  · rcases hA' with hA' | hA'
    · exact absurd hA' A'.2.2
    · rw [Subtype.ext hA']
      exact self_mem_pair

/-! ### From an isomorphism of lattices to a bijection of closed sets -/

/-- The proper closed sets correspond to the atoms of the lattice of closure subsystems. -/
noncomputable def properClosedEquivAtoms (p : Set α → Prop) [IsClosureSystem p] :
    ProperClosed p ≃ {𝒜 : ClosureSubsystem p // IsAtom 𝒜} :=
  Equiv.ofBijective (fun A ↦ ⟨pair A A.2.1, isAtom_pair A.2.2⟩) <| by
    refine ⟨fun A B h ↦ Subtype.ext ?_, ?_⟩
    · have hAB : (A : Set α) ∈ pair (B : Set α) B.2.1 := by
        have h' : pair (A : Set α) A.2.1 = pair (B : Set α) B.2.1 := congrArg Subtype.val h
        rw [← h']
        exact self_mem_pair
      exact (mem_pair.1 hAB).resolve_left A.2.2
    · rintro ⟨𝒜, h𝒜⟩
      obtain ⟨A, hA, hu, rfl⟩ := isAtom_iff.1 h𝒜
      exact ⟨⟨A, hA, hu⟩, rfl⟩

@[simp]
theorem coe_properClosedEquivAtoms (A : ProperClosed p) :
    (properClosedEquivAtoms p A : ClosureSubsystem p) = pair A A.2.1 :=
  rfl

/-- The bijection between proper closed sets induced by an isomorphism of lattices of closure
subsystems, which maps atoms to atoms. -/
noncomputable def properClosedEquivOfOrderIso (e : ClosureSubsystem p ≃o ClosureSubsystem q) :
    ProperClosed p ≃ ProperClosed q :=
  (properClosedEquivAtoms p).trans <|
    (e.toEquiv.subtypeEquiv fun 𝒜 ↦ (e.isAtom_iff 𝒜).symm).trans (properClosedEquivAtoms q).symm

/-- An isomorphism `e` maps the atom `{G, A}` to the atom `{G, φ A}` for the induced bijection
`φ`. -/
theorem pair_properClosedEquivOfOrderIso (e : ClosureSubsystem p ≃o ClosureSubsystem q)
    (A : ProperClosed p) :
    pair (properClosedEquivOfOrderIso e A : Set β) (properClosedEquivOfOrderIso e A).2.1 =
      e (pair A A.2.1) :=
  congrArg Subtype.val ((properClosedEquivAtoms q).apply_symm_apply
    ((e.toEquiv.subtypeEquiv fun 𝒜 ↦ (e.isAtom_iff 𝒜).symm) (properClosedEquivAtoms p A)))

/-- The join of two atoms `{G, A}` and `{G, A'}` is `{G, A, A', A ∩ A'}`. -/
theorem mem_pair_sup_pair {A A' C : Set α} {hA : p A} {hA' : p A'} :
    C ∈ pair A hA ⊔ pair A' hA' ↔ C = univ ∨ C = A ∨ C = A' ∨ C = A ∩ A' := by
  rw [mem_sup]
  constructor
  · rintro ⟨_, (rfl | rfl), _, (rfl | rfl), rfl⟩ <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨univ, univ_mem _, univ, univ_mem _, inter_self _⟩
    · exact ⟨C, self_mem_pair, univ, univ_mem _, inter_univ _⟩
    · exact ⟨univ, univ_mem _, C, self_mem_pair, univ_inter _⟩
    · exact ⟨A, self_mem_pair, A', self_mem_pair, rfl⟩

theorem pair_le_pair_sup_pair_iff (A A' C : ProperClosed p) :
    pair (C : Set α) C.2.1 ≤ pair (A : Set α) A.2.1 ⊔ pair (A' : Set α) A'.2.1 ↔
      (C : Set α) = A ∨ (C : Set α) = A' ∨ (C : Set α) = A.1 ∩ A'.1 := by
  rw [pair_le_iff, mem_pair_sup_pair, or_iff_right C.2.2]

/-- The bijection induced by an isomorphism of lattices of closure subsystems preserves
comparability and intersections of incomparable sets. -/
theorem isInterEquiv_properClosedEquivOfOrderIso (e : ClosureSubsystem p ≃o ClosureSubsystem q) :
    IsInterEquiv (properClosedEquivOfOrderIso e) :=
  .of_mem_iff fun A A' C ↦ by
    rw [← pair_le_pair_sup_pair_iff, ← pair_le_pair_sup_pair_iff,
      pair_properClosedEquivOfOrderIso, pair_properClosedEquivOfOrderIso,
      pair_properClosedEquivOfOrderIso, ← map_sup, e.le_iff_le]

/-- **The lattice of closure subsystems as an invariant.** For closure systems on finite types,
the lattices of closure subsystems are isomorphic if and only if there is a bijection between
the proper closed sets that preserves comparability and intersections of incomparable sets. -/
theorem nonempty_orderIso_iff [Finite α] [Finite β] :
    Nonempty (ClosureSubsystem p ≃o ClosureSubsystem q) ↔
      ∃ φ : ProperClosed p ≃ ProperClosed q, IsInterEquiv φ :=
  ⟨fun ⟨e⟩ ↦ ⟨_, isInterEquiv_properClosedEquivOfOrderIso e⟩,
    fun ⟨φ, h⟩ ↦ ⟨orderIsoOfInterEquiv φ h⟩⟩

/-- The bijection induced by the isomorphism induced by `φ` is `φ`. -/
theorem properClosedEquivOfOrderIso_orderIsoOfInterEquiv [Finite α] [Finite β]
    (h : IsInterEquiv φ) : properClosedEquivOfOrderIso (orderIsoOfInterEquiv φ h) = φ := by
  refine Equiv.ext fun A ↦ (properClosedEquivAtoms q).injective (Subtype.ext ?_)
  rw [coe_properClosedEquivAtoms, pair_properClosedEquivOfOrderIso, orderIsoOfInterEquiv_pair,
    coe_properClosedEquivAtoms]

end ClosureSubsystem

/-! ### Coatomistic closure systems -/

/-- A maximal proper closed set. -/
def IsClosedCoatom (p : Set α → Prop) (C : Set α) : Prop :=
  p C ∧ C ≠ univ ∧ ∀ D, p D → C ⊆ D → D = C ∨ D = univ

/-- A closure system is coatomistic if every closed set is an intersection of maximal proper
closed sets. -/
def IsClosedCoatomistic (p : Set α → Prop) : Prop :=
  ∀ A, p A → ∃ S : Set (Set α), (∀ C ∈ S, IsClosedCoatom p C) ∧ ⋂₀ S = A

namespace IsInterEquiv

variable [IsClosureSystem p] {φ : ProperClosed p ≃ ProperClosed q}

omit [IsClosureSystem p] in
theorem subset_of_eq_inter_isClosedCoatom (h : IsInterEquiv φ) {X Y : ProperClosed p}
    {C : Set α} (hC : IsClosedCoatom p C) (hY : (Y : Set α) = X.1 ∩ C) :
    (φ Y : Set β) ⊆ φ X := by
  by_cases hXC : (X : Set α) ⊆ C
  · have hYX : Y = X := Subtype.ext (hY.trans (inter_eq_left.2 hXC))
    rw [hYX]
  by_cases hCX : C ⊆ (X : Set α)
  · rcases hC.2.2 X X.2.1 hCX with hX | hX
    · exact absurd hX.le hXC
    · exact absurd hX X.2.2
  · rw [h.map_inter X ⟨C, hC.1, hC.2.1⟩ Y hXC hCX hY]
    exact inter_subset_left

theorem subset_of_eq_inter_sInter (h : IsInterEquiv φ) {S : Set (Set α)} (hS : S.Finite)
    (hS' : ∀ C ∈ S, IsClosedCoatom p C) {X Y : ProperClosed p}
    (hY : (Y : Set α) = X.1 ∩ ⋂₀ S) : (φ Y : Set β) ⊆ φ X := by
  induction S, hS using Set.Finite.induction_on generalizing X Y with
  | empty =>
    have hYX : Y = X := Subtype.ext (by simpa using hY)
    rw [hYX]
  | @insert C S _ _ ih =>
    have hC := hS' C (mem_insert _ _)
    let Z : ProperClosed p := ⟨X.1 ∩ C, IsClosureSystem.inter_mem X.2.1 hC.1,
      fun hu ↦ X.2.2 (univ_subset_iff.1 (hu.symm.subset.trans inter_subset_left))⟩
    have hYZ : (Y : Set α) = Z.1 ∩ ⋂₀ S := by
      rw [hY, sInter_insert, inter_assoc]
    exact (ih (fun C hC ↦ hS' C (mem_insert_of_mem _ hC)) hYZ).trans
      (h.subset_of_eq_inter_isClosedCoatom hC rfl)

/-- For a coatomistic closure system on a finite type, an intersection-preserving bijection of
proper closed sets is monotone. -/
theorem subset_of_subset [Finite α] (h : IsInterEquiv φ) (hp : IsClosedCoatomistic p)
    {A B : ProperClosed p} (hAB : (A : Set α) ⊆ B) : (φ A : Set β) ⊆ φ B := by
  obtain ⟨S, hS, hSA⟩ := hp A A.2.1
  exact h.subset_of_eq_inter_sInter S.toFinite hS (by rw [hSA, inter_eq_right.2 hAB])

/-- For a coatomistic closure system on a finite type, an intersection-preserving bijection of
proper closed sets is an order embedding. -/
theorem subset_iff [Finite α] (h : IsInterEquiv φ) (hp : IsClosedCoatomistic p)
    {A B : ProperClosed p} : (φ A : Set β) ⊆ φ B ↔ (A : Set α) ⊆ B := by
  refine ⟨fun hAB ↦ ?_, h.subset_of_subset hp⟩
  rcases (h.comparable_iff A B).1 (.inl hAB) with h' | h'
  · exact h'
  · have h'' : φ A = φ B := Subtype.ext (hAB.antisymm (h.subset_of_subset hp h'))
    exact (congrArg Subtype.val (φ.injective h'')).le

end IsInterEquiv

namespace ClosureSubsystem

variable [IsClosureSystem p] [IsClosureSystem q]

open Classical in
/-- The extension of a bijection between proper closed sets to all closed sets, mapping the
whole set to the whole set. -/
noncomputable def closedEquiv (φ : ProperClosed p ≃ ProperClosed q) :
    {A // p A} ≃ {B // q B} where
  toFun A := if h : A.1 = univ then ⟨univ, IsClosureSystem.univ_mem⟩
    else ⟨φ ⟨A.1, A.2, h⟩, (φ ⟨A.1, A.2, h⟩).2.1⟩
  invFun B := if h : B.1 = univ then ⟨univ, IsClosureSystem.univ_mem⟩
    else ⟨φ.symm ⟨B.1, B.2, h⟩, (φ.symm ⟨B.1, B.2, h⟩).2.1⟩
  left_inv A := by
    by_cases h : A.1 = univ
    · simpa [h] using Subtype.ext h.symm
    · simp [h, (φ ⟨A.1, A.2, h⟩).2.2]
  right_inv B := by
    by_cases h : B.1 = univ
    · simpa [h] using Subtype.ext h.symm
    · simp [h, (φ.symm ⟨B.1, B.2, h⟩).2.2]

theorem closedEquiv_of_eq_univ (φ : ProperClosed p ≃ ProperClosed q) {A : {A // p A}}
    (h : A.1 = univ) : (closedEquiv φ A : Set β) = univ := by
  simp [closedEquiv, h]

theorem closedEquiv_of_ne_univ (φ : ProperClosed p ≃ ProperClosed q) {A : {A // p A}}
    (h : A.1 ≠ univ) : (closedEquiv φ A : Set β) = φ ⟨A.1, A.2, h⟩ := by
  simp [closedEquiv, h]

/-- A bijection between proper closed sets that is an order embedding extends to an order
isomorphism between all closed sets. -/
noncomputable def closedOrderIso (φ : ProperClosed p ≃ ProperClosed q)
    (hφ : ∀ A B : ProperClosed p, (φ A : Set β) ⊆ φ B ↔ (A : Set α) ⊆ B) :
    {A // p A} ≃o {B // q B} where
  toEquiv := closedEquiv φ
  map_rel_iff' {A B} := by
    change (closedEquiv φ A : Set β) ⊆ closedEquiv φ B ↔ A.1 ⊆ B.1
    by_cases hB : B.1 = univ
    · simp [closedEquiv_of_eq_univ φ hB, hB]
    by_cases hA : A.1 = univ
    · rw [closedEquiv_of_eq_univ φ hA, closedEquiv_of_ne_univ φ hB, hA, univ_subset_iff,
        univ_subset_iff]
      exact iff_of_false (φ _).2.2 hB
    · rw [closedEquiv_of_ne_univ φ hA, closedEquiv_of_ne_univ φ hB]
      exact hφ _ _

/-- **Reconstruction for coatomistic closure systems.** If every closed set of a closure system
`p` on a finite type is an intersection of maximal proper closed sets, then the lattice of
closure subsystems of `p` determines the closed sets of `p` up to order isomorphism. -/
theorem nonempty_closed_orderIso [Finite α] (hp : IsClosedCoatomistic p)
    (e : ClosureSubsystem p ≃o ClosureSubsystem q) : Nonempty ({A // p A} ≃o {B // q B}) :=
  ⟨closedOrderIso (properClosedEquivOfOrderIso e) fun _ _ ↦
    (isInterEquiv_properClosedEquivOfOrderIso e).subset_iff hp⟩

end ClosureSubsystem

end FCA
