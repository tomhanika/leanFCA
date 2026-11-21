/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.Cover
public import Mathlib.Order.Heyting.Basic

/-!
# Semidistributive, pseudocomplemented and meet-distributive lattices

This file defines three weakenings of distributivity for lattices, none of which is in Mathlib.

## Main definitions

* `FCA.IsJoinSemidistrib`, `FCA.IsMeetSemidistrib`: a lattice is *join-semidistributive* if
  `a ⊔ b = a ⊔ c` implies `a ⊔ b = a ⊔ b ⊓ c`, and *meet-semidistributive* dually.
* `FCA.IsJoinPseudocompl a c`, `FCA.IsMeetPseudocompl a c`: `c` is the least element whose join
  with `a` is `⊤`, respectively the greatest element whose meet with `a` is `⊥`.
* `FCA.IsJoinPseudocomplemented`, `FCA.IsMeetPseudocomplemented`: every element has a
  join-pseudocomplement, respectively a meet-pseudocomplement.
* `FCA.lowerCore b`: the meet of `b` with all its lower covers.
* `FCA.IsMeetDistrib`: a complete lattice is *meet-distributive* (lower locally distributive) if
  every interval `[lowerCore b, b]` is a Boolean lattice.

## Main results

* Distributive lattices are join- and meet-semidistributive; the two notions are dual.
* Co-Heyting algebras are join-pseudocomplemented, Heyting algebras meet-pseudocomplemented.
* `FCA.isJoinPseudocomplemented_of_finite`: a finite join-semidistributive lattice with a
  greatest element is join-pseudocomplemented, and dually.
* `FCA.IsMeetDistrib.of_orderIso`: a complete lattice is meet-distributive as soon as every
  interval `[lowerCore b, b]` is order isomorphic to a powerset.

## References

* [N. Caspard, B. Monjardet, *The lattices of closure systems, closure operators, and
  implicational systems on a finite set: a survey*][caspard2003]
-/

@[expose] public section

open Set Order

namespace FCA

variable {α : Type*}

/-! ### Semidistributivity -/

/-- A lattice is *join-semidistributive* if `a ⊔ b = a ⊔ c` implies `a ⊔ b = a ⊔ b ⊓ c`. -/
class IsJoinSemidistrib (α : Type*) [Lattice α] : Prop where
  /-- `a ⊔ b = a ⊔ c` implies `a ⊔ b = a ⊔ b ⊓ c`. -/
  sup_eq_sup_inf_of_sup_eq_sup : ∀ ⦃a b c : α⦄, a ⊔ b = a ⊔ c → a ⊔ b = a ⊔ b ⊓ c

/-- A lattice is *meet-semidistributive* if `a ⊓ b = a ⊓ c` implies `a ⊓ b = a ⊓ (b ⊔ c)`. -/
class IsMeetSemidistrib (α : Type*) [Lattice α] : Prop where
  /-- `a ⊓ b = a ⊓ c` implies `a ⊓ b = a ⊓ (b ⊔ c)`. -/
  inf_eq_inf_sup_of_inf_eq_inf : ∀ ⦃a b c : α⦄, a ⊓ b = a ⊓ c → a ⊓ b = a ⊓ (b ⊔ c)

theorem sup_eq_sup_inf_of_sup_eq_sup [Lattice α] [IsJoinSemidistrib α] {a b c : α}
    (h : a ⊔ b = a ⊔ c) : a ⊔ b = a ⊔ b ⊓ c :=
  IsJoinSemidistrib.sup_eq_sup_inf_of_sup_eq_sup h

theorem inf_eq_inf_sup_of_inf_eq_inf [Lattice α] [IsMeetSemidistrib α] {a b c : α}
    (h : a ⊓ b = a ⊓ c) : a ⊓ b = a ⊓ (b ⊔ c) :=
  IsMeetSemidistrib.inf_eq_inf_sup_of_inf_eq_inf h

instance (priority := 100) [DistribLattice α] : IsJoinSemidistrib α :=
  ⟨fun a b c h ↦ by rw [sup_inf_left, ← h, inf_idem]⟩

instance (priority := 100) [DistribLattice α] : IsMeetSemidistrib α :=
  ⟨fun a b c h ↦ by rw [inf_sup_left, ← h, sup_idem]⟩

instance [Lattice α] [IsMeetSemidistrib α] : IsJoinSemidistrib αᵒᵈ :=
  ⟨fun _ _ _ h ↦ inf_eq_inf_sup_of_inf_eq_inf (α := α) h⟩

instance [Lattice α] [IsJoinSemidistrib α] : IsMeetSemidistrib αᵒᵈ :=
  ⟨fun _ _ _ h ↦ sup_eq_sup_inf_of_sup_eq_sup (α := α) h⟩

/-- Semidistributivity is invariant under order isomorphisms. -/
theorem IsJoinSemidistrib.of_orderIso {β : Type*} [Lattice α] [Lattice β] [IsJoinSemidistrib α]
    (e : α ≃o β) : IsJoinSemidistrib β where
  sup_eq_sup_inf_of_sup_eq_sup a b c h := by
    have h' : e.symm a ⊔ e.symm b = e.symm a ⊔ e.symm c := by
      rw [← e.symm.map_sup, ← e.symm.map_sup, h]
    have := congrArg e (sup_eq_sup_inf_of_sup_eq_sup h')
    simpa [e.map_sup, e.map_inf] using this

/-- Semidistributivity is invariant under order isomorphisms. -/
theorem IsMeetSemidistrib.of_orderIso {β : Type*} [Lattice α] [Lattice β] [IsMeetSemidistrib α]
    (e : α ≃o β) : IsMeetSemidistrib β where
  inf_eq_inf_sup_of_inf_eq_inf a b c h := by
    have h' : e.symm a ⊓ e.symm b = e.symm a ⊓ e.symm c := by
      rw [← e.symm.map_inf, ← e.symm.map_inf, h]
    have := congrArg e (inf_eq_inf_sup_of_inf_eq_inf h')
    simpa [e.map_sup, e.map_inf] using this

/-! ### Pseudocomplements -/

/-- `c` is the *join-pseudocomplement* of `a`: the least element whose join with `a` is `⊤`. -/
def IsJoinPseudocompl [Lattice α] [OrderTop α] (a c : α) : Prop :=
  IsLeast {b | a ⊔ b = ⊤} c

/-- `c` is the *meet-pseudocomplement* of `a`: the greatest element whose meet with `a` is
`⊥`. -/
def IsMeetPseudocompl [Lattice α] [OrderBot α] (a c : α) : Prop :=
  IsGreatest {b | a ⊓ b = ⊥} c

section JoinPseudocompl

variable [Lattice α] [OrderTop α] {a b c : α}

theorem IsJoinPseudocompl.sup_eq_top (h : IsJoinPseudocompl a c) : a ⊔ c = ⊤ :=
  h.1

theorem IsJoinPseudocompl.le_iff (h : IsJoinPseudocompl a c) : c ≤ b ↔ a ⊔ b = ⊤ :=
  ⟨fun hcb ↦ top_unique (h.1 ▸ sup_le_sup_left hcb a), fun hb ↦ h.2 hb⟩

theorem IsJoinPseudocompl.unique {c' : α} (h : IsJoinPseudocompl a c)
    (h' : IsJoinPseudocompl a c') : c = c' :=
  IsLeast.unique h h'

/-- A lattice with a greatest element is *join-pseudocomplemented* if every element has a
join-pseudocomplement. -/
class IsJoinPseudocomplemented (α : Type*) [Lattice α] [OrderTop α] : Prop where
  /-- Every element has a join-pseudocomplement. -/
  exists_isJoinPseudocompl : ∀ a : α, ∃ c, IsJoinPseudocompl a c

end JoinPseudocompl

section MeetPseudocompl

variable [Lattice α] [OrderBot α] {a b c : α}

theorem IsMeetPseudocompl.inf_eq_bot (h : IsMeetPseudocompl a c) : a ⊓ c = ⊥ :=
  h.1

theorem IsMeetPseudocompl.le_iff (h : IsMeetPseudocompl a c) : b ≤ c ↔ a ⊓ b = ⊥ :=
  ⟨fun hbc ↦ bot_unique (h.1 ▸ inf_le_inf_left a hbc), fun hb ↦ h.2 hb⟩

theorem IsMeetPseudocompl.unique {c' : α} (h : IsMeetPseudocompl a c)
    (h' : IsMeetPseudocompl a c') : c = c' :=
  IsGreatest.unique h h'

/-- A lattice with a least element is *meet-pseudocomplemented* if every element has a
meet-pseudocomplement. -/
class IsMeetPseudocomplemented (α : Type*) [Lattice α] [OrderBot α] : Prop where
  /-- Every element has a meet-pseudocomplement. -/
  exists_isMeetPseudocompl : ∀ a : α, ∃ c, IsMeetPseudocompl a c

end MeetPseudocompl

/-- In a Heyting algebra the complement is the meet-pseudocomplement. -/
theorem isMeetPseudocompl_compl [HeytingAlgebra α] (a : α) : IsMeetPseudocompl a aᶜ :=
  ⟨inf_compl_self a, fun b hb ↦ le_compl_iff_disjoint_right.2 (disjoint_iff.2 (inf_comm b a ▸ hb))⟩

instance (priority := 100) [HeytingAlgebra α] : IsMeetPseudocomplemented α :=
  ⟨fun a ↦ ⟨aᶜ, isMeetPseudocompl_compl a⟩⟩

/-- In a co-Heyting algebra the negation is the join-pseudocomplement. -/
theorem isJoinPseudocompl_hnot [CoheytingAlgebra α] (a : α) : IsJoinPseudocompl a (￢a) :=
  ⟨sup_hnot_self a, fun _ hb ↦ hnot_le_iff_codisjoint_right.2 (codisjoint_iff.2 hb)⟩

instance (priority := 100) [CoheytingAlgebra α] : IsJoinPseudocomplemented α :=
  ⟨fun a ↦ ⟨￢a, isJoinPseudocompl_hnot a⟩⟩

/-- A finite join-semidistributive lattice with a greatest element is join-pseudocomplemented. -/
theorem isJoinPseudocomplemented_of_finite [Lattice α] [OrderTop α] [Finite α]
    [IsJoinSemidistrib α] : IsJoinPseudocomplemented α where
  exists_isJoinPseudocompl a := by
    have hfin := toFinite {b : α | a ⊔ b = ⊤}
    refine ⟨hfin.toFinset.inf id, ?_, fun b hb ↦ Finset.inf_le (f := id) (hfin.mem_toFinset.2 hb)⟩
    refine Finset.inf_induction (p := fun b ↦ a ⊔ b = ⊤) (sup_top_eq a)
      (fun b hb c hc ↦ ?_) fun b hb ↦ hfin.mem_toFinset.1 hb
    rw [← sup_eq_sup_inf_of_sup_eq_sup (hb.trans hc.symm), hb]

/-- A finite meet-semidistributive lattice with a least element is meet-pseudocomplemented. -/
theorem isMeetPseudocomplemented_of_finite [Lattice α] [OrderBot α] [Finite α]
    [IsMeetSemidistrib α] : IsMeetPseudocomplemented α where
  exists_isMeetPseudocompl a := by
    have hfin := toFinite {b : α | a ⊓ b = ⊥}
    refine ⟨hfin.toFinset.sup id, ?_, fun b hb ↦ Finset.le_sup (f := id) (hfin.mem_toFinset.2 hb)⟩
    refine Finset.sup_induction (p := fun b ↦ a ⊓ b = ⊥) (inf_bot_eq a)
      (fun b hb c hc ↦ ?_) fun b hb ↦ hfin.mem_toFinset.1 hb
    rw [← inf_eq_inf_sup_of_inf_eq_inf (hb.trans hc.symm), hb]

/-! ### Meet-distributivity -/

/-- The meet of `b` with all its lower covers. -/
def lowerCore [CompleteLattice α] (b : α) : α :=
  b ⊓ sInf {a | a ⋖ b}

theorem lowerCore_le [CompleteLattice α] (b : α) : lowerCore b ≤ b :=
  inf_le_left

/-- A complete lattice is *meet-distributive* (or *lower locally distributive*) if for every
element `b` the interval between `lowerCore b` and `b` is a Boolean lattice, that is,
distributive and complemented. -/
class IsMeetDistrib (α : Type*) [CompleteLattice α] : Prop where
  /-- The interval `[lowerCore b, b]` is distributive. -/
  inf_sup_le : ∀ ⦃b x y z : α⦄, x ∈ Icc (lowerCore b) b → y ∈ Icc (lowerCore b) b →
    z ∈ Icc (lowerCore b) b → x ⊓ (y ⊔ z) ≤ x ⊓ y ⊔ x ⊓ z
  /-- The interval `[lowerCore b, b]` is complemented. -/
  exists_compl : ∀ ⦃b x : α⦄, x ∈ Icc (lowerCore b) b →
    ∃ y ∈ Icc (lowerCore b) b, x ⊓ y = lowerCore b ∧ x ⊔ y = b

/-- A complete lattice is meet-distributive if every interval `[lowerCore b, b]` is order
isomorphic to a powerset. -/
theorem IsMeetDistrib.of_orderIso [CompleteLattice α]
    (h : ∀ b : α, ∃ ι : Type*, Nonempty (Icc (lowerCore b) b ≃o Set ι)) : IsMeetDistrib α where
  inf_sup_le b x y z hx hy hz := by
    obtain ⟨ι, ⟨e⟩⟩ := h b
    have key : (⟨x, hx⟩ : Icc (lowerCore b) b) ⊓ (⟨y, hy⟩ ⊔ ⟨z, hz⟩) ≤
        ⟨x, hx⟩ ⊓ ⟨y, hy⟩ ⊔ ⟨x, hx⟩ ⊓ ⟨z, hz⟩ := by
      rw [← e.le_iff_le]
      simp only [e.map_inf, e.map_sup]
      exact (inf_sup_left _ _ _).le
    exact key
  exists_compl b x hx := by
    obtain ⟨ι, ⟨e⟩⟩ := h b
    have : Fact (lowerCore b ≤ b) := ⟨lowerCore_le b⟩
    refine ⟨(e.symm (e ⟨x, hx⟩)ᶜ).1, (e.symm (e ⟨x, hx⟩)ᶜ).2, ?_, ?_⟩
    · have : (⟨x, hx⟩ : Icc (lowerCore b) b) ⊓ e.symm (e ⟨x, hx⟩)ᶜ = ⊥ := by
        apply e.injective
        rw [e.map_inf, e.apply_symm_apply, inf_compl_self, e.map_bot]
      exact congrArg Subtype.val this
    · have : (⟨x, hx⟩ : Icc (lowerCore b) b) ⊔ e.symm (e ⟨x, hx⟩)ᶜ = ⊤ := by
        apply e.injective
        rw [e.map_sup, e.apply_symm_apply, sup_compl_eq_top, e.map_top]
      exact congrArg Subtype.val this

end FCA
