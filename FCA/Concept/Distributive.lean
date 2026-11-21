/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Concept.Dense
public import FCA.Context.Arrows
public import FCA.Order.Semidistributive
public import Mathlib.Order.ModularLattice

/-!
# Distributivity, semidistributivity and semimodularity of concept lattices

This file characterises structural properties of the concept lattice `Concept α β r` in terms
of the arrow relations of the context `r`.

Throughout, `γ a = Concept.ofObject r a` and `μ b = Concept.ofAttribute r b` denote object and
attribute concepts. A context is *well-founded* if it is both `FCA.ObjectWellFounded` and
`FCA.AttributeWellFounded`; every context with finitely many objects or finitely many attributes
is well-founded.

## Main results

* `Concept.sup_inf_le_of_isExtent_union`, `Concept.distribLatticeOfIsExtentUnion`: if the extents
  of a context are closed under binary unions, its concept lattice is distributive.
* `FCA.isExtent_union_of_upArrow`: in an attribute well-founded context in which the up arrows
  leaving an object all point to attributes with the same extent, the extents are closed under
  binary unions.
* `FCA.sup_inf_le_iff_upArrow`: the concept lattice of a well-founded context is distributive
  iff for every irreducible object `a`, the relations `a ↗ b` and `a ↗ b'` imply that `b` and
  `b'` have the same extent. `FCA.sup_inf_le_iff_downArrow` is the dual statement.
* `FCA.isMeetSemidistrib_iff_doubleArrow`: the concept lattice of a well-founded context is
  meet-semidistributive iff `a ⤢ b` and `a ⤢ b'` imply that `b` and `b'` have the same extent.
  `FCA.isJoinSemidistrib_iff_doubleArrow` is the dual statement.
* `FCA.UpArrow.downArrow`: if the concept lattice is lower semimodular, then `a ↗ b` implies
  `a ↙ b` for every irreducible object `a`.
* `FCA.DownArrow.upArrow`: if the concept lattice is upper semimodular, then `a ↙ b` implies
  `a ↗ b` for every irreducible attribute `b`.
* `FCA.downArrow_iff_upArrow`: in a modular concept lattice the two arrow relations coincide on
  irreducible objects and attributes.

## Implementation notes

Distributivity is stated as the inequality `(c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e`, which is the field
`le_sup_inf` of Mathlib's `DistribLattice`.

The implications from the lattice property to the arrow condition need no finiteness
assumption.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

namespace Concept

variable {α β : Type*} {r : α → β → Prop} {c d e : Concept α β r}

/-! ### Extents closed under unions -/

/-- If the union of the extents of two concepts is an extent, it is the extent of their
supremum. -/
theorem extent_sup_of_isExtent_union (h : IsExtent r (c.extent ∪ d.extent)) :
    (c ⊔ d).extent = c.extent ∪ d.extent := by
  refine Subset.antisymm ?_ (union_subset (extent_subset_extent_iff.2 le_sup_left)
    (extent_subset_extent_iff.2 le_sup_right))
  have hle : c ⊔ d ≤ ofIsExtent r _ h :=
    sup_le (extent_subset_extent_iff.1 subset_union_left)
      (extent_subset_extent_iff.1 subset_union_right)
  exact extent_subset_extent_iff.2 hle

/-- If the supremum of concepts is computed by the union of extents, the concept lattice is
distributive. -/
theorem sup_inf_le_of_extent_sup (h : ∀ c d : Concept α β r, (c ⊔ d).extent ⊆ c.extent ∪ d.extent)
    (c d e : Concept α β r) : (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e := by
  rw [← extent_subset_extent_iff]
  rintro a ⟨had, hae⟩
  rcases h c d had with hc | hd
  · exact extent_subset_extent_iff.2 le_sup_left hc
  · rcases h c e hae with hc | he
    · exact extent_subset_extent_iff.2 le_sup_left hc
    · exact extent_subset_extent_iff.2 le_sup_right ⟨hd, he⟩

/-- If the extents of a context are closed under binary unions, its concept lattice is
distributive. -/
theorem sup_inf_le_of_isExtent_union
    (h : ∀ s t, IsExtent r s → IsExtent r t → IsExtent r (s ∪ t)) (c d e : Concept α β r) :
    (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e :=
  sup_inf_le_of_extent_sup (fun c d ↦
    (extent_sup_of_isExtent_union (h _ _ c.isExtent_extent d.isExtent_extent)).subset) c d e

/-- The concept lattice of a context whose extents are closed under binary unions, as a
distributive lattice. -/
abbrev distribLatticeOfIsExtentUnion
    (h : ∀ s t, IsExtent r s → IsExtent r t → IsExtent r (s ∪ t)) :
    DistribLattice (Concept α β r) :=
  { (inferInstance : Lattice (Concept α β r)) with
    le_sup_inf := sup_inf_le_of_isExtent_union h }

end Concept

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {a : α} {b b' : β} {c d e z : Concept α β r}

/-! ### Arrows and the order of the concept lattice -/

/-- If `a ↙ b`, every concept strictly below the object concept of `a` lies below the attribute
concept of `b`. -/
theorem DownArrow.le_ofAttribute_of_lt (h : a ↙[r] b) (hz : z < Concept.ofObject r a) :
    z ≤ Concept.ofAttribute r b := by
  rw [Concept.le_ofAttribute_iff, ← z.upperPolar_extent]
  intro a' ha'
  exact h.2 a' (Concept.intent_ssubset_intent_iff.2 ((Concept.ofObject_le_iff.2 ha').trans_lt hz))

/-- If `a ↗ b`, every concept strictly above the attribute concept of `b` lies above the object
concept of `a`. -/
theorem UpArrow.ofObject_le_of_lt (h : a ↗[r] b) (hz : Concept.ofAttribute r b < z) :
    Concept.ofObject r a ≤ z := by
  rw [Concept.ofObject_le_iff, ← z.lowerPolar_intent]
  intro b' hb'
  exact h.2 b'
    (Concept.extent_ssubset_extent_iff.2 (hz.trans_le (Concept.le_ofAttribute_iff.2 hb')))

/-- If `a ↗ b`, the attribute concept of `b` is covered by its supremum with the object concept
of `a`. -/
theorem UpArrow.covBy (h : a ↗[r] b) :
    Concept.ofAttribute r b ⋖ Concept.ofAttribute r b ⊔ Concept.ofObject r a := by
  refine ⟨lt_of_le_of_ne le_sup_left fun heq ↦ h.1 ?_, fun z hz hz' ↦ ?_⟩
  · exact Concept.ofObject_le_ofAttribute_iff.1 (heq ▸ le_sup_right)
  · exact hz'.not_ge (sup_le hz.le (h.ofObject_le_of_lt hz))

/-- If `a ↙ b`, the object concept of `a` covers its infimum with the attribute concept of
`b`. -/
theorem DownArrow.covBy (h : a ↙[r] b) :
    Concept.ofObject r a ⊓ Concept.ofAttribute r b ⋖ Concept.ofObject r a := by
  refine ⟨lt_of_le_of_ne inf_le_left fun heq ↦ h.1 ?_, fun z hz hz' ↦ ?_⟩
  · exact Concept.ofObject_le_ofAttribute_iff.1 (heq ▸ inf_le_right)
  · exact hz.not_ge (le_inf hz'.le (h.le_ofAttribute_of_lt hz'))

/-- If `a ↗ b` and `a ↗ b'` for attributes with different extents, the object concept of `a`
lies below the supremum of the two attribute concepts. -/
theorem UpArrow.ofObject_le_sup (h : a ↗[r] b) (h' : a ↗[r] b')
    (hne : lowerPolar r {b} ≠ lowerPolar r {b'}) :
    Concept.ofObject r a ≤ Concept.ofAttribute r b ⊔ Concept.ofAttribute r b' := by
  rw [Concept.ofObject_le_iff, ← Concept.lowerPolar_intent]
  intro n hn
  have hn₁ : lowerPolar r {b} ⊆ lowerPolar r {n} :=
    fun x hx ↦ (mem_lowerPolar_singleton r).2 (hn.1 hx)
  have hn₂ : lowerPolar r {b'} ⊆ lowerPolar r {n} :=
    fun x hx ↦ (mem_lowerPolar_singleton r).2 (hn.2 hx)
  by_cases hs : lowerPolar r {b} ⊂ lowerPolar r {n}
  · exact h.2 n hs
  · have hnb : lowerPolar r {n} ⊆ lowerPolar r {b} := by_contra fun hc ↦ hs ⟨hn₁, hc⟩
    by_cases hs' : lowerPolar r {b'} ⊂ lowerPolar r {b}
    · exact absurd (h'.2 b hs') h.1
    · exact absurd (Subset.antisymm (by_contra fun hc ↦ hs' ⟨hn₂.trans hnb, hc⟩)
        (hn₂.trans hnb)) hne

/-- If `a ∉ d.extent` although all objects with a properly larger intent belong to `d.extent`,
there is a double arrow from `a` to an attribute of the intent of `d`. -/
theorem exists_doubleArrow_of_notMem_extent (hr : AttributeWellFounded r) (had : a ∉ d.extent)
    (hlow : ∀ a', upperPolar r {a} ⊂ upperPolar r {a'} → a' ∈ d.extent) :
    ∃ m ∈ d.intent, a ⤢[r] m := by
  have : ∃ m ∈ d.intent, ¬ r a m := by
    by_contra hcon
    refine had ?_
    rw [← d.lowerPolar_intent]
    exact fun m hm ↦ by_contra fun ham ↦ hcon ⟨m, hm, ham⟩
  obtain ⟨m, hm, ham⟩ := this
  have hdown : a ↙[r] m := ⟨ham, fun a' ha' ↦ Concept.rel_extent_intent (hlow a' ha') hm⟩
  obtain ⟨m', hmm', hd⟩ := hdown.exists_doubleArrow hr
  refine ⟨m', ?_, hd⟩
  rw [← d.upperPolar_extent]
  intro x hx
  exact (mem_lowerPolar_singleton r).1
    (hmm' ((mem_lowerPolar_singleton r).2 (Concept.rel_extent_intent hx hm)))

/-- In an object well-founded context, the order of the concept lattice is determined by the
irreducible objects. -/
theorem ObjectWellFounded.le_of_forall_irreducible (hr : ObjectWellFounded r)
    (h : ∀ a, ObjectIrreducible r a → a ∈ c.extent → a ∈ d.extent) : c ≤ d := by
  rw [← Concept.extent_subset_extent_iff]
  intro a ha
  obtain ⟨u, hu, hua⟩ := hr.exists_irreducible a
  have huc : u ⊆ c.extent := fun a' ha' ↦
    c.isExtent_extent.lowerPolar_upperPolar_subset (singleton_subset_iff.2 ha)
      (hua ▸ subset_lowerPolar_upperPolar r u ha')
  have hud : u ⊆ d.extent := fun a' ha' ↦ h a' (hu ha') (huc ha')
  exact d.isExtent_extent.lowerPolar_upperPolar_subset hud
    (hua ▸ subset_lowerPolar_upperPolar r {a} rfl)

/-! ### Distributivity -/

/-- In an attribute well-founded context, an object whose up arrows all point to attributes with
the same extent has a join-prime object concept. -/
theorem mem_extent_or_of_mem_extent_sup (hr : AttributeWellFounded r)
    (h : ∀ b b', a ↗[r] b → a ↗[r] b' → lowerPolar r {b} = lowerPolar r {b'})
    (ha : a ∈ (c ⊔ d).extent) : a ∈ c.extent ∨ a ∈ d.extent := by
  by_contra hcon
  rw [not_or, ← c.lowerPolar_intent, ← d.lowerPolar_intent] at hcon
  have hc : ∃ m ∈ c.intent, ¬ r a m := by
    by_contra hc
    exact hcon.1 fun m hm ↦ by_contra fun ham ↦ hc ⟨m, hm, ham⟩
  have hd : ∃ n ∈ d.intent, ¬ r a n := by
    by_contra hd
    exact hcon.2 fun n hn ↦ by_contra fun han ↦ hd ⟨n, hn, han⟩
  obtain ⟨m, hm, ham⟩ := hc
  obtain ⟨n, hn, han⟩ := hd
  obtain ⟨m', hmm', ham'⟩ := hr.exists_upArrow ham
  obtain ⟨n', hnn', han'⟩ := hr.exists_upArrow han
  have heq := h m' n' ham' han'
  refine ham'.1 (Concept.rel_extent_intent ha (y := m') ⟨?_, ?_⟩)
  · rw [← c.upperPolar_extent]
    exact fun x hx ↦ (mem_lowerPolar_singleton r).1
      (hmm' ((mem_lowerPolar_singleton r).2 (Concept.rel_extent_intent hx hm)))
  · rw [← d.upperPolar_extent]
    exact fun x hx ↦ (mem_lowerPolar_singleton r).1
      (heq ▸ hnn' ((mem_lowerPolar_singleton r).2 (Concept.rel_extent_intent hx hn)))

/-- In an attribute well-founded context in which the up arrows leaving an object all point to
attributes with the same extent, the extents are closed under binary unions. -/
theorem isExtent_union_of_upArrow (hr : AttributeWellFounded r)
    (h : ∀ a b b', a ↗[r] b → a ↗[r] b' → lowerPolar r {b} = lowerPolar r {b'}) {s t : Set α}
    (hs : IsExtent r s) (ht : IsExtent r t) : IsExtent r (s ∪ t) := by
  have : (Concept.ofIsExtent r s hs ⊔ Concept.ofIsExtent r t ht).extent = s ∪ t :=
    Subset.antisymm (fun a ha ↦ mem_extent_or_of_mem_extent_sup hr (h a) ha)
      (union_subset
        (Concept.extent_subset_extent_iff.2
          (le_sup_left : Concept.ofIsExtent r s hs ≤ _ ⊔ Concept.ofIsExtent r t ht))
        (Concept.extent_subset_extent_iff.2
          (le_sup_right : Concept.ofIsExtent r t ht ≤ Concept.ofIsExtent r s hs ⊔ _)))
  exact this ▸ Concept.isExtent_extent _

/-- In a distributive concept lattice, the up arrows leaving an irreducible object all point to
attributes with the same extent. -/
theorem UpArrow.lowerPolar_eq_of_sup_inf_le
    (hdist : ∀ c d e : Concept α β r, (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e)
    (ha : ObjectIrreducible r a) (h : a ↗[r] b) (h' : a ↗[r] b') :
    lowerPolar r {b} = lowerPolar r {b'} := by
  by_contra hne
  let : DistribLattice (Concept α β r) :=
    { (inferInstance : Lattice (Concept α β r)) with le_sup_inf := hdist }
  have hle := h.ofObject_le_sup h' hne
  have heq : Concept.ofObject r a ⊓ Concept.ofAttribute r b ⊔
      Concept.ofObject r a ⊓ Concept.ofAttribute r b' = Concept.ofObject r a := by
    rw [← inf_sup_left]
    exact inf_eq_left.2 hle
  rcases ha.supIrred.2 heq with h₁ | h₁
  · exact h.1 (Concept.ofObject_le_ofAttribute_iff.1 (inf_eq_left.1 h₁))
  · exact h'.1 (Concept.ofObject_le_ofAttribute_iff.1 (inf_eq_left.1 h₁))

/-- The concept lattice of a well-founded context is **distributive** if and only if the up
arrows leaving an irreducible object all point to attributes with the same extent. -/
theorem sup_inf_le_iff_upArrow (ho : ObjectWellFounded r) (ha : AttributeWellFounded r) :
    (∀ c d e : Concept α β r, (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e) ↔
      ∀ a b b', ObjectIrreducible r a → a ↗[r] b → a ↗[r] b' →
        lowerPolar r {b} = lowerPolar r {b'} := by
  refine ⟨fun hdist a b b' hirr h h' ↦ h.lowerPolar_eq_of_sup_inf_le hdist hirr h', ?_⟩
  intro h c d e
  refine ho.le_of_forall_irreducible fun a hirr hmem ↦ ?_
  rcases mem_extent_or_of_mem_extent_sup ha (fun b b' ↦ h a b b' hirr) hmem.1 with hc | hd
  · exact Concept.extent_subset_extent_iff.2 le_sup_left hc
  · rcases mem_extent_or_of_mem_extent_sup ha (fun b b' ↦ h a b b' hirr) hmem.2 with hc | he
    · exact Concept.extent_subset_extent_iff.2 le_sup_left hc
    · exact Concept.extent_subset_extent_iff.2 le_sup_right ⟨hd, he⟩

/-- The concept lattice of a well-founded context in which every object is irreducible is
distributive if and only if its extents are closed under binary unions. -/
theorem sup_inf_le_iff_isExtent_union (ha : AttributeWellFounded r)
    (hirr : ∀ a, ObjectIrreducible r a) :
    (∀ c d e : Concept α β r, (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e) ↔
      ∀ s t, IsExtent r s → IsExtent r t → IsExtent r (s ∪ t) :=
  ⟨fun hdist _ _ hs ht ↦ isExtent_union_of_upArrow ha
    (fun a _ _ h h' ↦ h.lowerPolar_eq_of_sup_inf_le hdist (hirr a) h') hs ht,
    Concept.sup_inf_le_of_isExtent_union⟩

/-- Distributivity passes to lattices which are order isomorphic to the dual lattice. -/
theorem sup_inf_le_of_orderIso_dual {L M : Type*} [Lattice L] [Lattice M] (f : Lᵒᵈ ≃o M)
    (h : ∀ x y z : L, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z) (x y z : M) :
    (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z := by
  let : DistribLattice L := { (inferInstance : Lattice L) with le_sup_inf := h }
  rw [← f.symm.le_iff_le]
  simp only [map_sup, map_inf]
  exact le_sup_inf

/-- The concept lattice of a well-founded context is **distributive** if and only if the down
arrows entering an irreducible attribute all come from objects with the same intent. -/
theorem sup_inf_le_iff_downArrow (ho : ObjectWellFounded r) (ha : AttributeWellFounded r) :
    (∀ c d e : Concept α β r, (c ⊔ d) ⊓ (c ⊔ e) ≤ c ⊔ d ⊓ e) ↔
      ∀ a a' b, AttributeIrreducible r b → a ↙[r] b → a' ↙[r] b →
        upperPolar r {a} = upperPolar r {a'} := by
  have key := sup_inf_le_iff_upArrow (r := swap r) ha ho
  exact ⟨fun h a a' b hb h₁ h₂ ↦ key.1 (sup_inf_le_of_orderIso_dual Concept.swapEquiv h) b a a' hb
    h₁ h₂, fun h ↦ sup_inf_le_of_orderIso_dual
      (Concept.swapEquiv : (Concept β α (swap r))ᵒᵈ ≃o Concept α β r)
      (key.2 fun b a a' hb h₁ h₂ ↦ h a a' b hb h₁ h₂)⟩

/-! ### Semidistributivity -/

/-- In a meet-semidistributive concept lattice, the double arrows leaving an object all point to
attributes with the same extent. -/
theorem DoubleArrow.lowerPolar_eq [IsMeetSemidistrib (Concept α β r)] (h : a ⤢[r] b)
    (h' : a ⤢[r] b') : lowerPolar r {b} = lowerPolar r {b'} := by
  by_contra hne
  have hlt : Concept.ofObject r a ⊓ Concept.ofAttribute r b < Concept.ofObject r a :=
    h.downArrow.covBy.lt
  have hlt' : Concept.ofObject r a ⊓ Concept.ofAttribute r b' < Concept.ofObject r a :=
    h'.downArrow.covBy.lt
  have heq : Concept.ofObject r a ⊓ Concept.ofAttribute r b =
      Concept.ofObject r a ⊓ Concept.ofAttribute r b' :=
    le_antisymm (le_inf inf_le_left (h'.downArrow.le_ofAttribute_of_lt hlt))
      (le_inf inf_le_left (h.downArrow.le_ofAttribute_of_lt hlt'))
  rw [inf_eq_inf_sup_of_inf_eq_inf heq, inf_eq_left.2 (h.upArrow.ofObject_le_sup h'.upArrow hne)]
    at hlt
  exact lt_irrefl _ hlt

/-- The concept lattice of a well-founded context is **meet-semidistributive** if and only if the
double arrows leaving an object all point to attributes with the same extent. -/
theorem isMeetSemidistrib_iff_doubleArrow (ho : ObjectWellFounded r)
    (ha : AttributeWellFounded r) :
    IsMeetSemidistrib (Concept α β r) ↔
      ∀ a b b', a ⤢[r] b → a ⤢[r] b' → lowerPolar r {b} = lowerPolar r {b'} := by
  refine ⟨fun _ a b b' h h' ↦ h.lowerPolar_eq h', fun huniq ↦ ⟨fun c d e h ↦ ?_⟩⟩
  refine le_antisymm (le_inf inf_le_left (inf_le_right.trans le_sup_left)) ?_
  by_contra hnle
  rw [← Concept.extent_subset_extent_iff] at hnle
  obtain ⟨a₀, ha₀⟩ := not_subset.1 hnle
  obtain ⟨a, ⟨hav, hau⟩, hmin⟩ :=
    ho.has_min {a | a ∈ (c ⊓ (d ⊔ e)).extent ∧ a ∉ (c ⊓ d).extent} ⟨a₀, ha₀⟩
  have hau' : a ∉ (c ⊓ e).extent := by rw [← h]; exact hau
  have hlow : ∀ a', upperPolar r {a} ⊂ upperPolar r {a'} → a' ∈ (c ⊓ d).extent := by
    intro a' ha'
    by_contra hcon
    refine hmin a' ⟨?_, hcon⟩ ha'
    exact Concept.ofObject_le_iff.1
      ((Concept.intent_ssubset_intent_iff (c := Concept.ofObject r a)
        (d := Concept.ofObject r a')).1 ha' |>.le.trans (Concept.ofObject_le_iff.2 hav))
  have hlow' : ∀ a', upperPolar r {a} ⊂ upperPolar r {a'} → a' ∈ (c ⊓ e).extent := by
    intro a' ha'
    rw [← h]
    exact hlow a' ha'
  obtain ⟨m, hm, ham⟩ := exists_doubleArrow_of_notMem_extent (d := d) ha
    (fun had ↦ hau ⟨hav.1, had⟩) fun a' ha' ↦ (hlow a' ha').2
  obtain ⟨n, hn, han⟩ := exists_doubleArrow_of_notMem_extent (d := e) ha
    (fun hae ↦ hau' ⟨hav.1, hae⟩) fun a' ha' ↦ (hlow' a' ha').2
  have heq := huniq a m n ham han
  refine ham.not_rel (Concept.rel_extent_intent hav.2 (y := m) ⟨hm, ?_⟩)
  rw [← e.upperPolar_extent]
  exact fun x hx ↦ (mem_lowerPolar_singleton r).1
    (heq ▸ (mem_lowerPolar_singleton r).2 (Concept.rel_extent_intent hx hn))

/-- A lattice is join-semidistributive if its dual is meet-semidistributive. -/
theorem isJoinSemidistrib_of_dual {L : Type*} [Lattice L] [IsMeetSemidistrib Lᵒᵈ] :
    IsJoinSemidistrib L :=
  ⟨fun _ _ _ h ↦ inf_eq_inf_sup_of_inf_eq_inf (α := Lᵒᵈ) h⟩

/-- The concept lattice of a well-founded context is **join-semidistributive** if and only if the
double arrows entering an attribute all come from objects with the same intent. -/
theorem isJoinSemidistrib_iff_doubleArrow (ho : ObjectWellFounded r)
    (ha : AttributeWellFounded r) :
    IsJoinSemidistrib (Concept α β r) ↔
      ∀ a a' b, a ⤢[r] b → a' ⤢[r] b → upperPolar r {a} = upperPolar r {a'} := by
  have key := isMeetSemidistrib_iff_doubleArrow (r := swap r) ha ho
  constructor
  · intro _ a a' b h h'
    have : IsMeetSemidistrib (Concept β α (swap r)) := .of_orderIso Concept.swapEquiv
    exact key.1 this b a a' (doubleArrow_swap.2 h) (doubleArrow_swap.2 h')
  · intro h
    have : IsMeetSemidistrib (Concept β α (swap r)) :=
      key.2 fun b a a' h₁ h₂ ↦ h a a' b (doubleArrow_swap.1 h₁) (doubleArrow_swap.1 h₂)
    have : IsMeetSemidistrib (Concept α β r)ᵒᵈ := .of_orderIso Concept.swapEquiv.symm
    exact isJoinSemidistrib_of_dual

/-! ### Semimodularity -/

/-- In a lower semimodular concept lattice, `a ↗ b` implies `a ↙ b` for every irreducible
object `a`. -/
theorem UpArrow.downArrow [IsLowerModularLattice (Concept α β r)] (h : a ↗[r] b)
    (ha : ObjectIrreducible r a) : a ↙[r] b := by
  have hcov : Concept.ofAttribute r b ⊓ Concept.ofObject r a ⋖ Concept.ofObject r a :=
    IsLowerModularLattice.inf_covBy_of_covBy_sup h.covBy
  have hne : sSup {z | z < Concept.ofObject r a} ≠ Concept.ofObject r a := by
    intro heq
    have hmem : Concept.ofObject r a ∈ {z | z < Concept.ofObject r a} :=
      objectIrreducible_iff_forall_sSup.1 ha _ heq
    exact lt_irrefl (Concept.ofObject r a) hmem
  have hle : sSup {z | z < Concept.ofObject r a} ≤ Concept.ofObject r a :=
    sSup_le fun z hz ↦ le_of_lt hz
  have hge : Concept.ofAttribute r b ⊓ Concept.ofObject r a ≤
      sSup {z | z < Concept.ofObject r a} :=
    le_sSup hcov.lt
  have heq : sSup {z | z < Concept.ofObject r a} =
      Concept.ofAttribute r b ⊓ Concept.ofObject r a :=
    (hcov.eq_or_eq hge hle).resolve_right hne
  refine ⟨h.1, fun a' ha' ↦ Concept.ofObject_le_ofAttribute_iff.1 ?_⟩
  have hlt : Concept.ofObject r a' < Concept.ofObject r a :=
    (Concept.intent_ssubset_intent_iff (c := Concept.ofObject r a)
      (d := Concept.ofObject r a')).1 ha'
  have hle' : Concept.ofObject r a' ≤ sSup {z | z < Concept.ofObject r a} := le_sSup hlt
  exact (hle'.trans heq.le).trans inf_le_left

/-- In an upper semimodular concept lattice, `a ↙ b` implies `a ↗ b` for every irreducible
attribute `b`. -/
theorem DownArrow.upArrow [IsUpperModularLattice (Concept α β r)] (h : a ↙[r] b)
    (hb : AttributeIrreducible r b) : a ↗[r] b := by
  have hcov : Concept.ofAttribute r b ⋖ Concept.ofObject r a ⊔ Concept.ofAttribute r b :=
    IsUpperModularLattice.covBy_sup_of_inf_covBy h.covBy
  have hne : sInf {z | Concept.ofAttribute r b < z} ≠ Concept.ofAttribute r b := fun heq ↦
    lt_irrefl _ (attributeIrreducible_iff_forall_sInf.1 hb _ heq)
  have hle : Concept.ofAttribute r b ≤ sInf {z | Concept.ofAttribute r b < z} :=
    le_sInf fun z hz ↦ le_of_lt hz
  have heq : sInf {z | Concept.ofAttribute r b < z} =
      Concept.ofObject r a ⊔ Concept.ofAttribute r b :=
    (hcov.eq_or_eq hle (sInf_le hcov.lt)).resolve_left hne
  refine ⟨h.1, fun b' hb' ↦ Concept.ofObject_le_ofAttribute_iff.1 ?_⟩
  have hlt : Concept.ofAttribute r b < Concept.ofAttribute r b' :=
    (Concept.extent_ssubset_extent_iff (c := Concept.ofAttribute r b)
      (d := Concept.ofAttribute r b')).1 hb'
  exact (le_sup_left.trans heq.ge).trans (sInf_le hlt)

/-- In a modular concept lattice, the two arrow relations coincide on irreducible objects and
irreducible attributes. -/
theorem downArrow_iff_upArrow [IsModularLattice (Concept α β r)] (ha : ObjectIrreducible r a)
    (hb : AttributeIrreducible r b) : a ↙[r] b ↔ a ↗[r] b :=
  ⟨fun h ↦ h.upArrow hb, fun h ↦ h.downArrow ha⟩

/-- In a modular concept lattice every arrow between an irreducible object and an irreducible
attribute is a double arrow. -/
theorem doubleArrow_iff_upArrow [IsModularLattice (Concept α β r)] (ha : ObjectIrreducible r a) :
    a ⤢[r] b ↔ a ↗[r] b :=
  ⟨fun h ↦ h.upArrow, fun h ↦ ⟨h.downArrow ha, h⟩⟩

end FCA
