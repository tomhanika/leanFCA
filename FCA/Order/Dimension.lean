/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Order.Extension.Linear
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Realizers and the order dimension

The *order dimension* of a partial order `P` (Dushnik–Miller) is the least number of linear
orders on `P` whose intersection is the order of `P`. Such a family of linear orders is called a
*realizer*. Equivalently, the order dimension is the least number of chains into whose product
`P` embeds.

Since cardinalities of index types are awkward to work with, this file uses the predicate
`FCA.HasRealizer P ι`: the order of `P` is the intersection of a family of linear orders indexed
by `ι`, that is, `P` has order dimension at most the cardinality of `ι`.

## Main definitions

* `FCA.HasRealizer P ι`: `P` has a realizer indexed by `ι`.

## Main results

* `FCA.HasRealizer.of_forall_le_iff`: a family of maps into chains which jointly reflect the
  order yields a realizer.
* `FCA.hasRealizer_iff_exists_orderEmbedding`: `P` has a realizer indexed by `ι` if and only if
  `P` embeds into a product of chains indexed by `ι`.
* `FCA.HasRealizer.mono`: the order dimension is monotone along order embeddings.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Function

universe u

namespace FCA

variable {P : Type u} {Q ι κ : Type*} [PartialOrder P] [PartialOrder Q]

/-- The partial order `P` has a *realizer* indexed by `ι`: its order is the intersection of a
family of linear orders on `P` indexed by `ι`. This expresses that the order dimension of `P` is
at most the cardinality of `ι`. -/
def HasRealizer (P : Type*) [PartialOrder P] (ι : Type*) : Prop :=
  ∃ L : ι → LinearOrder P, ∀ x y : P, x ≤ y ↔ ∀ i, (L i).le x y

/-- A family of maps into linear orders such that `x ≤ y` if and only if `f i x ≤ f i y` for all
`i` yields a realizer. The maps need not be injective: ties are broken by a linear extension of
the order of `P`. -/
theorem HasRealizer.of_forall_le_iff {C : ι → Type*} [∀ i, LinearOrder (C i)] (f : ∀ i, P → C i)
    (hf : ∀ x y, x ≤ y ↔ ∀ i, f i x ≤ f i y) : HasRealizer P ι := by
  have hinj (i : ι) : Injective fun x : P ↦ toLex (f i x, toLinearExtension x) :=
    fun x y h ↦ (Prod.mk.inj (toLex.injective h)).2
  refine ⟨fun i ↦ LinearOrder.lift' _ (hinj i), fun x y ↦ ?_⟩
  change x ≤ y ↔ ∀ i, toLex (f i x, toLinearExtension x) ≤ toLex (f i y, toLinearExtension y)
  simp only [Prod.Lex.toLex_le_toLex]
  refine ⟨fun h i ↦ ?_, fun h ↦ (hf x y).2 fun i ↦ ?_⟩
  · exact ((hf x y).1 h i).lt_or_eq.imp_right fun h' ↦ ⟨h', toLinearExtension.monotone h⟩
  · exact (h i).elim le_of_lt fun h' ↦ h'.1.le

/-- A partial order which embeds into a product of chains indexed by `ι` has a realizer indexed
by `ι`. -/
theorem HasRealizer.of_orderEmbedding {C : ι → Type*} [∀ i, LinearOrder (C i)]
    (e : P ↪o ∀ i, C i) : HasRealizer P ι :=
  .of_forall_le_iff (fun i x ↦ e x i) fun _ _ ↦ e.le_iff_le.symm.trans Pi.le_def

/-- A partial order with a realizer indexed by `ι` embeds into a product of chains indexed by
`ι`. -/
theorem HasRealizer.exists_orderEmbedding (h : HasRealizer P ι) :
    ∃ (C : ι → Type u) (_ : ∀ i, LinearOrder (C i)), Nonempty (P ↪o ∀ i, C i) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun _ ↦ P, L, ⟨@OrderEmbedding.ofMapLEIff P (ι → P) _
    (@Pi.preorder ι (fun _ ↦ P) fun i ↦ (L i).toPreorder) (fun x _ ↦ x) fun x y ↦ (hL x y).symm⟩⟩

/-- A partial order has a realizer indexed by `ι` if and only if it embeds into a product of
chains indexed by `ι`. -/
theorem hasRealizer_iff_exists_orderEmbedding :
    HasRealizer P ι ↔
      ∃ (C : ι → Type u) (_ : ∀ i, LinearOrder (C i)), Nonempty (P ↪o ∀ i, C i) :=
  ⟨HasRealizer.exists_orderEmbedding, fun ⟨_, _, ⟨e⟩⟩ ↦ .of_orderEmbedding e⟩

/-- The order dimension is monotone along order embeddings. -/
theorem HasRealizer.mono (h : HasRealizer P ι) (e : Q ↪o P) : HasRealizer Q ι := by
  obtain ⟨L, hL⟩ := h
  exact @HasRealizer.of_forall_le_iff Q ι _ (fun _ ↦ P) L (fun _ ↦ e) fun x y ↦
    e.le_iff_le.symm.trans (hL _ _)

/-- A realizer can be reindexed along a surjection. -/
theorem HasRealizer.of_surjective (h : HasRealizer P ι) (e : κ → ι) (he : Surjective e) :
    HasRealizer P κ :=
  let ⟨L, hL⟩ := h
  ⟨fun k ↦ L (e k), fun x y ↦ (hL x y).trans he.forall⟩

/-- Order-isomorphic partial orders have the same order dimension. -/
theorem _root_.OrderIso.hasRealizer_iff (e : P ≃o Q) : HasRealizer P ι ↔ HasRealizer Q ι :=
  ⟨fun h ↦ h.mono e.symm.toOrderEmbedding, fun h ↦ h.mono e.toOrderEmbedding⟩

/-- A chain has order dimension at most one. -/
theorem hasRealizer_of_linearOrder (C : Type*) [LinearOrder C] (ι : Type*) [Nonempty ι] :
    HasRealizer C ι :=
  .of_forall_le_iff (C := fun _ ↦ C) (fun _ ↦ id) fun _ _ ↦ (forall_const ι).symm

end FCA
