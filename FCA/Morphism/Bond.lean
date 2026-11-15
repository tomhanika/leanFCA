/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Concept.Dense
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Bonds between formal contexts

A *bond* from a context `r : α → β → Prop` to a context `s : γ → δ → Prop` is a relation
`j : α → δ → Prop` between the objects of `r` and the attributes of `s` such that every row
`upperPolar j {a}` is an intent of `s` and every column `lowerPolar j {d}` is an extent of `r`.
Bonds are the morphisms of contexts corresponding to supremum-preserving maps between the concept
lattices.

## Main definitions

* `FCA.Bond r s`: the bonds from `r` to `s`.
* `FCA.Bond.refl r`: the incidence `r` itself is a bond from `r` to `r`.
* `FCA.Bond.trans j₁ j₂`: the bond product of `j₁ : Bond r s` and `j₂ : Bond s t`, relating `a`
  to all elements of `(a^{j₁})^{s j₂}`. Composition is written in diagrammatic order.
* `FCA.Bond.swap`: a bond from `r` to `s` is a bond between the dual contexts, from `s` to `r`.
* `FCA.Bond.map j`: the supremum-preserving map `Concept α β r → Concept γ δ s` induced by a bond.
* `FCA.Bond.comap j`: the infimum-preserving map `Concept γ δ s → Concept α β r` induced by a
  bond.
* `FCA.Bond.ofSSupHom`: the bond of a supremum-preserving map between concept lattices.
* `FCA.Bond.equivSSupHom`: the bijection between bonds from `r` to `s` and supremum-preserving
  maps `Concept α β r → Concept γ δ s`.

## Main results

* `FCA.Bond.refl_trans`, `FCA.Bond.trans_refl`, `FCA.Bond.trans_assoc`: contexts and bonds form a
  category.
* `FCA.Bond.map_refl`, `FCA.Bond.map_trans`: `Bond.map` is functorial.
* `FCA.Bond.gc_map_comap`: `Bond.map` and `Bond.comap` form a Galois connection.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [B. Ganter, *Relational Galois connections*][ganter2007]
-/

@[expose] public section

open Set Order Function

variable {α β γ δ ε ζ η θ : Type*} {r : α → β → Prop} {s : γ → δ → Prop} {t : ε → ζ → Prop}
  {u : η → θ → Prop}

namespace Order

/-- For an intent `t` and an extent `s`, the extent belonging to `t` is contained in `s` iff the
intent belonging to `s` is contained in `t`. -/
theorem IsIntent.lowerPolar_subset_iff {s : Set α} {t : Set β} (ht : IsIntent r t)
    (hs : IsExtent r s) : lowerPolar r t ⊆ s ↔ upperPolar r s ⊆ t :=
  ⟨fun h => ht.eq ▸ upperPolar_anti r h, fun h => hs.eq ▸ lowerPolar_anti r h⟩

end Order

namespace FCA

/-- A *bond* from the context `r : α → β → Prop` to the context `s : γ → δ → Prop` is a relation
between the objects of `r` and the attributes of `s` all of whose rows are intents of `s` and all
of whose columns are extents of `r`. -/
structure Bond (r : α → β → Prop) (s : γ → δ → Prop) where
  /-- The underlying relation of a bond. -/
  rel : α → δ → Prop
  /-- Every row of a bond is an intent of the target context. -/
  isIntent_upperPolar_singleton (a : α) : IsIntent s (upperPolar rel {a})
  /-- Every column of a bond is an extent of the source context. -/
  isExtent_lowerPolar_singleton (d : δ) : IsExtent r (lowerPolar rel {d})

namespace Bond

@[ext]
theorem ext {j₁ j₂ : Bond r s} (h : ∀ a d, j₁.rel a d ↔ j₂.rel a d) : j₁ = j₂ := by
  obtain ⟨j₁, _, _⟩ := j₁
  obtain ⟨j₂, _, _⟩ := j₂
  obtain rfl : j₁ = j₂ := funext₂ fun a d => propext (h a d)
  rfl

/-! ### Polars of a bond -/

section Polar

variable (j : Bond r s)

/-- A bond from `r` to `s` is also a bond between the dual contexts, from `swap s` to
`swap r`. -/
@[simps]
protected def swap : Bond (swap s) (swap r) where
  rel := swap j.rel
  isIntent_upperPolar_singleton := j.isExtent_lowerPolar_singleton
  isExtent_lowerPolar_singleton := j.isIntent_upperPolar_singleton

@[simp]
theorem swap_swap : j.swap.swap = j :=
  rfl

/-- The upper polar of any set of objects along a bond is an intent of the target context. -/
theorem isIntent_upperPolar (X : Set α) : IsIntent s (upperPolar j.rel X) := by
  rw [← biUnion_of_singleton X, upperPolar_iUnion₂]
  exact .iInter₂ _ fun a _ => j.isIntent_upperPolar_singleton a

/-- The lower polar of any set of attributes along a bond is an extent of the source context. -/
theorem isExtent_lowerPolar (Y : Set δ) : IsExtent r (lowerPolar j.rel Y) :=
  j.swap.isIntent_upperPolar Y

/-- The upper polar along a bond does not change when passing to the generated extent. -/
@[simp]
theorem upperPolar_lowerPolar_upperPolar (X : Set α) :
    upperPolar j.rel (lowerPolar r (upperPolar r X)) = upperPolar j.rel X := by
  refine (upperPolar_anti _ (subset_lowerPolar_upperPolar r X)).antisymm fun d hd a ha => ?_
  have hX : X ⊆ lowerPolar j.rel {d} := fun a ha => (mem_lowerPolar_singleton _).2 (hd ha)
  exact (mem_lowerPolar_singleton _).1
    ((j.isExtent_lowerPolar_singleton d).lowerPolar_upperPolar_subset hX ha)

/-- The lower polar along a bond does not change when passing to the generated intent. -/
@[simp]
theorem lowerPolar_upperPolar_lowerPolar (Y : Set δ) :
    lowerPolar j.rel (upperPolar s (lowerPolar s Y)) = lowerPolar j.rel Y :=
  j.swap.upperPolar_lowerPolar_upperPolar Y

end Polar

/-! ### Identity and composition -/

/-- The incidence relation of a context is a bond from the context to itself. It is the identity
for the bond product. -/
protected def refl (r : α → β → Prop) : Bond r r where
  rel := r
  isIntent_upperPolar_singleton _ := Order.isIntent_upperPolar
  isExtent_lowerPolar_singleton _ := Order.isExtent_lowerPolar

@[simp]
theorem refl_rel (r : α → β → Prop) : (Bond.refl r).rel = r :=
  rfl

instance : Inhabited (Bond r r) :=
  ⟨.refl r⟩

/-- The two descriptions of the bond product agree: `Y ⊆ (X^{j₁})^{s j₂}` iff
`X ⊆ (Y^{j₂})^{s j₁}`. -/
theorem subset_upperPolar_lowerPolar_upperPolar_iff (j₁ : Bond r s) (j₂ : Bond s t) {X : Set α}
    {Y : Set ζ} :
    Y ⊆ upperPolar j₂.rel (lowerPolar s (upperPolar j₁.rel X)) ↔
      X ⊆ lowerPolar j₁.rel (upperPolar s (lowerPolar j₂.rel Y)) := by
  rw [subset_upperPolar_iff_subset_lowerPolar,
    (j₁.isIntent_upperPolar X).lowerPolar_subset_iff (j₂.isExtent_lowerPolar Y),
    subset_upperPolar_iff_subset_lowerPolar]

/-- The *bond product* of a bond `j₁` from `r` to `s` and a bond `j₂` from `s` to `t`, a bond
from `r` to `t`: an object `a` of `r` is related to the attribute `f` of `t` iff `f` lies in
`(a^{j₁})^{s j₂}`, where `a^{j₁}` is the row of `a` in `j₁`, the polar `^s` is taken in the
middle context, and `^{j₂}` is the upper polar along `j₂`. -/
protected def trans (j₁ : Bond r s) (j₂ : Bond s t) : Bond r t where
  rel a f := f ∈ upperPolar j₂.rel (lowerPolar s (upperPolar j₁.rel {a}))
  isIntent_upperPolar_singleton a := by
    convert j₂.isIntent_upperPolar (lowerPolar s (upperPolar j₁.rel {a}))
    ext f
    exact mem_upperPolar_singleton _
  isExtent_lowerPolar_singleton f := by
    convert j₁.isExtent_lowerPolar (upperPolar s (lowerPolar j₂.rel {f}))
    ext a
    rw [mem_lowerPolar_singleton, ← singleton_subset_iff,
      j₁.subset_upperPolar_lowerPolar_upperPolar_iff j₂, singleton_subset_iff]

section Trans

variable (j₁ : Bond r s) (j₂ : Bond s t) (j₃ : Bond t u)

theorem trans_rel_iff {a : α} {f : ζ} :
    (j₁.trans j₂).rel a f ↔ f ∈ upperPolar j₂.rel (lowerPolar s (upperPolar j₁.rel {a})) :=
  Iff.rfl

theorem trans_rel_iff' {a : α} {f : ζ} :
    (j₁.trans j₂).rel a f ↔ a ∈ lowerPolar j₁.rel (upperPolar s (lowerPolar j₂.rel {f})) := by
  rw [trans_rel_iff, ← singleton_subset_iff, subset_upperPolar_lowerPolar_upperPolar_iff,
    singleton_subset_iff]

/-- The upper polar along a bond product. -/
theorem upperPolar_trans_rel (X : Set α) :
    upperPolar (j₁.trans j₂).rel X = upperPolar j₂.rel (lowerPolar s (upperPolar j₁.rel X)) := by
  ext f
  rw [← singleton_subset_iff (s := upperPolar j₂.rel _),
    subset_upperPolar_lowerPolar_upperPolar_iff]
  exact forall₂_congr fun a _ => j₁.trans_rel_iff' j₂

/-- The lower polar along a bond product. -/
theorem lowerPolar_trans_rel (Y : Set ζ) :
    lowerPolar (j₁.trans j₂).rel Y = lowerPolar j₁.rel (upperPolar s (lowerPolar j₂.rel Y)) := by
  ext a
  rw [← singleton_subset_iff (s := lowerPolar j₁.rel _),
    ← subset_upperPolar_lowerPolar_upperPolar_iff]
  exact Iff.rfl

@[simp]
theorem swap_trans : (j₁.trans j₂).swap = j₂.swap.trans j₁.swap :=
  ext fun _ _ => j₁.trans_rel_iff' j₂

@[simp]
theorem refl_trans : (Bond.refl r).trans j₁ = j₁ := by
  ext a d
  rw [trans_rel_iff, refl_rel, j₁.upperPolar_lowerPolar_upperPolar, mem_upperPolar_singleton]

@[simp]
theorem trans_refl : j₁.trans (.refl s) = j₁ := by
  ext a d
  rw [trans_rel_iff, refl_rel, (j₁.isIntent_upperPolar_singleton a).eq, mem_upperPolar_singleton]

theorem trans_assoc : (j₁.trans j₂).trans j₃ = j₁.trans (j₂.trans j₃) := by
  ext a h
  rw [trans_rel_iff, trans_rel_iff, upperPolar_trans_rel, upperPolar_trans_rel]

end Trans

/-! ### The maps between concept lattices induced by a bond -/

section Map

variable (j : Bond r s)

/-- The supremum-preserving map between concept lattices induced by a bond: the concept with
extent `A` is sent to the concept with intent `A^j`. -/
def map : sSupHom (Concept α β r) (Concept γ δ s) where
  toFun c := .ofIsIntent s (upperPolar j.rel c.extent) (j.isIntent_upperPolar _)
  map_sSup' S := by
    refine Concept.ext' ?_
    have h : ⋂ c ∈ S, c.intent = upperPolar r (⋃ c ∈ S, c.extent) := by
      simp
    rw [Concept.intent_ofIsIntent, Concept.extent_sSup, h, j.upperPolar_lowerPolar_upperPolar,
      upperPolar_iUnion₂, Concept.intent_sSup, biInter_image]
    rfl

@[simp]
theorem intent_map (c : Concept α β r) : (j.map c).intent = upperPolar j.rel c.extent :=
  rfl

@[simp]
theorem extent_map (c : Concept α β r) :
    (j.map c).extent = lowerPolar s (upperPolar j.rel c.extent) :=
  rfl

/-- The image of an object concept under the map induced by a bond has the row of the object as
its intent. -/
theorem intent_map_ofObject (a : α) : (j.map (.ofObject r a)).intent = upperPolar j.rel {a} :=
  j.upperPolar_lowerPolar_upperPolar {a}

/-- The infimum-preserving map between concept lattices induced by a bond: the concept with
intent `B` is sent to the concept with extent `B^j`. -/
def comap : sInfHom (Concept γ δ s) (Concept α β r) where
  toFun c := .ofIsExtent r (lowerPolar j.rel c.intent) (j.isExtent_lowerPolar _)
  map_sInf' S := by
    refine Concept.ext ?_
    have h : ⋂ c ∈ S, c.extent = lowerPolar s (⋃ c ∈ S, c.intent) := by
      simp
    rw [Concept.extent_ofIsExtent, Concept.intent_sInf, h, j.lowerPolar_upperPolar_lowerPolar,
      lowerPolar_iUnion₂, Concept.extent_sInf, biInter_image]
    rfl

@[simp]
theorem extent_comap (c : Concept γ δ s) : (j.comap c).extent = lowerPolar j.rel c.intent :=
  rfl

@[simp]
theorem intent_comap (c : Concept γ δ s) :
    (j.comap c).intent = upperPolar r (lowerPolar j.rel c.intent) :=
  rfl

theorem map_le_iff {c : Concept α β r} {d : Concept γ δ s} : j.map c ≤ d ↔ c ≤ j.comap d :=
  Concept.intent_subset_intent_iff.symm.trans subset_upperPolar_iff_subset_lowerPolar

/-- The maps between concept lattices induced by a bond form a Galois connection. -/
theorem gc_map_comap : GaloisConnection j.map j.comap :=
  fun _ _ => j.map_le_iff

@[simp]
theorem map_refl : (Bond.refl r).map = sSupHom.id _ :=
  sSupHom.ext fun c => Concept.ext' c.upperPolar_extent

@[simp]
theorem comap_refl : (Bond.refl r).comap = sInfHom.id _ :=
  sInfHom.ext fun c => Concept.ext c.lowerPolar_intent

theorem map_trans (j₁ : Bond r s) (j₂ : Bond s t) : (j₁.trans j₂).map = j₂.map.comp j₁.map :=
  sSupHom.ext fun c => Concept.ext' (j₁.upperPolar_trans_rel j₂ c.extent)

theorem comap_trans (j₁ : Bond r s) (j₂ : Bond s t) :
    (j₁.trans j₂).comap = j₁.comap.comp j₂.comap :=
  sInfHom.ext fun c => Concept.ext (j₁.lowerPolar_trans_rel j₂ c.intent)

end Map

/-! ### Bonds and supremum-preserving maps -/

/-- The bond of a supremum-preserving map `φ` between concept lattices: an object `a` is related
to the attribute `d` iff `d` lies in the intent of the image of the object concept of `a`. -/
def ofSSupHom (φ : sSupHom (Concept α β r) (Concept γ δ s)) : Bond r s where
  rel a d := d ∈ (φ (.ofObject r a)).intent
  isIntent_upperPolar_singleton a := by
    convert (φ (.ofObject r a)).isIntent_intent
    ext d
    exact mem_upperPolar_singleton _
  isExtent_lowerPolar_singleton d := by
    refine isExtent_iff.2 (Subset.antisymm (fun a ha => ?_) (subset_lowerPolar_upperPolar ..))
    rw [mem_lowerPolar_singleton]
    have h₁ : Concept.ofObject r a ≤ .ofObjects r (lowerPolar _ {d}) := Concept.ofObject_le_iff.2 ha
    have h₂ : φ (.ofObjects r (lowerPolar (fun a d => d ∈ (φ (.ofObject r a)).intent) {d})) ≤
        .ofAttribute s d := by
      rw [Concept.ofObjects_eq_iSup, map_iSup₂]
      exact iSup₂_le fun a' ha' => Concept.le_ofAttribute_iff.2 ((mem_lowerPolar_singleton _).1 ha')
    exact Concept.le_ofAttribute_iff.1 ((OrderHomClass.mono φ h₁).trans h₂)

theorem ofSSupHom_rel_iff {φ : sSupHom (Concept α β r) (Concept γ δ s)} {a : α} {d : δ} :
    (ofSSupHom φ).rel a d ↔ d ∈ (φ (.ofObject r a)).intent :=
  Iff.rfl

theorem ofSSupHom_rel_iff_le {φ : sSupHom (Concept α β r) (Concept γ δ s)} {a : α} {d : δ} :
    (ofSSupHom φ).rel a d ↔ φ (.ofObject r a) ≤ .ofAttribute s d :=
  Concept.le_ofAttribute_iff.symm

@[simp]
theorem ofSSupHom_map (j : Bond r s) : ofSSupHom j.map = j := by
  ext a d
  rw [ofSSupHom_rel_iff, intent_map_ofObject, mem_upperPolar_singleton]

@[simp]
theorem map_ofSSupHom (φ : sSupHom (Concept α β r) (Concept γ δ s)) : (ofSSupHom φ).map = φ := by
  refine sSupHom.ext fun c => Concept.ext' ?_
  conv_rhs => rw [← Concept.iSup_ofObject_extent c, map_iSup₂]
  ext d
  simp [mem_upperPolar_iff, ofSSupHom_rel_iff]

/-- Bonds from `r` to `s` correspond bijectively to supremum-preserving maps from the concept
lattice of `r` to the concept lattice of `s`. -/
@[simps]
def equivSSupHom : Bond r s ≃ sSupHom (Concept α β r) (Concept γ δ s) where
  toFun := map
  invFun := ofSSupHom
  left_inv := ofSSupHom_map
  right_inv := map_ofSSupHom

end Bond

end FCA
