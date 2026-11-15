/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Order.Concept

/-!
# Constructions of formal contexts

A formal context is a relation `r : α → β → Prop`. This file collects the standard constructions
of new contexts from old ones and computes their derivation operators `upperPolar`, `lowerPolar`
and, where possible, their extents, intents and concept lattices.

## Main definitions

* `FCA.complement`: the complementary context.
* `FCA.apposition`, `FCA.subposition`: glueing two contexts along a common object set
  (respectively a common attribute set).
* `FCA.restrict`, `FCA.restrictObjects`, `FCA.restrictAttributes`: subcontexts.
* `FCA.disjointUnion`, `FCA.directSum`: disjoint union and direct sum of two contexts.
* `Concept.orderIsoOfIsExtentIff`, `Concept.orderIsoOfIsIntentIff`: contexts with the same extents
  (intents) have isomorphic concept lattices.
* `Concept.comapOrderIso`: an incidence preserving and reflecting pair of surjections induces an
  isomorphism of concept lattices.
* `FCA.restrictAttributesOrderIso`, `FCA.restrictObjectsOrderIso`: restricting a context to a
  dense set of attributes (objects) does not change the concept lattice.
* `FCA.directSumOrderIso`: the concept lattice of a direct sum is the product of the concept
  lattices.

## Main results

* `Order.isExtent_swap`, `Order.isIntent_swap`: extents of the dual context `Function.swap r` are
  the intents of `r` and vice versa. The isomorphism of concept lattices is Mathlib's
  `Concept.swapEquiv`.
* `FCA.lowerPolar_apposition`, `FCA.upperPolar_apposition`: derivation in an apposition.
* `FCA.isExtent_apposition_iff`: the extents of an apposition are the intersections of extents of
  the two parts.
* `FCA.isIntent_subposition_iff`: the intents of a subposition are the intersections of intents
  of the two parts.
* `FCA.isExtent_restrictObjects_iff`: the extents of a subcontext with all attributes are the
  traces of the extents of the full context.
* `FCA.IsExtent.of_restrictAttributes`: the extents of a subcontext with all objects are extents
  of the full context.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

/-! ### The dual context -/

namespace Order

variable {α β : Type*} {r : α → β → Prop} {s : Set α} {t : Set β}

/-- The extents of the dual context are the intents of the context. -/
@[simp]
theorem isExtent_swap : IsExtent (swap r) t ↔ IsIntent r t :=
  Iff.rfl

/-- The intents of the dual context are the extents of the context. -/
@[simp]
theorem isIntent_swap : IsIntent (swap r) s ↔ IsExtent r s :=
  Iff.rfl

end Order

/-! ### Isomorphisms of concept lattices -/

section Surjective

variable {α α' β β' : Type*} {r : α → β → Prop} {r' : α' → β' → Prop} {f : α → α'} {g : β → β'}

theorem lowerPolar_preimage_of_surjective (hg : Surjective g) (h : ∀ a b, r' (f a) (g b) ↔ r a b)
    (t : Set β') : lowerPolar r (g ⁻¹' t) = f ⁻¹' lowerPolar r' t := by
  ext a
  refine ⟨fun ha b' hb' ↦ ?_, fun ha b hb ↦ (h a b).1 (ha hb)⟩
  obtain ⟨b, rfl⟩ := hg b'
  exact (h a b).2 (ha hb')

theorem upperPolar_preimage_of_surjective (hf : Surjective f) (h : ∀ a b, r' (f a) (g b) ↔ r a b)
    (s : Set α') : upperPolar r (f ⁻¹' s) = g ⁻¹' upperPolar r' s :=
  lowerPolar_preimage_of_surjective (r := swap r) (r' := swap r') hf (fun b a ↦ h a b) s

theorem upperPolar_image_of_surjective (hg : Surjective g) (h : ∀ a b, r' (f a) (g b) ↔ r a b)
    (s : Set α) : upperPolar r' (f '' s) = g '' upperPolar r s := by
  ext b'
  obtain ⟨b, rfl⟩ := hg b'
  constructor
  · exact fun hb ↦ ⟨b, fun a ha ↦ (h a b).1 (hb (mem_image_of_mem f ha)), rfl⟩
  · rintro ⟨b₀, hb₀, hb⟩ _ ⟨a, ha, rfl⟩
    exact hb ▸ (h a b₀).2 (hb₀ ha)

theorem lowerPolar_image_of_surjective (hf : Surjective f) (h : ∀ a b, r' (f a) (g b) ↔ r a b)
    (t : Set β) : lowerPolar r' (g '' t) = f '' lowerPolar r t :=
  upperPolar_image_of_surjective (r := swap r) (r' := swap r') hf (fun b a ↦ h a b) t

end Surjective

namespace Concept

variable {α α' β β' : Type*}

/-- Two contexts on the same set of objects which have the same extents have isomorphic concept
lattices. -/
def orderIsoOfIsExtentIff {r : α → β → Prop} {r' : α → β' → Prop}
    (h : ∀ s, IsExtent r s ↔ IsExtent r' s) : Concept α β r ≃o Concept α β' r' where
  toFun c := ofIsExtent r' c.extent ((h _).1 c.isExtent_extent)
  invFun c := ofIsExtent r c.extent ((h _).2 c.isExtent_extent)
  left_inv _ := ext rfl
  right_inv _ := ext rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem extent_orderIsoOfIsExtentIff {r : α → β → Prop} {r' : α → β' → Prop}
    (h : ∀ s, IsExtent r s ↔ IsExtent r' s) (c : Concept α β r) :
    (orderIsoOfIsExtentIff h c).extent = c.extent :=
  rfl

@[simp]
theorem extent_orderIsoOfIsExtentIff_symm {r : α → β → Prop} {r' : α → β' → Prop}
    (h : ∀ s, IsExtent r s ↔ IsExtent r' s) (c : Concept α β' r') :
    ((orderIsoOfIsExtentIff h).symm c).extent = c.extent :=
  rfl

/-- Two contexts on the same set of attributes which have the same intents have isomorphic concept
lattices. -/
def orderIsoOfIsIntentIff {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ t, IsIntent r t ↔ IsIntent r' t) : Concept α β r ≃o Concept α' β r' where
  toFun c := ofIsIntent r' c.intent ((h _).1 c.isIntent_intent)
  invFun c := ofIsIntent r c.intent ((h _).2 c.isIntent_intent)
  left_inv _ := ext' rfl
  right_inv _ := ext' rfl
  map_rel_iff' {c d} := by
    rw [← intent_subset_intent_iff, ← intent_subset_intent_iff (c := d)]
    rfl

@[simp]
theorem intent_orderIsoOfIsIntentIff {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ t, IsIntent r t ↔ IsIntent r' t) (c : Concept α β r) :
    (orderIsoOfIsIntentIff h c).intent = c.intent :=
  rfl

@[simp]
theorem intent_orderIsoOfIsIntentIff_symm {r : α → β → Prop} {r' : α' → β → Prop}
    (h : ∀ t, IsIntent r t ↔ IsIntent r' t) (c : Concept α' β r') :
    ((orderIsoOfIsIntentIff h).symm c).intent = c.intent :=
  rfl

variable {r : α → β → Prop} {r' : α' → β' → Prop} {f : α → α'} {g : β → β'}

/-- A pair of surjections `f : α → α'`, `g : β → β'` which preserves and reflects incidence
induces an isomorphism of concept lattices, given by taking preimages of extents and intents. -/
def comapOrderIso (hf : Surjective f) (hg : Surjective g) (h : ∀ a b, r' (f a) (g b) ↔ r a b) :
    Concept α' β' r' ≃o Concept α β r where
  toFun c :=
    { extent := f ⁻¹' c.extent
      intent := g ⁻¹' c.intent
      upperPolar_extent := by rw [upperPolar_preimage_of_surjective hf h, c.upperPolar_extent]
      lowerPolar_intent := by rw [lowerPolar_preimage_of_surjective hg h, c.lowerPolar_intent] }
  invFun c :=
    { extent := f '' c.extent
      intent := g '' c.intent
      upperPolar_extent := by rw [upperPolar_image_of_surjective hg h, c.upperPolar_extent]
      lowerPolar_intent := by rw [lowerPolar_image_of_surjective hf h, c.lowerPolar_intent] }
  left_inv c := ext (image_preimage_eq _ hf)
  right_inv c := by
    refine ext (subset_antisymm ?_ (subset_preimage_image f _))
    rintro a ⟨a₀, ha₀, ha⟩
    rw [← c.lowerPolar_intent] at ha₀ ⊢
    exact fun b hb ↦ (h a b).1 (ha ▸ (h a₀ b).2 (ha₀ hb))
  map_rel_iff' := hf.preimage_subset_preimage_iff

@[simp]
theorem extent_comapOrderIso (hf : Surjective f) (hg : Surjective g)
    (h : ∀ a b, r' (f a) (g b) ↔ r a b) (c : Concept α' β' r') :
    (comapOrderIso hf hg h c).extent = f ⁻¹' c.extent :=
  rfl

@[simp]
theorem intent_comapOrderIso (hf : Surjective f) (hg : Surjective g)
    (h : ∀ a b, r' (f a) (g b) ↔ r a b) (c : Concept α' β' r') :
    (comapOrderIso hf hg h c).intent = g ⁻¹' c.intent :=
  rfl

@[simp]
theorem extent_comapOrderIso_symm (hf : Surjective f) (hg : Surjective g)
    (h : ∀ a b, r' (f a) (g b) ↔ r a b) (c : Concept α β r) :
    ((comapOrderIso hf hg h).symm c).extent = f '' c.extent :=
  rfl

@[simp]
theorem intent_comapOrderIso_symm (hf : Surjective f) (hg : Surjective g)
    (h : ∀ a b, r' (f a) (g b) ↔ r a b) (c : Concept α β r) :
    ((comapOrderIso hf hg h).symm c).intent = g '' c.intent :=
  rfl

end Concept

namespace FCA

variable {α β α₁ α₂ β₁ β₂ : Type*}

/-! ### The complementary context -/

section Compl

variable {r : α → β → Prop} {s : Set α} {t : Set β} {a : α} {b : β}

/-- The *complementary context* of `r`: an object has an attribute in `complement r` iff it does not
have it in `r`. -/
def complement (r : α → β → Prop) : α → β → Prop :=
  fun a b ↦ ¬ r a b

/-- The complementary context is the pointwise complement `rᶜ` of the relation. -/
theorem complement_eq_compl (r : α → β → Prop) : complement r = rᶜ :=
  rfl

@[simp]
theorem complement_apply : complement r a b ↔ ¬ r a b :=
  Iff.rfl

@[simp]
theorem complement_complement (r : α → β → Prop) : complement (complement r) = r := by
  ext a b
  exact not_not

theorem complement_injective : Injective (complement : (α → β → Prop) → α → β → Prop) :=
  LeftInverse.injective complement_complement

theorem swap_complement (r : α → β → Prop) : swap (complement r) = complement (swap r) :=
  rfl

theorem mem_upperPolar_complement : b ∈ upperPolar (complement r) s ↔ ∀ a ∈ s, ¬ r a b :=
  Iff.rfl

theorem mem_lowerPolar_complement : a ∈ lowerPolar (complement r) t ↔ ∀ b ∈ t, ¬ r a b :=
  Iff.rfl

/-- The object intents of the complementary context are the complements of the object intents. -/
@[simp]
theorem upperPolar_complement_singleton (r : α → β → Prop) (a : α) :
    upperPolar (complement r) {a} = (upperPolar r {a})ᶜ := by
  ext b
  simp

/-- The attribute extents of the complementary context are the complements of the attribute
extents. -/
@[simp]
theorem lowerPolar_complement_singleton (r : α → β → Prop) (b : β) :
    lowerPolar (complement r) {b} = (lowerPolar r {b})ᶜ := by
  ext a
  simp

theorem upperPolar_complement (r : α → β → Prop) (s : Set α) :
    upperPolar (complement r) s = ⋂ a ∈ s, (upperPolar r {a})ᶜ := by
  ext b
  simp [mem_upperPolar_iff]

theorem lowerPolar_complement (r : α → β → Prop) (t : Set β) :
    lowerPolar (complement r) t = ⋂ b ∈ t, (lowerPolar r {b})ᶜ := by
  ext a
  simp [mem_lowerPolar_iff]

end Compl

/-! ### Apposition -/

section Apposition

variable {r₁ : α → β₁ → Prop} {r₂ : α → β₂ → Prop} {s : Set α} {a : α}

/-- The *apposition* `r₁ | r₂` of two contexts with the same objects: the attributes are the
disjoint union of the attributes of `r₁` and `r₂`. -/
def apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) : α → β₁ ⊕ β₂ → Prop :=
  fun a ↦ Sum.elim (r₁ a) (r₂ a)

@[simp]
theorem apposition_inl {b : β₁} : apposition r₁ r₂ a (.inl b) ↔ r₁ a b :=
  Iff.rfl

@[simp]
theorem apposition_inr {b : β₂} : apposition r₁ r₂ a (.inr b) ↔ r₂ a b :=
  Iff.rfl

theorem lowerPolar_apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) (t : Set (β₁ ⊕ β₂)) :
    lowerPolar (apposition r₁ r₂) t =
      lowerPolar r₁ (Sum.inl ⁻¹' t) ∩ lowerPolar r₂ (Sum.inr ⁻¹' t) := by
  ext a
  simp [mem_lowerPolar_iff]

theorem upperPolar_apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) (s : Set α) :
    upperPolar (apposition r₁ r₂) s = Sum.inl '' upperPolar r₁ s ∪ Sum.inr '' upperPolar r₂ s := by
  ext (b | b) <;> simp [mem_upperPolar_iff]

@[simp]
theorem preimage_inl_upperPolar_apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) (s : Set α) :
    Sum.inl ⁻¹' upperPolar (apposition r₁ r₂) s = upperPolar r₁ s :=
  rfl

@[simp]
theorem preimage_inr_upperPolar_apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) (s : Set α) :
    Sum.inr ⁻¹' upperPolar (apposition r₁ r₂) s = upperPolar r₂ s :=
  rfl

/-- The extents of an apposition are exactly the intersections of an extent of the first context
with an extent of the second context. -/
theorem isExtent_apposition_iff :
    IsExtent (apposition r₁ r₂) s ↔ ∃ s₁ s₂, IsExtent r₁ s₁ ∧ IsExtent r₂ s₂ ∧ s₁ ∩ s₂ = s := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, _, isExtent_lowerPolar, isExtent_lowerPolar, (lowerPolar_apposition ..).symm⟩
  · rintro ⟨_, _, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩, rfl⟩
    refine ⟨Sum.inl '' t₁ ∪ Sum.inr '' t₂, ?_⟩
    simp [lowerPolar_apposition, preimage_image_eq _ Sum.inl_injective,
      preimage_image_eq _ Sum.inr_injective]

/-- Every extent of the first context is an extent of the apposition. -/
theorem IsExtent.apposition_left (h : IsExtent r₁ s) : IsExtent (apposition r₁ r₂) s :=
  isExtent_apposition_iff.2 ⟨s, univ, h, .univ, inter_univ s⟩

/-- Every extent of the second context is an extent of the apposition. -/
theorem IsExtent.apposition_right (h : IsExtent r₂ s) : IsExtent (apposition r₁ r₂) s :=
  isExtent_apposition_iff.2 ⟨univ, s, .univ, h, univ_inter s⟩

/-- The first component of an intent of an apposition is an intent of the first context. -/
theorem IsIntent.preimage_inl_of_apposition {t : Set (β₁ ⊕ β₂)}
    (h : IsIntent (apposition r₁ r₂) t) : IsIntent r₁ (Sum.inl ⁻¹' t) := by
  obtain ⟨s, rfl⟩ := h
  exact isIntent_upperPolar

/-- The second component of an intent of an apposition is an intent of the second context. -/
theorem IsIntent.preimage_inr_of_apposition {t : Set (β₁ ⊕ β₂)}
    (h : IsIntent (apposition r₁ r₂) t) : IsIntent r₂ (Sum.inr ⁻¹' t) := by
  obtain ⟨s, rfl⟩ := h
  exact isIntent_upperPolar

end Apposition

/-! ### Subposition -/

section Subposition

variable {r₁ : α₁ → β → Prop} {r₂ : α₂ → β → Prop} {t : Set β} {b : β}

/-- The *subposition* of two contexts with the same attributes: the objects are the disjoint union
of the objects of `r₁` and `r₂`. -/
def subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop) : α₁ ⊕ α₂ → β → Prop :=
  fun a b ↦ Sum.elim (r₁ · b) (r₂ · b) a

@[simp]
theorem subposition_inl {a : α₁} : subposition r₁ r₂ (.inl a) b ↔ r₁ a b :=
  Iff.rfl

@[simp]
theorem subposition_inr {a : α₂} : subposition r₁ r₂ (.inr a) b ↔ r₂ a b :=
  Iff.rfl

/-- The dual of a subposition is the apposition of the duals. -/
theorem swap_subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop) :
    swap (subposition r₁ r₂) = apposition (swap r₁) (swap r₂) :=
  rfl

/-- The dual of an apposition is the subposition of the duals. -/
theorem swap_apposition (r₁ : α → β₁ → Prop) (r₂ : α → β₂ → Prop) :
    swap (apposition r₁ r₂) = subposition (swap r₁) (swap r₂) :=
  rfl

theorem upperPolar_subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop) (s : Set (α₁ ⊕ α₂)) :
    upperPolar (subposition r₁ r₂) s =
      upperPolar r₁ (Sum.inl ⁻¹' s) ∩ upperPolar r₂ (Sum.inr ⁻¹' s) :=
  lowerPolar_apposition (swap r₁) (swap r₂) s

theorem lowerPolar_subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop) (t : Set β) :
    lowerPolar (subposition r₁ r₂) t = Sum.inl '' lowerPolar r₁ t ∪ Sum.inr '' lowerPolar r₂ t :=
  upperPolar_apposition (swap r₁) (swap r₂) t

@[simp]
theorem preimage_inl_lowerPolar_subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop)
    (t : Set β) : Sum.inl ⁻¹' lowerPolar (subposition r₁ r₂) t = lowerPolar r₁ t :=
  rfl

@[simp]
theorem preimage_inr_lowerPolar_subposition (r₁ : α₁ → β → Prop) (r₂ : α₂ → β → Prop)
    (t : Set β) : Sum.inr ⁻¹' lowerPolar (subposition r₁ r₂) t = lowerPolar r₂ t :=
  rfl

/-- The intents of a subposition are exactly the intersections of an intent of the first context
with an intent of the second context. -/
theorem isIntent_subposition_iff :
    IsIntent (subposition r₁ r₂) t ↔ ∃ t₁ t₂, IsIntent r₁ t₁ ∧ IsIntent r₂ t₂ ∧ t₁ ∩ t₂ = t :=
  isExtent_apposition_iff (r₁ := swap r₁) (r₂ := swap r₂)

/-- Every intent of the first context is an intent of the subposition. -/
theorem IsIntent.subposition_left (h : IsIntent r₁ t) : IsIntent (subposition r₁ r₂) t :=
  isIntent_subposition_iff.2 ⟨t, univ, h, .univ, inter_univ t⟩

/-- Every intent of the second context is an intent of the subposition. -/
theorem IsIntent.subposition_right (h : IsIntent r₂ t) : IsIntent (subposition r₁ r₂) t :=
  isIntent_subposition_iff.2 ⟨univ, t, .univ, h, univ_inter t⟩

/-- The first component of an extent of a subposition is an extent of the first context. -/
theorem IsExtent.preimage_inl_of_subposition {s : Set (α₁ ⊕ α₂)}
    (h : IsExtent (subposition r₁ r₂) s) : IsExtent r₁ (Sum.inl ⁻¹' s) := by
  obtain ⟨t, rfl⟩ := h
  exact isExtent_lowerPolar

/-- The second component of an extent of a subposition is an extent of the second context. -/
theorem IsExtent.preimage_inr_of_subposition {s : Set (α₁ ⊕ α₂)}
    (h : IsExtent (subposition r₁ r₂) s) : IsExtent r₂ (Sum.inr ⁻¹' s) := by
  obtain ⟨t, rfl⟩ := h
  exact isExtent_lowerPolar

end Subposition

/-! ### Subcontexts -/

section Restrict

variable {r : α → β → Prop} {s : Set α} {t : Set β}

/-- The subcontext of `r` with object set `s` and all attributes. -/
def restrictObjects (r : α → β → Prop) (s : Set α) : s → β → Prop :=
  fun a b ↦ r a b

/-- The subcontext of `r` with all objects and attribute set `t`. -/
def restrictAttributes (r : α → β → Prop) (t : Set β) : α → t → Prop :=
  fun a b ↦ r a b

/-- The subcontext of `r` with object set `s` and attribute set `t`. -/
def restrict (r : α → β → Prop) (s : Set α) (t : Set β) : s → t → Prop :=
  fun a b ↦ r a b

@[simp]
theorem restrictObjects_apply {a : s} {b : β} : restrictObjects r s a b ↔ r a b :=
  Iff.rfl

@[simp]
theorem restrictAttributes_apply {a : α} {b : t} : restrictAttributes r t a b ↔ r a b :=
  Iff.rfl

@[simp]
theorem restrict_apply {a : s} {b : t} : restrict r s t a b ↔ r a b :=
  Iff.rfl

theorem restrictAttributes_restrictObjects (r : α → β → Prop) (s : Set α) (t : Set β) :
    restrictAttributes (restrictObjects r s) t = restrict r s t :=
  rfl

theorem restrictObjects_restrictAttributes (r : α → β → Prop) (s : Set α) (t : Set β) :
    restrictObjects (restrictAttributes r t) s = restrict r s t :=
  rfl

theorem swap_restrictObjects (r : α → β → Prop) (s : Set α) :
    swap (restrictObjects r s) = restrictAttributes (swap r) s :=
  rfl

theorem swap_restrictAttributes (r : α → β → Prop) (t : Set β) :
    swap (restrictAttributes r t) = restrictObjects (swap r) t :=
  rfl

theorem swap_restrict (r : α → β → Prop) (s : Set α) (t : Set β) :
    swap (restrict r s t) = restrict (swap r) t s :=
  rfl

theorem lowerPolar_restrictObjects (r : α → β → Prop) (s : Set α) (u : Set β) :
    lowerPolar (restrictObjects r s) u = Subtype.val ⁻¹' lowerPolar r u :=
  rfl

theorem upperPolar_restrictObjects (r : α → β → Prop) (s : Set α) (u : Set s) :
    upperPolar (restrictObjects r s) u = upperPolar r (Subtype.val '' u) := by
  ext b
  simp [mem_upperPolar_iff]

theorem upperPolar_restrictAttributes (r : α → β → Prop) (t : Set β) (u : Set α) :
    upperPolar (restrictAttributes r t) u = Subtype.val ⁻¹' upperPolar r u :=
  rfl

theorem lowerPolar_restrictAttributes (r : α → β → Prop) (t : Set β) (u : Set t) :
    lowerPolar (restrictAttributes r t) u = lowerPolar r (Subtype.val '' u) :=
  upperPolar_restrictObjects (swap r) t u

theorem lowerPolar_restrict (r : α → β → Prop) (s : Set α) (t : Set β) (u : Set t) :
    lowerPolar (restrict r s t) u = Subtype.val ⁻¹' lowerPolar r (Subtype.val '' u) := by
  rw [← restrictObjects_restrictAttributes, lowerPolar_restrictObjects,
    lowerPolar_restrictAttributes]

theorem upperPolar_restrict (r : α → β → Prop) (s : Set α) (t : Set β) (u : Set s) :
    upperPolar (restrict r s t) u = Subtype.val ⁻¹' upperPolar r (Subtype.val '' u) :=
  lowerPolar_restrict (swap r) t s u

/-- The extents of a subcontext which keeps all attributes are exactly the traces of the extents
of the full context on the smaller object set. -/
theorem isExtent_restrictObjects_iff {u : Set s} :
    IsExtent (restrictObjects r s) u ↔ ∃ e, IsExtent r e ∧ Subtype.val ⁻¹' e = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, isExtent_lowerPolar, rfl⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩

/-- The intents of a subcontext which keeps all objects are exactly the traces of the intents of
the full context on the smaller attribute set. -/
theorem isIntent_restrictAttributes_iff {u : Set t} :
    IsIntent (restrictAttributes r t) u ↔ ∃ i, IsIntent r i ∧ Subtype.val ⁻¹' i = u :=
  isExtent_restrictObjects_iff (r := swap r)

/-- Every extent of a subcontext which keeps all objects is an extent of the full context. -/
theorem IsExtent.of_restrictAttributes {e : Set α} (h : IsExtent (restrictAttributes r t) e) :
    IsExtent r e := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨_, (lowerPolar_restrictAttributes r t u).symm⟩

/-- Every intent of a subcontext which keeps all attributes is an intent of the full context. -/
theorem IsIntent.of_restrictObjects {i : Set β} (h : IsIntent (restrictObjects r s) i) :
    IsIntent r i :=
  IsExtent.of_restrictAttributes (r := swap r) h

/-- Every extent of a subcontext is the trace of an extent of the full context. -/
theorem IsExtent.exists_of_restrict {u : Set s} (h : IsExtent (restrict r s t) u) :
    ∃ e, IsExtent r e ∧ Subtype.val ⁻¹' e = u := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨_, isExtent_lowerPolar, (lowerPolar_restrict r s t v).symm⟩

/-- Every intent of a subcontext is the trace of an intent of the full context. -/
theorem IsIntent.exists_of_restrict {u : Set t} (h : IsIntent (restrict r s t) u) :
    ∃ i, IsIntent r i ∧ Subtype.val ⁻¹' i = u :=
  IsExtent.exists_of_restrict (r := swap r) h

/-- If every attribute extent is the extent of a set of attributes in `t` (that is, the attribute
concepts of `t` are infimum-dense), then the subcontext with attribute set `t` has the same
extents as the full context. -/
theorem isExtent_restrictAttributes_iff_of_dense
    (ht : ∀ b, ∃ u ⊆ t, lowerPolar r u = lowerPolar r {b}) {e : Set α} :
    IsExtent (restrictAttributes r t) e ↔ IsExtent r e := by
  refine ⟨IsExtent.of_restrictAttributes, ?_⟩
  rintro ⟨v, rfl⟩
  choose u hut hu using ht
  refine ⟨Subtype.val ⁻¹' ⋃ b ∈ v, u b, ?_⟩
  rw [lowerPolar_restrictAttributes, Subtype.image_preimage_coe,
    inter_eq_self_of_subset_right (iUnion₂_subset fun b _ ↦ hut b), lowerPolar_iUnion₂]
  simp_rw [hu]
  rw [← lowerPolar_iUnion₂, biUnion_of_singleton]

/-- If every object intent is the intent of a set of objects in `s` (that is, the object concepts
of `s` are supremum-dense), then the subcontext with object set `s` has the same intents as the
full context. -/
theorem isIntent_restrictObjects_iff_of_dense
    (hs : ∀ a, ∃ u ⊆ s, upperPolar r u = upperPolar r {a}) {i : Set β} :
    IsIntent (restrictObjects r s) i ↔ IsIntent r i :=
  isExtent_restrictAttributes_iff_of_dense (r := swap r) hs

/-- Restricting a context to an infimum-dense set of attributes does not change the concept
lattice. -/
def restrictAttributesOrderIso (ht : ∀ b, ∃ u ⊆ t, lowerPolar r u = lowerPolar r {b}) :
    Concept α t (restrictAttributes r t) ≃o Concept α β r :=
  Concept.orderIsoOfIsExtentIff fun _ ↦ isExtent_restrictAttributes_iff_of_dense ht

@[simp]
theorem extent_restrictAttributesOrderIso
    (ht : ∀ b, ∃ u ⊆ t, lowerPolar r u = lowerPolar r {b})
    (c : Concept α t (restrictAttributes r t)) :
    (restrictAttributesOrderIso ht c).extent = c.extent :=
  rfl

/-- Restricting a context to a supremum-dense set of objects does not change the concept
lattice. -/
def restrictObjectsOrderIso (hs : ∀ a, ∃ u ⊆ s, upperPolar r u = upperPolar r {a}) :
    Concept s β (restrictObjects r s) ≃o Concept α β r :=
  Concept.orderIsoOfIsIntentIff fun _ ↦ isIntent_restrictObjects_iff_of_dense hs

@[simp]
theorem intent_restrictObjectsOrderIso
    (hs : ∀ a, ∃ u ⊆ s, upperPolar r u = upperPolar r {a})
    (c : Concept s β (restrictObjects r s)) :
    (restrictObjectsOrderIso hs c).intent = c.intent :=
  rfl

end Restrict

/-! ### Disjoint union and direct sum -/

section Sum

variable {r₁ : α₁ → β₁ → Prop} {r₂ : α₂ → β₂ → Prop}

/-- The *disjoint union* of two contexts: objects and attributes are the disjoint unions, and
objects of one context are not incident with attributes of the other one. -/
def disjointUnion (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) : α₁ ⊕ α₂ → β₁ ⊕ β₂ → Prop :=
  Sum.elim (fun a ↦ Sum.elim (r₁ a) fun _ ↦ False) fun a ↦ Sum.elim (fun _ ↦ False) (r₂ a)

/-- The *direct sum* of two contexts: objects and attributes are the disjoint unions, and
objects of one context are incident with all attributes of the other one. -/
def directSum (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) : α₁ ⊕ α₂ → β₁ ⊕ β₂ → Prop :=
  Sum.elim (fun a ↦ Sum.elim (r₁ a) fun _ ↦ True) fun a ↦ Sum.elim (fun _ ↦ True) (r₂ a)

@[simp]
theorem disjointUnion_inl_inl {a : α₁} {b : β₁} :
    disjointUnion r₁ r₂ (.inl a) (.inl b) ↔ r₁ a b :=
  Iff.rfl

@[simp]
theorem disjointUnion_inr_inr {a : α₂} {b : β₂} :
    disjointUnion r₁ r₂ (.inr a) (.inr b) ↔ r₂ a b :=
  Iff.rfl

@[simp]
theorem not_disjointUnion_inl_inr {a : α₁} {b : β₂} : ¬ disjointUnion r₁ r₂ (.inl a) (.inr b) :=
  id

@[simp]
theorem not_disjointUnion_inr_inl {a : α₂} {b : β₁} : ¬ disjointUnion r₁ r₂ (.inr a) (.inl b) :=
  id

@[simp]
theorem directSum_inl_inl {a : α₁} {b : β₁} : directSum r₁ r₂ (.inl a) (.inl b) ↔ r₁ a b :=
  Iff.rfl

@[simp]
theorem directSum_inr_inr {a : α₂} {b : β₂} : directSum r₁ r₂ (.inr a) (.inr b) ↔ r₂ a b :=
  Iff.rfl

@[simp]
theorem directSum_inl_inr {a : α₁} {b : β₂} : directSum r₁ r₂ (.inl a) (.inr b) :=
  trivial

@[simp]
theorem directSum_inr_inl {a : α₂} {b : β₁} : directSum r₁ r₂ (.inr a) (.inl b) :=
  trivial

theorem swap_disjointUnion (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) :
    swap (disjointUnion r₁ r₂) = disjointUnion (swap r₁) (swap r₂) := by
  ext (b | b) (a | a) <;> rfl

theorem swap_directSum (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) :
    swap (directSum r₁ r₂) = directSum (swap r₁) (swap r₂) := by
  ext (b | b) (a | a) <;> rfl

/-- The direct sum is the complement of the disjoint union of the complements. -/
theorem complement_directSum (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) :
    complement (directSum r₁ r₂) = disjointUnion (complement r₁) (complement r₂) := by
  ext (a | a) (b | b) <;> simp

/-- The disjoint union is the complement of the direct sum of the complements. -/
theorem complement_disjointUnion (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) :
    complement (disjointUnion r₁ r₂) = directSum (complement r₁) (complement r₂) := by
  ext (a | a) (b | b) <;> simp

theorem lowerPolar_directSum (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) (t : Set (β₁ ⊕ β₂)) :
    lowerPolar (directSum r₁ r₂) t =
      Sum.inl '' lowerPolar r₁ (Sum.inl ⁻¹' t) ∪ Sum.inr '' lowerPolar r₂ (Sum.inr ⁻¹' t) := by
  ext (a | a) <;> simp [mem_lowerPolar_iff]

theorem upperPolar_directSum (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) (s : Set (α₁ ⊕ α₂)) :
    upperPolar (directSum r₁ r₂) s =
      Sum.inl '' upperPolar r₁ (Sum.inl ⁻¹' s) ∪ Sum.inr '' upperPolar r₂ (Sum.inr ⁻¹' s) := by
  rw [← lowerPolar_swap, swap_directSum, lowerPolar_directSum]
  rfl

theorem inl_mem_lowerPolar_disjointUnion {a : α₁} {t : Set (β₁ ⊕ β₂)} :
    .inl a ∈ lowerPolar (disjointUnion r₁ r₂) t ↔
      a ∈ lowerPolar r₁ (Sum.inl ⁻¹' t) ∧ Sum.inr ⁻¹' t = ∅ := by
  simp [mem_lowerPolar_iff, eq_empty_iff_forall_notMem]

theorem inr_mem_lowerPolar_disjointUnion {a : α₂} {t : Set (β₁ ⊕ β₂)} :
    .inr a ∈ lowerPolar (disjointUnion r₁ r₂) t ↔
      a ∈ lowerPolar r₂ (Sum.inr ⁻¹' t) ∧ Sum.inl ⁻¹' t = ∅ := by
  simp [mem_lowerPolar_iff, eq_empty_iff_forall_notMem, and_comm]

theorem inl_mem_upperPolar_disjointUnion {b : β₁} {s : Set (α₁ ⊕ α₂)} :
    .inl b ∈ upperPolar (disjointUnion r₁ r₂) s ↔
      b ∈ upperPolar r₁ (Sum.inl ⁻¹' s) ∧ Sum.inr ⁻¹' s = ∅ := by
  simp [mem_upperPolar_iff, eq_empty_iff_forall_notMem]

theorem inr_mem_upperPolar_disjointUnion {b : β₂} {s : Set (α₁ ⊕ α₂)} :
    .inr b ∈ upperPolar (disjointUnion r₁ r₂) s ↔
      b ∈ upperPolar r₂ (Sum.inr ⁻¹' s) ∧ Sum.inl ⁻¹' s = ∅ := by
  simp [mem_upperPolar_iff, eq_empty_iff_forall_notMem, and_comm]

/-- The concept lattice of a direct sum of contexts is isomorphic to the product of the concept
lattices of the summands. -/
def directSumOrderIso (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) :
    Concept (α₁ ⊕ α₂) (β₁ ⊕ β₂) (directSum r₁ r₂) ≃o Concept α₁ β₁ r₁ × Concept α₂ β₂ r₂ where
  toFun c :=
    (⟨Sum.inl ⁻¹' c.extent, Sum.inl ⁻¹' c.intent,
        by rw [← c.upperPolar_extent, upperPolar_directSum]
           simp [preimage_image_eq _ Sum.inl_injective],
        by rw [← c.lowerPolar_intent, lowerPolar_directSum]
           simp [preimage_image_eq _ Sum.inl_injective]⟩,
      ⟨Sum.inr ⁻¹' c.extent, Sum.inr ⁻¹' c.intent,
        by rw [← c.upperPolar_extent, upperPolar_directSum]
           simp [preimage_image_eq _ Sum.inr_injective],
        by rw [← c.lowerPolar_intent, lowerPolar_directSum]
           simp [preimage_image_eq _ Sum.inr_injective]⟩)
  invFun p :=
    ⟨Sum.inl '' p.1.extent ∪ Sum.inr '' p.2.extent, Sum.inl '' p.1.intent ∪ Sum.inr '' p.2.intent,
      by rw [upperPolar_directSum]
         simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective],
      by rw [lowerPolar_directSum]
         simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]⟩
  left_inv c := Concept.ext (image_preimage_inl_union_image_preimage_inr c.extent)
  right_inv p := by
    refine Prod.ext (Concept.ext ?_) (Concept.ext ?_) <;>
      simp [preimage_image_eq _ Sum.inl_injective, preimage_image_eq _ Sum.inr_injective]
  map_rel_iff' {c d} := by
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨preimage_mono h, preimage_mono h⟩⟩
    rintro (a | a) ha
    exacts [h.1 ha, h.2 ha]

@[simp]
theorem extent_fst_directSumOrderIso (c : Concept (α₁ ⊕ α₂) (β₁ ⊕ β₂) (directSum r₁ r₂)) :
    (directSumOrderIso r₁ r₂ c).1.extent = Sum.inl ⁻¹' c.extent :=
  rfl

@[simp]
theorem extent_snd_directSumOrderIso (c : Concept (α₁ ⊕ α₂) (β₁ ⊕ β₂) (directSum r₁ r₂)) :
    (directSumOrderIso r₁ r₂ c).2.extent = Sum.inr ⁻¹' c.extent :=
  rfl

@[simp]
theorem intent_fst_directSumOrderIso (c : Concept (α₁ ⊕ α₂) (β₁ ⊕ β₂) (directSum r₁ r₂)) :
    (directSumOrderIso r₁ r₂ c).1.intent = Sum.inl ⁻¹' c.intent :=
  rfl

@[simp]
theorem intent_snd_directSumOrderIso (c : Concept (α₁ ⊕ α₂) (β₁ ⊕ β₂) (directSum r₁ r₂)) :
    (directSumOrderIso r₁ r₂ c).2.intent = Sum.inr ⁻¹' c.intent :=
  rfl

end Sum

end FCA
