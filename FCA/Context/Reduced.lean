/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Clarified
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Irreducible

/-!
# Reducible attributes and objects, reduced contexts

An attribute `b` of a formal context `r : α → β → Prop` is *reducible* if its attribute extent is
the intersection of the attribute extents properly containing it. Equivalently, the attribute
concept of `b` is not completely meet-irreducible in the concept lattice. Reducible attributes can
be deleted without changing the concept lattice. Dually for objects.

## Main definitions

* `FCA.AttributeReducible`, `FCA.AttributeIrreducible`: reducible and irreducible attributes.
* `FCA.ObjectReducible`, `FCA.ObjectIrreducible`: reducible and irreducible objects.
* `FCA.AttributeReduced`, `FCA.ObjectReduced`, `FCA.Reduced`: reduced contexts.
* `FCA.AttributeWellFounded`, `FCA.ObjectWellFounded`: strict inclusion of attribute extents
  (object intents) has no infinite ascending chains; this holds in particular if the set of
  objects or the set of attributes is finite.
* `FCA.deleteAttributeOrderIso`, `FCA.deleteObjectOrderIso`: deleting a reducible attribute
  (object) does not change the concept lattice.
* `FCA.reduceAttributesOrderIso`, `FCA.reduceObjectsOrderIso`: in a well-founded context,
  deleting all reducible attributes (objects) at once does not change the concept lattice.

## Main results

* `FCA.attributeIrreducible_iff_forall_sInf`: an attribute is irreducible iff its attribute concept
  is completely meet-irreducible, that is, it belongs to every set of concepts of which it is
  the infimum.
* `FCA.objectIrreducible_iff_forall_sSup`: an object is irreducible iff its object concept is
  completely join-irreducible.
* `FCA.attributeIrreducible_iff_infIrred`, `FCA.objectIrreducible_iff_supIrred`: for a finite set
  of objects (or attributes) this agrees with Mathlib's `InfIrred` and `SupIrred`.
* `FCA.attributeReducible_iff_exists_of_attributeClarified`: in an attribute clarified context,
  `b` is reducible iff there is a set of attributes not containing `b` with the same extent.
* `FCA.AttributeWellFounded.exists_irreducible`: in a well-founded context the irreducible
  attributes are infimum-dense.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

theorem lowerPolar_eq_biInter {α β : Type*} (r : α → β → Prop) (t : Set β) :
    lowerPolar r t = ⋂ b ∈ t, lowerPolar r {b} := by
  rw [← lowerPolar_iUnion₂, biUnion_of_singleton]

theorem upperPolar_eq_biInter {α β : Type*} (r : α → β → Prop) (s : Set α) :
    upperPolar r s = ⋂ a ∈ s, upperPolar r {a} :=
  lowerPolar_eq_biInter (swap r) s

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {a : α} {b : β}

/-! ### Reducible attributes and objects -/

/-- An attribute `b` is *reducible* if its attribute extent is the intersection of all attribute
extents properly containing it. In particular, an attribute shared by all objects is reducible. -/
def AttributeReducible (r : α → β → Prop) (b : β) : Prop :=
  lowerPolar r {b} = lowerPolar r {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}}

/-- An attribute is *irreducible* if it is not reducible. -/
def AttributeIrreducible (r : α → β → Prop) (b : β) : Prop :=
  ¬ AttributeReducible r b

/-- An object `a` is *reducible* if its object intent is the intersection of all object intents
properly containing it. In particular, an object having all attributes is reducible. -/
def ObjectReducible (r : α → β → Prop) (a : α) : Prop :=
  upperPolar r {a} = upperPolar r {a' | upperPolar r {a} ⊂ upperPolar r {a'}}

/-- An object is *irreducible* if it is not reducible. -/
def ObjectIrreducible (r : α → β → Prop) (a : α) : Prop :=
  ¬ ObjectReducible r a

@[simp]
theorem objectReducible_swap : ObjectReducible (swap r) b ↔ AttributeReducible r b :=
  Iff.rfl

@[simp]
theorem attributeReducible_swap : AttributeReducible (swap r) a ↔ ObjectReducible r a :=
  Iff.rfl

@[simp]
theorem objectIrreducible_swap : ObjectIrreducible (swap r) b ↔ AttributeIrreducible r b :=
  Iff.rfl

@[simp]
theorem attributeIrreducible_swap : AttributeIrreducible (swap r) a ↔ ObjectIrreducible r a :=
  Iff.rfl

@[simp]
theorem not_attributeIrreducible : ¬ AttributeIrreducible r b ↔ AttributeReducible r b :=
  not_not

@[simp]
theorem not_objectIrreducible : ¬ ObjectIrreducible r a ↔ ObjectReducible r a :=
  not_not

theorem lowerPolar_singleton_subset_lowerPolar_ssubset (r : α → β → Prop) (b : β) :
    lowerPolar r {b} ⊆ lowerPolar r {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}} :=
  fun _ ha b' (hb' : lowerPolar r {b} ⊂ lowerPolar r {b'}) ↦
    (mem_lowerPolar_singleton r).1 (hb'.subset ha)

theorem upperPolar_singleton_subset_upperPolar_ssubset (r : α → β → Prop) (a : α) :
    upperPolar r {a} ⊆ upperPolar r {a' | upperPolar r {a} ⊂ upperPolar r {a'}} :=
  lowerPolar_singleton_subset_lowerPolar_ssubset (swap r) a

theorem attributeReducible_iff_subset :
    AttributeReducible r b ↔
      lowerPolar r {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}} ⊆ lowerPolar r {b} :=
  ⟨fun h ↦ h.ge, fun h ↦ (lowerPolar_singleton_subset_lowerPolar_ssubset r b).antisymm h⟩

theorem objectReducible_iff_subset :
    ObjectReducible r a ↔
      upperPolar r {a' | upperPolar r {a} ⊂ upperPolar r {a'}} ⊆ upperPolar r {a} :=
  attributeReducible_iff_subset (r := swap r)

/-- An attribute is irreducible iff some object lacks it but has all attributes with a properly
larger attribute extent. -/
theorem attributeIrreducible_iff_exists :
    AttributeIrreducible r b ↔
      ∃ a, ¬ r a b ∧ ∀ b', lowerPolar r {b} ⊂ lowerPolar r {b'} → r a b' := by
  simp only [AttributeIrreducible, attributeReducible_iff_subset, not_subset, mem_lowerPolar_iff,
    mem_ofPred_eq, mem_singleton_iff, forall_eq]
  exact exists_congr fun a ↦ and_comm

/-- An object is irreducible iff some attribute does not apply to it but applies to all objects
with a properly larger object intent. -/
theorem objectIrreducible_iff_exists :
    ObjectIrreducible r a ↔
      ∃ b, ¬ r a b ∧ ∀ a', upperPolar r {a} ⊂ upperPolar r {a'} → r a' b :=
  attributeIrreducible_iff_exists (r := swap r)

/-- An attribute shared by all objects is reducible. -/
theorem attributeReducible_of_lowerPolar_eq_univ (h : lowerPolar r {b} = univ) :
    AttributeReducible r b :=
  attributeReducible_iff_subset.2 (h ▸ subset_univ _)

/-- An object having all attributes is reducible. -/
theorem objectReducible_of_upperPolar_eq_univ (h : upperPolar r {a} = univ) :
    ObjectReducible r a :=
  objectReducible_iff_subset.2 (h ▸ subset_univ _)

/-- The extent of a reducible attribute is the extent of a set of other attributes. -/
theorem AttributeReducible.exists_notMem (h : AttributeReducible r b) :
    ∃ t, b ∉ t ∧ lowerPolar r t = lowerPolar r {b} :=
  ⟨_, fun hb ↦ ssubset_irrefl (lowerPolar r {b}) hb, h.symm⟩

/-- The intent of a reducible object is the intent of a set of other objects. -/
theorem ObjectReducible.exists_notMem (h : ObjectReducible r a) :
    ∃ s, a ∉ s ∧ upperPolar r s = upperPolar r {a} :=
  AttributeReducible.exists_notMem (r := swap r) h

/-- In an attribute clarified context, an attribute is reducible iff its extent is the extent of
a set of other attributes. This is the definition of Ganter and Wille. -/
theorem attributeReducible_iff_exists_of_attributeClarified (hr : AttributeClarified r) :
    AttributeReducible r b ↔ ∃ t, b ∉ t ∧ lowerPolar r t = lowerPolar r {b} := by
  refine ⟨AttributeReducible.exists_notMem, fun ⟨t, hbt, ht⟩ ↦ ?_⟩
  rw [attributeReducible_iff_subset]
  refine (lowerPolar_anti r fun b' hb' ↦ ?_).trans ht.subset
  have hsub : lowerPolar r {b} ⊆ lowerPolar r {b'} :=
    ht ▸ lowerPolar_anti r (singleton_subset_iff.2 hb')
  exact hsub.ssubset_of_ne fun h ↦ hbt (hr h ▸ hb')

/-- In an object clarified context, an object is reducible iff its intent is the intent of a set
of other objects. -/
theorem objectReducible_iff_exists_of_objectClarified (hr : ObjectClarified r) :
    ObjectReducible r a ↔ ∃ s, a ∉ s ∧ upperPolar r s = upperPolar r {a} :=
  attributeReducible_iff_exists_of_attributeClarified (r := swap r) hr

/-! ### Irreducibility in the concept lattice -/

/-- An attribute is irreducible iff its attribute concept is completely meet-irreducible: it
belongs to every set of concepts whose infimum it is. -/
theorem attributeIrreducible_iff_forall_sInf :
    AttributeIrreducible r b ↔ ∀ S : Set (Concept α β r),
      sInf S = Concept.ofAttribute r b → Concept.ofAttribute r b ∈ S := by
  constructor
  · intro hb S hS
    by_contra hmem
    refine hb (attributeReducible_iff_subset.2 fun a ha ↦ ?_)
    have hmem' : a ∈ (sInf S).extent := by
      rw [Concept.extent_sInf]
      refine mem_iInter₂.2 fun c hc ↦ ?_
      have hlt : Concept.ofAttribute r b < c :=
        lt_of_le_of_ne (hS ▸ sInf_le hc) fun h ↦ hmem (h ▸ hc)
      rw [← c.lowerPolar_intent]
      intro b' hb'
      have hle : c ≤ Concept.ofAttribute r b' :=
        Concept.le_ofAttributes_iff.2 (singleton_subset_iff.2 hb')
      exact ha (Concept.extent_ssubset_extent_iff.2 (hlt.trans_le hle))
    rw [hS] at hmem'
    exact hmem'
  · intro h hb
    have hS : sInf (Concept.ofAttribute r '' {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}}) =
        Concept.ofAttribute r b := by
      refine Concept.ext ?_
      rw [Concept.extent_sInf, biInter_image]
      exact (lowerPolar_eq_biInter r _).symm.trans hb.symm
    obtain ⟨b', hb', hbb'⟩ := h _ hS
    exact hb'.ne (congrArg Concept.extent hbb').symm

/-- An object is irreducible iff its object concept is completely join-irreducible: it belongs to
every set of concepts whose supremum it is. -/
theorem objectIrreducible_iff_forall_sSup :
    ObjectIrreducible r a ↔ ∀ S : Set (Concept α β r),
      sSup S = Concept.ofObject r a → Concept.ofObject r a ∈ S := by
  constructor
  · intro ha S hS
    by_contra hmem
    refine ha (objectReducible_iff_subset.2 fun b hb ↦ ?_)
    have hmem' : b ∈ (sSup S).intent := by
      rw [Concept.intent_sSup]
      refine mem_iInter₂.2 fun c hc ↦ ?_
      have hlt : c < Concept.ofObject r a :=
        lt_of_le_of_ne (hS ▸ le_sSup hc) fun h ↦ hmem (h ▸ hc)
      rw [← c.upperPolar_extent]
      intro a' ha'
      have hle : Concept.ofObject r a' ≤ c :=
        Concept.ofObjects_le_iff.2 (singleton_subset_iff.2 ha')
      exact hb (Concept.intent_ssubset_intent_iff.2 (hle.trans_lt hlt))
    rw [hS] at hmem'
    exact hmem'
  · intro h ha
    have hS : sSup (Concept.ofObject r '' {a' | upperPolar r {a} ⊂ upperPolar r {a'}}) =
        Concept.ofObject r a := by
      refine Concept.ext' ?_
      rw [Concept.intent_sSup, biInter_image]
      exact (upperPolar_eq_biInter r _).symm.trans ha.symm
    obtain ⟨a', ha', haa'⟩ := h _ hS
    exact ha'.ne (congrArg Concept.intent haa').symm

/-- The attribute concept of an irreducible attribute is meet-irreducible. -/
theorem AttributeIrreducible.infIrred (h : AttributeIrreducible r b) :
    InfIrred (Concept.ofAttribute r b) := by
  rw [attributeIrreducible_iff_forall_sInf] at h
  refine ⟨fun hmax ↦ ?_, fun c d hcd ↦ ?_⟩
  · simpa using h ∅ (by rw [sInf_empty, isMax_iff_eq_top.1 hmax])
  · have := h {c, d} (by rw [sInf_pair, hcd])
    grind

/-- The object concept of an irreducible object is join-irreducible. -/
theorem ObjectIrreducible.supIrred (h : ObjectIrreducible r a) :
    SupIrred (Concept.ofObject r a) := by
  rw [objectIrreducible_iff_forall_sSup] at h
  refine ⟨fun hmin ↦ ?_, fun c d hcd ↦ ?_⟩
  · simpa using h ∅ (by rw [sSup_empty, isMin_iff_eq_bot.1 hmin])
  · have := h {c, d} (by rw [sSup_pair, hcd])
    grind

/-- If the concept lattice is finite, an attribute is irreducible iff its attribute concept is
meet-irreducible. -/
theorem attributeIrreducible_iff_infIrred [Finite (Concept α β r)] :
    AttributeIrreducible r b ↔ InfIrred (Concept.ofAttribute r b) := by
  refine ⟨AttributeIrreducible.infIrred, fun h ↦ attributeIrreducible_iff_forall_sInf.2 ?_⟩
  intro S hS
  rw [← S.toFinite.coe_toFinset, ← Finset.inf_id_eq_sInf] at hS
  obtain ⟨c, hc, rfl⟩ := h.finset_inf_eq hS
  simpa using hc

/-- If the concept lattice is finite, an object is irreducible iff its object concept is
join-irreducible. -/
theorem objectIrreducible_iff_supIrred [Finite (Concept α β r)] :
    ObjectIrreducible r a ↔ SupIrred (Concept.ofObject r a) := by
  refine ⟨ObjectIrreducible.supIrred, fun h ↦ objectIrreducible_iff_forall_sSup.2 ?_⟩
  intro S hS
  rw [← S.toFinite.coe_toFinset, ← Finset.sup_id_eq_sSup] at hS
  obtain ⟨c, hc, rfl⟩ := h.finset_sup_eq hS
  simpa using hc

/-- A context with finitely many objects has a finite concept lattice. -/
theorem finite_concept_of_finite_objects [Finite α] : Finite (Concept α β r) :=
  Finite.of_injective _ Concept.extent_injective

/-- A context with finitely many attributes has a finite concept lattice. -/
theorem finite_concept_of_finite_attributes [Finite β] : Finite (Concept α β r) :=
  Finite.of_injective _ Concept.intent_injective

/-! ### Deleting reducible attributes and objects -/

/-- Deleting a reducible attribute does not change the concept lattice. More generally this holds
for every attribute whose extent is the extent of a set of other attributes. -/
def deleteAttributeOrderIso (h : ∃ t, b ∉ t ∧ lowerPolar r t = lowerPolar r {b}) :
    Concept α ({b}ᶜ : Set β) (restrictAttributes r {b}ᶜ) ≃o Concept α β r :=
  restrictAttributesOrderIso fun b' ↦ by
    obtain rfl | hb' := eq_or_ne b' b
    · obtain ⟨t, hbt, ht⟩ := h
      exact ⟨t, fun x hx hxb ↦ hbt (mem_singleton_iff.1 hxb ▸ hx), ht⟩
    · exact ⟨{b'}, singleton_subset_iff.2 hb', rfl⟩

@[simp]
theorem extent_deleteAttributeOrderIso (h : ∃ t, b ∉ t ∧ lowerPolar r t = lowerPolar r {b})
    (c : Concept α ({b}ᶜ : Set β) (restrictAttributes r {b}ᶜ)) :
    (deleteAttributeOrderIso h c).extent = c.extent :=
  rfl

/-- Deleting a reducible object does not change the concept lattice. More generally this holds
for every object whose intent is the intent of a set of other objects. -/
def deleteObjectOrderIso (h : ∃ s, a ∉ s ∧ upperPolar r s = upperPolar r {a}) :
    Concept ({a}ᶜ : Set α) β (restrictObjects r {a}ᶜ) ≃o Concept α β r :=
  restrictObjectsOrderIso fun a' ↦ by
    obtain rfl | ha' := eq_or_ne a' a
    · obtain ⟨s, has, hs⟩ := h
      exact ⟨s, fun x hx hxa ↦ has (mem_singleton_iff.1 hxa ▸ hx), hs⟩
    · exact ⟨{a'}, singleton_subset_iff.2 ha', rfl⟩

@[simp]
theorem intent_deleteObjectOrderIso (h : ∃ s, a ∉ s ∧ upperPolar r s = upperPolar r {a})
    (c : Concept ({a}ᶜ : Set α) β (restrictObjects r {a}ᶜ)) :
    (deleteObjectOrderIso h c).intent = c.intent :=
  rfl

/-! ### Well-founded contexts -/

/-- A context is *attribute well-founded* if there is no infinite strictly ascending chain of
attribute extents. This holds if the set of objects or the set of attributes is finite. -/
def AttributeWellFounded (r : α → β → Prop) : Prop :=
  WellFounded fun b' b : β ↦ lowerPolar r {b} ⊂ lowerPolar r {b'}

/-- A context is *object well-founded* if there is no infinite strictly ascending chain of
object intents. This holds if the set of objects or the set of attributes is finite. -/
def ObjectWellFounded (r : α → β → Prop) : Prop :=
  WellFounded fun a' a : α ↦ upperPolar r {a} ⊂ upperPolar r {a'}

@[simp]
theorem objectWellFounded_swap : ObjectWellFounded (swap r) ↔ AttributeWellFounded r :=
  Iff.rfl

@[simp]
theorem attributeWellFounded_swap : AttributeWellFounded (swap r) ↔ ObjectWellFounded r :=
  Iff.rfl

theorem AttributeWellFounded.of_finite_objects [Finite α] (r : α → β → Prop) :
    AttributeWellFounded r :=
  InvImage.wf (fun b ↦ lowerPolar r {b}) (wellFounded_gt (α := Set α))

theorem AttributeWellFounded.of_finite_attributes [Finite β] (r : α → β → Prop) :
    AttributeWellFounded r :=
  haveI : IsTrans β fun b' b : β ↦ lowerPolar r {b} ⊂ lowerPolar r {b'} :=
    ⟨fun _ _ _ h₁ h₂ ↦ h₂.trans h₁⟩
  haveI : Std.Irrefl fun b' b : β ↦ lowerPolar r {b} ⊂ lowerPolar r {b'} :=
    ⟨fun _ ↦ ssubset_irrefl _⟩
  Finite.wellFounded_of_trans_of_irrefl _

theorem ObjectWellFounded.of_finite_objects [Finite α] (r : α → β → Prop) :
    ObjectWellFounded r :=
  AttributeWellFounded.of_finite_attributes (swap r)

theorem ObjectWellFounded.of_finite_attributes [Finite β] (r : α → β → Prop) :
    ObjectWellFounded r :=
  AttributeWellFounded.of_finite_objects (swap r)

/-- In an attribute well-founded context the irreducible attributes are infimum-dense: every
attribute extent is the extent of a set of irreducible attributes. -/
theorem AttributeWellFounded.exists_irreducible (h : AttributeWellFounded r) (b : β) :
    ∃ u ⊆ {b' | AttributeIrreducible r b'}, lowerPolar r u = lowerPolar r {b} := by
  induction b using h.induction with | _ b ih
  by_cases hb : AttributeReducible r b
  · choose! u hu hul using ih
    refine ⟨⋃ b' ∈ {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}}, u b',
      iUnion₂_subset fun b' hb' ↦ hu b' hb', ?_⟩
    rw [lowerPolar_iUnion₂]
    refine Eq.trans ?_ hb.symm
    rw [lowerPolar_eq_biInter r {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}}]
    exact iInter₂_congr fun b' hb' ↦ hul b' hb'
  · exact ⟨{b}, singleton_subset_iff.2 hb, rfl⟩

/-- In an object well-founded context the irreducible objects are supremum-dense: every object
intent is the intent of a set of irreducible objects. -/
theorem ObjectWellFounded.exists_irreducible (h : ObjectWellFounded r) (a : α) :
    ∃ u ⊆ {a' | ObjectIrreducible r a'}, upperPolar r u = upperPolar r {a} :=
  AttributeWellFounded.exists_irreducible (r := swap r) h a

/-- In an attribute well-founded context (for instance a finite one), deleting all reducible
attributes does not change the concept lattice. -/
def reduceAttributesOrderIso (h : AttributeWellFounded r) :
    Concept α {b | AttributeIrreducible r b} (restrictAttributes r {b | AttributeIrreducible r b})
      ≃o Concept α β r :=
  restrictAttributesOrderIso h.exists_irreducible

/-- In an object well-founded context (for instance a finite one), deleting all reducible
objects does not change the concept lattice. -/
def reduceObjectsOrderIso (h : ObjectWellFounded r) :
    Concept {a | ObjectIrreducible r a} β (restrictObjects r {a | ObjectIrreducible r a})
      ≃o Concept α β r :=
  restrictObjectsOrderIso h.exists_irreducible

@[simp]
theorem extent_reduceAttributesOrderIso (h : AttributeWellFounded r)
    (c : Concept α {b | AttributeIrreducible r b}
      (restrictAttributes r {b | AttributeIrreducible r b})) :
    (reduceAttributesOrderIso h c).extent = c.extent :=
  rfl

@[simp]
theorem intent_reduceObjectsOrderIso (h : ObjectWellFounded r)
    (c : Concept {a | ObjectIrreducible r a} β (restrictObjects r {a | ObjectIrreducible r a})) :
    (reduceObjectsOrderIso h c).intent = c.intent :=
  rfl

/-! ### Reduced contexts -/

/-- A context is *attribute reduced* (column reduced) if it is attribute clarified and every
attribute is irreducible. -/
def AttributeReduced (r : α → β → Prop) : Prop :=
  AttributeClarified r ∧ ∀ b, AttributeIrreducible r b

/-- A context is *object reduced* (row reduced) if it is object clarified and every object is
irreducible. -/
def ObjectReduced (r : α → β → Prop) : Prop :=
  ObjectClarified r ∧ ∀ a, ObjectIrreducible r a

/-- A context is *reduced* if it is both object reduced and attribute reduced. -/
def Reduced (r : α → β → Prop) : Prop :=
  ObjectReduced r ∧ AttributeReduced r

@[simp]
theorem objectReduced_swap : ObjectReduced (swap r) ↔ AttributeReduced r :=
  Iff.rfl

@[simp]
theorem attributeReduced_swap : AttributeReduced (swap r) ↔ ObjectReduced r :=
  Iff.rfl

@[simp]
theorem reduced_swap : Reduced (swap r) ↔ Reduced r :=
  and_comm

theorem Reduced.clarified (h : Reduced r) : Clarified r :=
  ⟨h.1.1, h.2.1⟩

/-- A context is attribute reduced iff forming attribute concepts is injective and every
attribute concept is completely meet-irreducible. -/
theorem attributeReduced_iff :
    AttributeReduced r ↔ Injective (Concept.ofAttribute r) ∧ ∀ b, ∀ S : Set (Concept α β r),
      sInf S = Concept.ofAttribute r b → Concept.ofAttribute r b ∈ S :=
  and_congr attributeClarified_iff_injective_ofAttribute
    (forall_congr' fun _ ↦ attributeIrreducible_iff_forall_sInf)

/-- A context is object reduced iff forming object concepts is injective and every object concept
is completely join-irreducible. -/
theorem objectReduced_iff :
    ObjectReduced r ↔ Injective (Concept.ofObject r) ∧ ∀ a, ∀ S : Set (Concept α β r),
      sSup S = Concept.ofObject r a → Concept.ofObject r a ∈ S :=
  and_congr objectClarified_iff_injective_ofObject
    (forall_congr' fun _ ↦ objectIrreducible_iff_forall_sSup)

end FCA
