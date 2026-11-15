/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Constructions
public import Mathlib.Order.Setoid.Basic

/-!
# Clarified contexts

A formal context `r : α → β → Prop` is *clarified* if distinct objects have distinct object
intents and distinct attributes have distinct attribute extents. Every context can be clarified
by identifying objects with the same intent and attributes with the same extent; this does not
change the concept lattice.

## Main definitions

* `FCA.ObjectClarified`, `FCA.AttributeClarified`, `FCA.Clarified`: clarified contexts.
* `FCA.objectSetoid`, `FCA.attributeSetoid`: the equivalence relations "same object intent" and
  "same attribute extent".
* `FCA.clarifyObjects`, `FCA.clarifyAttributes`, `FCA.clarify`: the quotient contexts.
* `FCA.clarifyObjectsOrderIso`, `FCA.clarifyAttributesOrderIso`, `FCA.clarifyOrderIso`: the
  concept lattice of the clarified context is isomorphic to the original concept lattice.

## Main results

* `FCA.objectClarified_iff_injective_ofObject`, `FCA.attributeClarified_iff_injective_ofAttribute`:
  a context is object (attribute) clarified iff forming object (attribute) concepts is injective.
* `FCA.clarified_clarify`: the context `FCA.clarify r` is clarified.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {a a' : α} {b b' : β}

/-! ### Clarified contexts -/

/-- A context is *object clarified* if distinct objects have distinct object intents. -/
def ObjectClarified (r : α → β → Prop) : Prop :=
  Injective fun a ↦ upperPolar r {a}

/-- A context is *attribute clarified* if distinct attributes have distinct attribute extents. -/
def AttributeClarified (r : α → β → Prop) : Prop :=
  Injective fun b ↦ lowerPolar r {b}

/-- A context is *clarified* if it is both object clarified and attribute clarified. -/
def Clarified (r : α → β → Prop) : Prop :=
  ObjectClarified r ∧ AttributeClarified r

theorem objectClarified_iff :
    ObjectClarified r ↔ ∀ a a', (∀ b, r a b ↔ r a' b) → a = a' := by
  simp [ObjectClarified, Injective, Set.ext_iff]

theorem attributeClarified_iff :
    AttributeClarified r ↔ ∀ b b', (∀ a, r a b ↔ r a b') → b = b' := by
  simp [AttributeClarified, Injective, Set.ext_iff]

@[simp]
theorem objectClarified_swap : ObjectClarified (swap r) ↔ AttributeClarified r :=
  Iff.rfl

@[simp]
theorem attributeClarified_swap : AttributeClarified (swap r) ↔ ObjectClarified r :=
  Iff.rfl

@[simp]
theorem clarified_swap : Clarified (swap r) ↔ Clarified r :=
  and_comm

@[simp]
theorem objectClarified_complement : ObjectClarified (complement r) ↔ ObjectClarified r := by
  simp [ObjectClarified, Injective]

@[simp]
theorem attributeClarified_complement :
    AttributeClarified (complement r) ↔ AttributeClarified r := by
  simp [AttributeClarified, Injective]

@[simp]
theorem clarified_complement : Clarified (complement r) ↔ Clarified r := by
  simp [Clarified]

/-- A context is object clarified iff distinct objects have distinct object concepts. -/
theorem objectClarified_iff_injective_ofObject :
    ObjectClarified r ↔ Injective (Concept.ofObject r) :=
  ⟨fun h _ _ haa' ↦ h (congrArg Concept.intent haa'), fun h _ _ haa' ↦ h (Concept.ext' haa')⟩

/-- A context is attribute clarified iff distinct attributes have distinct attribute concepts. -/
theorem attributeClarified_iff_injective_ofAttribute :
    AttributeClarified r ↔ Injective (Concept.ofAttribute r) :=
  ⟨fun h _ _ hbb' ↦ h (congrArg Concept.extent hbb'), fun h _ _ hbb' ↦ h (Concept.ext hbb')⟩

/-! ### The equivalence relations of clarification -/

/-- Two objects are equivalent if they have the same object intent. -/
def objectSetoid (r : α → β → Prop) : Setoid α :=
  Setoid.ker fun a ↦ upperPolar r {a}

/-- Two attributes are equivalent if they have the same attribute extent. -/
def attributeSetoid (r : α → β → Prop) : Setoid β :=
  Setoid.ker fun b ↦ lowerPolar r {b}

theorem objectSetoid_def : objectSetoid r a a' ↔ upperPolar r {a} = upperPolar r {a'} :=
  Iff.rfl

theorem attributeSetoid_def : attributeSetoid r b b' ↔ lowerPolar r {b} = lowerPolar r {b'} :=
  Iff.rfl

theorem objectSetoid_iff : objectSetoid r a a' ↔ ∀ b, r a b ↔ r a' b := by
  simp [objectSetoid_def, Set.ext_iff]

theorem attributeSetoid_iff : attributeSetoid r b b' ↔ ∀ a, r a b ↔ r a b' := by
  simp [attributeSetoid_def, Set.ext_iff]

theorem objectSetoid_iff_ofObject_eq :
    objectSetoid r a a' ↔ Concept.ofObject r a = Concept.ofObject r a' :=
  ⟨fun h ↦ Concept.ext' h, fun h ↦ congrArg Concept.intent h⟩

theorem attributeSetoid_iff_ofAttribute_eq :
    attributeSetoid r b b' ↔ Concept.ofAttribute r b = Concept.ofAttribute r b' :=
  ⟨fun h ↦ Concept.ext h, fun h ↦ congrArg Concept.extent h⟩

theorem objectSetoid_swap (r : α → β → Prop) : objectSetoid (swap r) = attributeSetoid r :=
  rfl

theorem attributeSetoid_swap (r : α → β → Prop) : attributeSetoid (swap r) = objectSetoid r :=
  rfl

/-- A context is object clarified iff "same object intent" is the equality relation. -/
theorem objectSetoid_eq_bot_iff : objectSetoid r = ⊥ ↔ ObjectClarified r :=
  Setoid.ker_eq_bot_iff

/-- A context is attribute clarified iff "same attribute extent" is the equality relation. -/
theorem attributeSetoid_eq_bot_iff : attributeSetoid r = ⊥ ↔ AttributeClarified r :=
  Setoid.ker_eq_bot_iff

/-- Extents cannot separate objects with the same object intent. -/
theorem _root_.Order.IsExtent.mem_iff_of_objectSetoid {s : Set α} (hs : IsExtent r s)
    (h : objectSetoid r a a') : a ∈ s ↔ a' ∈ s := by
  obtain ⟨t, rfl⟩ := hs
  simp only [mem_lowerPolar_iff, objectSetoid_iff.1 h]

/-- Intents cannot separate attributes with the same attribute extent. -/
theorem _root_.Order.IsIntent.mem_iff_of_attributeSetoid {t : Set β} (ht : IsIntent r t)
    (h : attributeSetoid r b b') : b ∈ t ↔ b' ∈ t :=
  IsExtent.mem_iff_of_objectSetoid (r := swap r) ht h

/-! ### Clarification -/

/-- The context obtained from `r` by identifying objects with the same object intent. -/
def clarifyObjects (r : α → β → Prop) : Quotient (objectSetoid r) → β → Prop :=
  Quotient.lift r fun _ _ h ↦ funext fun b ↦ propext (objectSetoid_iff.1 h b)

/-- The context obtained from `r` by identifying attributes with the same attribute extent. -/
def clarifyAttributes (r : α → β → Prop) : α → Quotient (attributeSetoid r) → Prop :=
  fun a ↦ Quotient.lift (r a) fun _ _ h ↦ propext (attributeSetoid_iff.1 h a)

/-- The *clarification* of the context `r`, obtained by identifying objects with the same object
intent and attributes with the same attribute extent. -/
def clarify (r : α → β → Prop) : Quotient (objectSetoid r) → Quotient (attributeSetoid r) → Prop :=
  Quotient.lift₂ r fun _ _ _ _ h₁ h₂ ↦
    propext ((objectSetoid_iff.1 h₁ _).trans (attributeSetoid_iff.1 h₂ _))

@[simp]
theorem clarifyObjects_mk : clarifyObjects r ⟦a⟧ b ↔ r a b :=
  Iff.rfl

@[simp]
theorem clarifyAttributes_mk : clarifyAttributes r a ⟦b⟧ ↔ r a b :=
  Iff.rfl

@[simp]
theorem clarify_mk :
    clarify r (⟦a⟧ : Quotient (objectSetoid r)) (⟦b⟧ : Quotient (attributeSetoid r)) ↔ r a b :=
  Iff.rfl

theorem swap_clarifyObjects (r : α → β → Prop) :
    swap (clarifyObjects r) = clarifyAttributes (swap r) := by
  ext b ⟨a⟩
  rfl

theorem swap_clarifyAttributes (r : α → β → Prop) :
    swap (clarifyAttributes r) = clarifyObjects (swap r) := by
  ext ⟨b⟩ a
  rfl

theorem swap_clarify (r : α → β → Prop) : swap (clarify r) = clarify (swap r) := by
  ext ⟨b⟩ ⟨a⟩
  rfl

/-- Identifying objects with the same object intent yields an object clarified context. -/
theorem objectClarified_clarifyObjects (r : α → β → Prop) : ObjectClarified (clarifyObjects r) := by
  intro x y
  induction x using Quotient.inductionOn with | h a
  induction y using Quotient.inductionOn with | h a'
  intro (h : upperPolar (clarifyObjects r) {⟦a⟧} = upperPolar (clarifyObjects r) {⟦a'⟧})
  refine Quotient.sound (objectSetoid_iff.2 fun b ↦ ?_)
  simpa using Set.ext_iff.1 h b

/-- Identifying attributes with the same attribute extent yields an attribute clarified
context. -/
theorem attributeClarified_clarifyAttributes (r : α → β → Prop) :
    AttributeClarified (clarifyAttributes r) := by
  intro x y
  induction x using Quotient.inductionOn with | h b
  induction y using Quotient.inductionOn with | h b'
  intro (h : lowerPolar (clarifyAttributes r) {⟦b⟧} = lowerPolar (clarifyAttributes r) {⟦b'⟧})
  refine Quotient.sound (attributeSetoid_iff.2 fun a ↦ ?_)
  simpa using Set.ext_iff.1 h a

/-- The clarification of a context is clarified. -/
theorem clarified_clarify (r : α → β → Prop) : Clarified (clarify r) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | h a
    induction y using Quotient.inductionOn with | h a'
    intro (h : upperPolar (clarify r) {⟦a⟧} = upperPolar (clarify r) {⟦a'⟧})
    refine Quotient.sound (objectSetoid_iff.2 fun b ↦ ?_)
    simpa using Set.ext_iff.1 h ⟦b⟧
  · intro x y
    induction x using Quotient.inductionOn with | h b
    induction y using Quotient.inductionOn with | h b'
    intro (h : lowerPolar (clarify r) {⟦b⟧} = lowerPolar (clarify r) {⟦b'⟧})
    refine Quotient.sound (attributeSetoid_iff.2 fun a ↦ ?_)
    simpa using Set.ext_iff.1 h ⟦a⟧

/-- Identifying objects with the same object intent does not change the concept lattice. -/
def clarifyObjectsOrderIso (r : α → β → Prop) :
    Concept (Quotient (objectSetoid r)) β (clarifyObjects r) ≃o Concept α β r :=
  Concept.comapOrderIso (f := Quotient.mk _) (g := id) Quotient.mk_surjective surjective_id
    fun _ _ ↦ Iff.rfl

/-- Identifying attributes with the same attribute extent does not change the concept lattice. -/
def clarifyAttributesOrderIso (r : α → β → Prop) :
    Concept α (Quotient (attributeSetoid r)) (clarifyAttributes r) ≃o Concept α β r :=
  Concept.comapOrderIso (f := id) (g := Quotient.mk _) surjective_id Quotient.mk_surjective
    fun _ _ ↦ Iff.rfl

/-- The concept lattice of the clarification of a context is isomorphic to the concept lattice of
the context. -/
def clarifyOrderIso (r : α → β → Prop) :
    Concept (Quotient (objectSetoid r)) (Quotient (attributeSetoid r)) (clarify r) ≃o
      Concept α β r :=
  Concept.comapOrderIso (f := Quotient.mk _) (g := Quotient.mk _) Quotient.mk_surjective
    Quotient.mk_surjective fun _ _ ↦ Iff.rfl

@[simp]
theorem extent_clarifyObjectsOrderIso
    (c : Concept (Quotient (objectSetoid r)) β (clarifyObjects r)) :
    (clarifyObjectsOrderIso r c).extent = Quotient.mk _ ⁻¹' c.extent :=
  rfl

@[simp]
theorem intent_clarifyObjectsOrderIso
    (c : Concept (Quotient (objectSetoid r)) β (clarifyObjects r)) :
    (clarifyObjectsOrderIso r c).intent = c.intent :=
  rfl

@[simp]
theorem extent_clarifyAttributesOrderIso
    (c : Concept α (Quotient (attributeSetoid r)) (clarifyAttributes r)) :
    (clarifyAttributesOrderIso r c).extent = c.extent :=
  rfl

@[simp]
theorem intent_clarifyAttributesOrderIso
    (c : Concept α (Quotient (attributeSetoid r)) (clarifyAttributes r)) :
    (clarifyAttributesOrderIso r c).intent = Quotient.mk _ ⁻¹' c.intent :=
  rfl

@[simp]
theorem extent_clarifyOrderIso
    (c : Concept (Quotient (objectSetoid r)) (Quotient (attributeSetoid r)) (clarify r)) :
    (clarifyOrderIso r c).extent = Quotient.mk _ ⁻¹' c.extent :=
  rfl

@[simp]
theorem intent_clarifyOrderIso
    (c : Concept (Quotient (objectSetoid r)) (Quotient (attributeSetoid r)) (clarify r)) :
    (clarifyOrderIso r c).intent = Quotient.mk _ ⁻¹' c.intent :=
  rfl

/-- The clarification isomorphism maps object concepts to object concepts. -/
@[simp]
theorem clarifyOrderIso_ofObject (r : α → β → Prop) (a : α) :
    clarifyOrderIso r (Concept.ofObject (clarify r) ⟦a⟧) = Concept.ofObject r a := by
  refine Concept.ext' (Set.ext fun b ↦ ?_)
  simp

/-- The clarification isomorphism maps attribute concepts to attribute concepts. -/
@[simp]
theorem clarifyOrderIso_ofAttribute (r : α → β → Prop) (b : β) :
    clarifyOrderIso r (Concept.ofAttribute (clarify r) ⟦b⟧) = Concept.ofAttribute r b := by
  refine Concept.ext (Set.ext fun a ↦ ?_)
  simp

end FCA
