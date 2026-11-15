/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Reduced

/-!
# Arrow relations of a formal context

For a formal context `r : α → β → Prop`, an object `a` and an attribute `b`, Ganter and Wille
define

* `a ↙ b` iff `a` does not have `b`, but every object whose intent properly contains the intent
  of `a` has `b`;
* `a ↗ b` iff `a` does not have `b`, but `a` has every attribute whose extent properly contains
  the extent of `b`;
* `a ⤢ b` iff `a ↙ b` and `a ↗ b`.

The arrow relations detect the irreducible objects and attributes.

## Main definitions

* `FCA.DownArrow`, `FCA.UpArrow`, `FCA.DoubleArrow`: the arrow relations, with scoped notations
  `a ↙[r] b`, `a ↗[r] b` and `a ⤢[r] b`.

## Main results

* `FCA.downArrow_iff_maximalFor`: `a ↙ b` iff the intent of `a` is maximal among the object
  intents not containing `b`.
* `FCA.downArrow_iff_ofObject`, `FCA.upArrow_iff_ofAttribute`: the arrow relations in terms of
  object and attribute concepts.
* `FCA.attributeIrreducible_iff_exists_upArrow`: an attribute `b` is irreducible iff `a ↗ b` for
  some object `a`.
* `FCA.objectIrreducible_iff_exists_downArrow`: an object `a` is irreducible iff `a ↙ b` for some
  attribute `b`.
* `FCA.ObjectWellFounded.exists_downArrow`, `FCA.AttributeWellFounded.exists_upArrow`: in a
  well-founded (for instance finite) context, every non-incident pair can be enlarged to an
  arrow.
* `FCA.objectIrreducible_iff_exists_doubleArrow`,
  `FCA.attributeIrreducible_iff_exists_doubleArrow`: in a well-founded (for instance finite)
  context, an object or attribute is irreducible iff it is part of a double arrow.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {a : α} {b : β}

/-! ### Definitions -/

/-- The *down arrow* relation `a ↙ b`: the object `a` does not have the attribute `b`, but every
object whose intent properly contains the intent of `a` has `b`. -/
def DownArrow (r : α → β → Prop) (a : α) (b : β) : Prop :=
  ¬ r a b ∧ ∀ a', upperPolar r {a} ⊂ upperPolar r {a'} → r a' b

/-- The *up arrow* relation `a ↗ b`: the object `a` does not have the attribute `b`, but it has
every attribute whose extent properly contains the extent of `b`. -/
def UpArrow (r : α → β → Prop) (a : α) (b : β) : Prop :=
  ¬ r a b ∧ ∀ b', lowerPolar r {b} ⊂ lowerPolar r {b'} → r a b'

/-- The *double arrow* relation `a ⤢ b`: both `a ↙ b` and `a ↗ b`. -/
def DoubleArrow (r : α → β → Prop) (a : α) (b : β) : Prop :=
  DownArrow r a b ∧ UpArrow r a b

@[inherit_doc] scoped notation:50 a " ↙[" r "] " b:51 => DownArrow r a b
@[inherit_doc] scoped notation:50 a " ↗[" r "] " b:51 => UpArrow r a b
@[inherit_doc] scoped notation:50 a " ⤢[" r "] " b:51 => DoubleArrow r a b

theorem DownArrow.not_rel (h : a ↙[r] b) : ¬ r a b :=
  h.1

theorem UpArrow.not_rel (h : a ↗[r] b) : ¬ r a b :=
  h.1

theorem DoubleArrow.downArrow (h : a ⤢[r] b) : a ↙[r] b :=
  h.1

theorem DoubleArrow.upArrow (h : a ⤢[r] b) : a ↗[r] b :=
  h.2

theorem DoubleArrow.not_rel (h : a ⤢[r] b) : ¬ r a b :=
  h.1.1

/-! ### Duality -/

@[simp]
theorem upArrow_swap : b ↗[swap r] a ↔ a ↙[r] b :=
  Iff.rfl

@[simp]
theorem downArrow_swap : b ↙[swap r] a ↔ a ↗[r] b :=
  Iff.rfl

@[simp]
theorem doubleArrow_swap : b ⤢[swap r] a ↔ a ⤢[r] b :=
  and_comm

/-! ### Characterisations -/

/-- `a ↗ b` iff `a` lies in the intersection of the attribute extents properly containing the
extent of `b`, but not in the extent of `b`. -/
theorem upArrow_iff_mem_diff :
    a ↗[r] b ↔
      a ∈ lowerPolar r {b' | lowerPolar r {b} ⊂ lowerPolar r {b'}} \ lowerPolar r {b} := by
  rw [mem_sdiff, mem_lowerPolar_singleton, and_comm]
  rfl

/-- `a ↙ b` iff `b` lies in the intersection of the object intents properly containing the
intent of `a`, but not in the intent of `a`. -/
theorem downArrow_iff_mem_diff :
    a ↙[r] b ↔
      b ∈ upperPolar r {a' | upperPolar r {a} ⊂ upperPolar r {a'}} \ upperPolar r {a} :=
  upArrow_iff_mem_diff (r := swap r)

/-- `a ↙ b` iff the intent of `a` is maximal among the object intents not containing `b`. -/
theorem downArrow_iff_maximalFor :
    a ↙[r] b ↔ MaximalFor (fun a ↦ ¬ r a b) (fun a ↦ upperPolar r {a}) a := by
  refine and_congr_right fun _ ↦ forall_congr' fun a' ↦ ?_
  rw [ssubset_def]
  exact ⟨fun h ha' hle ↦ by_contra fun hge ↦ ha' (h ⟨hle, hge⟩),
    fun h hlt ↦ by_contra fun ha' ↦ hlt.2 (h ha' hlt.1)⟩

/-- `a ↗ b` iff the extent of `b` is maximal among the attribute extents not containing `a`. -/
theorem upArrow_iff_maximalFor :
    a ↗[r] b ↔ MaximalFor (fun b ↦ ¬ r a b) (fun b ↦ lowerPolar r {b}) b :=
  downArrow_iff_maximalFor (r := swap r)

/-- The down arrow relation in terms of object and attribute concepts: `a ↙ b` iff the object
concept of `a` is not below the attribute concept of `b`, but every object concept strictly below
the object concept of `a` is. -/
theorem downArrow_iff_ofObject :
    a ↙[r] b ↔ ¬ Concept.ofObject r a ≤ Concept.ofAttribute r b ∧
      ∀ a', Concept.ofObject r a' < Concept.ofObject r a →
        Concept.ofObject r a' ≤ Concept.ofAttribute r b :=
  and_congr (not_congr Concept.ofObject_le_ofAttribute_iff.symm) <| forall_congr' fun a' ↦
    imp_congr
      (Concept.intent_ssubset_intent_iff (c := Concept.ofObject r a) (d := Concept.ofObject r a'))
      Concept.ofObject_le_ofAttribute_iff.symm

/-- The up arrow relation in terms of object and attribute concepts: `a ↗ b` iff the object
concept of `a` is not below the attribute concept of `b`, but it is below every attribute concept
strictly above the attribute concept of `b`. -/
theorem upArrow_iff_ofAttribute :
    a ↗[r] b ↔ ¬ Concept.ofObject r a ≤ Concept.ofAttribute r b ∧
      ∀ b', Concept.ofAttribute r b < Concept.ofAttribute r b' →
        Concept.ofObject r a ≤ Concept.ofAttribute r b' :=
  and_congr (not_congr Concept.ofObject_le_ofAttribute_iff.symm) <| forall_congr' fun b' ↦
    imp_congr
      (Concept.extent_ssubset_extent_iff (c := Concept.ofAttribute r b)
        (d := Concept.ofAttribute r b'))
      Concept.ofObject_le_ofAttribute_iff.symm

/-- The arrow relations only depend on the object intent. -/
theorem downArrow_congr_left {a' : α} (h : upperPolar r {a} = upperPolar r {a'}) :
    a ↙[r] b ↔ a' ↙[r] b := by
  have hb : r a b ↔ r a' b := by simpa using Set.ext_iff.1 h b
  rw [DownArrow, DownArrow, h, hb]

/-- The arrow relations only depend on the attribute extent. -/
theorem upArrow_congr_right {b' : β} (h : lowerPolar r {b} = lowerPolar r {b'}) :
    a ↗[r] b ↔ a ↗[r] b' :=
  downArrow_congr_left (r := swap r) h

/-! ### Arrows and irreducibility -/

/-- An attribute `b` is irreducible iff `a ↗ b` for some object `a`. -/
theorem attributeIrreducible_iff_exists_upArrow : AttributeIrreducible r b ↔ ∃ a, a ↗[r] b :=
  attributeIrreducible_iff_exists

/-- An object `a` is irreducible iff `a ↙ b` for some attribute `b`. -/
theorem objectIrreducible_iff_exists_downArrow : ObjectIrreducible r a ↔ ∃ b, a ↙[r] b :=
  objectIrreducible_iff_exists

theorem UpArrow.attributeIrreducible (h : a ↗[r] b) : AttributeIrreducible r b :=
  attributeIrreducible_iff_exists_upArrow.2 ⟨a, h⟩

theorem DownArrow.objectIrreducible (h : a ↙[r] b) : ObjectIrreducible r a :=
  objectIrreducible_iff_exists_downArrow.2 ⟨b, h⟩

theorem DoubleArrow.attributeIrreducible (h : a ⤢[r] b) : AttributeIrreducible r b :=
  h.upArrow.attributeIrreducible

theorem DoubleArrow.objectIrreducible (h : a ⤢[r] b) : ObjectIrreducible r a :=
  h.downArrow.objectIrreducible

/-- A context is attribute reduced iff it is attribute clarified and every attribute is the
target of an up arrow. -/
theorem attributeReduced_iff_forall_exists_upArrow :
    AttributeReduced r ↔ AttributeClarified r ∧ ∀ b, ∃ a, a ↗[r] b :=
  and_congr_right fun _ ↦ forall_congr' fun _ ↦ attributeIrreducible_iff_exists_upArrow

/-- A context is object reduced iff it is object clarified and every object is the source of a
down arrow. -/
theorem objectReduced_iff_forall_exists_downArrow :
    ObjectReduced r ↔ ObjectClarified r ∧ ∀ a, ∃ b, a ↙[r] b :=
  and_congr_right fun _ ↦ forall_congr' fun _ ↦ objectIrreducible_iff_exists_downArrow

/-! ### Well-founded contexts -/

/-- In an object well-founded context (for instance a finite one), if `a` does not have `b` then
there is an object `a'` whose intent contains the intent of `a` such that `a' ↙ b`. -/
theorem ObjectWellFounded.exists_downArrow (h : ObjectWellFounded r) (hab : ¬ r a b) :
    ∃ a', upperPolar r {a} ⊆ upperPolar r {a'} ∧ a' ↙[r] b := by
  obtain ⟨m, ⟨hm, hmb⟩, hmin⟩ :=
    h.has_min {a' | upperPolar r {a} ⊆ upperPolar r {a'} ∧ ¬ r a' b} ⟨a, Subset.rfl, hab⟩
  exact ⟨m, hm, hmb, fun a' ha' ↦ by_contra fun ha'b ↦ hmin a' ⟨hm.trans ha'.subset, ha'b⟩ ha'⟩

/-- In an attribute well-founded context (for instance a finite one), if `a` does not have `b`
then there is an attribute `b'` whose extent contains the extent of `b` such that `a ↗ b'`. -/
theorem AttributeWellFounded.exists_upArrow (h : AttributeWellFounded r) (hab : ¬ r a b) :
    ∃ b', lowerPolar r {b} ⊆ lowerPolar r {b'} ∧ a ↗[r] b' :=
  ObjectWellFounded.exists_downArrow (r := swap r) h hab

/-- In an attribute well-founded context, every down arrow `a ↙ b` can be completed to a double
arrow `a ⤢ b'`, where the extent of `b'` contains the extent of `b`. -/
theorem DownArrow.exists_doubleArrow (hab : a ↙[r] b) (h : AttributeWellFounded r) :
    ∃ b', lowerPolar r {b} ⊆ lowerPolar r {b'} ∧ a ⤢[r] b' := by
  obtain ⟨b', hbb', hab'⟩ := h.exists_upArrow hab.not_rel
  exact ⟨b', hbb', ⟨hab'.not_rel, fun a' ha' ↦
    (mem_lowerPolar_singleton r).1 (hbb' ((mem_lowerPolar_singleton r).2 (hab.2 a' ha')))⟩, hab'⟩

/-- In an object well-founded context, every up arrow `a ↗ b` can be completed to a double
arrow `a' ⤢ b`, where the intent of `a'` contains the intent of `a`. -/
theorem UpArrow.exists_doubleArrow (hab : a ↗[r] b) (h : ObjectWellFounded r) :
    ∃ a', upperPolar r {a} ⊆ upperPolar r {a'} ∧ a' ⤢[r] b := by
  obtain ⟨a', haa', ha'b⟩ := DownArrow.exists_doubleArrow (r := swap r) hab h
  exact ⟨a', haa', doubleArrow_swap.1 ha'b⟩

/-- In an attribute well-founded context (for instance a finite one), an object `a` is
irreducible iff `a ⤢ b` for some attribute `b`. -/
theorem objectIrreducible_iff_exists_doubleArrow (h : AttributeWellFounded r) :
    ObjectIrreducible r a ↔ ∃ b, a ⤢[r] b := by
  refine ⟨fun ha ↦ ?_, fun ⟨b, hab⟩ ↦ hab.objectIrreducible⟩
  obtain ⟨b, hab⟩ := objectIrreducible_iff_exists_downArrow.1 ha
  obtain ⟨b', -, hab'⟩ := hab.exists_doubleArrow h
  exact ⟨b', hab'⟩

/-- In an object well-founded context (for instance a finite one), an attribute `b` is
irreducible iff `a ⤢ b` for some object `a`. -/
theorem attributeIrreducible_iff_exists_doubleArrow (h : ObjectWellFounded r) :
    AttributeIrreducible r b ↔ ∃ a, a ⤢[r] b := by
  refine ⟨fun hb ↦ ?_, fun ⟨a, hab⟩ ↦ hab.attributeIrreducible⟩
  obtain ⟨a, hab⟩ := attributeIrreducible_iff_exists_upArrow.1 hb
  obtain ⟨a', -, ha'b⟩ := hab.exists_doubleArrow h
  exact ⟨a', ha'b⟩

/-- In a context with finitely many objects, an attribute `b` is irreducible iff `a ⤢ b` for some
object `a`. -/
theorem attributeIrreducible_iff_exists_doubleArrow_of_finite [Finite α] :
    AttributeIrreducible r b ↔ ∃ a, a ⤢[r] b :=
  attributeIrreducible_iff_exists_doubleArrow (.of_finite_objects r)

/-- In a context with finitely many attributes, an object `a` is irreducible iff `a ⤢ b` for some
attribute `b`. -/
theorem objectIrreducible_iff_exists_doubleArrow_of_finite [Finite β] :
    ObjectIrreducible r a ↔ ∃ b, a ⤢[r] b :=
  objectIrreducible_iff_exists_doubleArrow (.of_finite_attributes r)

end FCA
