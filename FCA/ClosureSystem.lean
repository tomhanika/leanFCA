/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import Mathlib.Order.Concept

/-!
# Closure systems and formal contexts

The extents and the intents of a formal context `r : α → β → Prop` each form a closure system,
i.e. a family of sets closed under arbitrary intersections, and the concept lattice is isomorphic
to the closure system of extents and dually isomorphic to the closure system of intents.
Conversely, every closure operator on a powerset arises in this way: a closure operator `c` on
`Set β` is the intent closure of the context whose objects are the `c`-closed sets, whose
attributes are the elements of `β`, and whose incidence is (reversed) membership.

## Main definitions

* `Concept.extentOrderIso`, `Concept.intentOrderIso`: the concept lattice is isomorphic to the
  extents and dually isomorphic to the intents, ordered by inclusion.
* `Concept.extentClosedsOrderIso`, `Concept.intentClosedsOrderIso`: the same statements phrased
  with the closed sets of `extentClosure r` and `intentClosure r`.
* `FCA.closedsObjContext`: the context of a closure operator `c` on a set of attributes, with the
  closed sets as objects.
* `FCA.closedsAttrContext`: the context of a closure operator `c` on a set of objects, with the
  closed sets as attributes.
* `FCA.closedsOrderIsoConceptDual`, `FCA.closedsOrderIsoConcept`: the closed sets of `c` are
  dually isomorphic to the concept lattice of `closedsObjContext c` and isomorphic to the concept
  lattice of `closedsAttrContext c`.

## Main results

* `Order.IsExtent.sInter`, `Order.IsIntent.sInter`: extents and intents form closure systems.
* `extentClosure_isClosed_iff`, `intentClosure_isClosed_iff`: the closed sets of the polar
  closure operators are the extents and the intents.
* `FCA.intentClosure_closedsObjContext`: every closure operator on `Set β` is the intent closure
  of a context.
* `FCA.extentClosure_closedsAttrContext`: every closure operator on `Set α` is the extent closure
  of a context.
* `FCA.isIntent_closedsObjContext_iff`, `FCA.isExtent_closedsAttrContext_iff`: the intents
  (extents) of these contexts are exactly the closed sets.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Order OrderDual

variable {α β : Type*} {r : α → β → Prop} {s : Set α} {t : Set β}

/-! ### Extents and intents as closure systems -/

namespace Order

/-- The extents of a context form a closure system: they are closed under arbitrary
intersections. -/
protected theorem IsExtent.sInter {S : Set (Set α)} (hS : ∀ s ∈ S, IsExtent r s) :
    IsExtent r (⋂₀ S) := by
  rw [sInter_eq_biInter]
  exact .iInter₂ _ hS

/-- The intents of a context form a closure system: they are closed under arbitrary
intersections. -/
protected theorem IsIntent.sInter {S : Set (Set β)} (hS : ∀ t ∈ S, IsIntent r t) :
    IsIntent r (⋂₀ S) :=
  IsExtent.sInter hS

end Order

/-- The closed sets of the extent closure are exactly the extents. -/
theorem extentClosure_isClosed_iff : (extentClosure r).IsClosed s ↔ IsExtent r s :=
  (extentClosure r).isClosed_iff.trans isExtent_iff.symm

/-- The closed sets of the intent closure are exactly the intents. -/
theorem intentClosure_isClosed_iff : (intentClosure r).IsClosed t ↔ IsIntent r t :=
  (intentClosure r).isClosed_iff.trans isIntent_iff.symm

/-- The extent closure is the closure operator of the closure system of extents. -/
theorem extentClosure_eq_ofCompletePred (r : α → β → Prop) :
    extentClosure r = .ofCompletePred (IsExtent r) fun _ => IsExtent.sInter :=
  ClosureOperator.ext_isClosed _ _ fun _ => extentClosure_isClosed_iff

/-- The intent closure is the closure operator of the closure system of intents. -/
theorem intentClosure_eq_ofCompletePred (r : α → β → Prop) :
    intentClosure r = .ofCompletePred (IsIntent r) fun _ => IsIntent.sInter :=
  ClosureOperator.ext_isClosed _ _ fun _ => intentClosure_isClosed_iff

namespace Concept

/-! ### The concept lattice as a lattice of closed sets -/

/-- The concept lattice is isomorphic to the extents ordered by inclusion. -/
@[simps]
def extentOrderIso (r : α → β → Prop) : Concept α β r ≃o {s // IsExtent r s} where
  toFun c := ⟨c.extent, c.isExtent_extent⟩
  invFun s := ofIsExtent r s.1 s.2
  left_inv _ := ext rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The concept lattice is dually isomorphic to the intents ordered by inclusion. -/
@[simps]
def intentOrderIso (r : α → β → Prop) : (Concept α β r)ᵒᵈ ≃o {t // IsIntent r t} where
  toFun c := ⟨(ofDual c).intent, (ofDual c).isIntent_intent⟩
  invFun t := toDual (ofIsIntent r t.1 t.2)
  left_inv _ := ext' rfl
  right_inv _ := rfl
  map_rel_iff' := intent_subset_intent_iff

/-- The concept lattice is isomorphic to the lattice of closed sets of the extent closure. -/
@[simps]
def extentClosedsOrderIso (r : α → β → Prop) : Concept α β r ≃o (extentClosure r).Closeds where
  toFun c := ⟨c.extent, extentClosure_isClosed_iff.2 c.isExtent_extent⟩
  invFun s := ofIsExtent r s.1 (extentClosure_isClosed_iff.1 s.2)
  left_inv _ := ext rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The concept lattice is dually isomorphic to the lattice of closed sets of the intent
closure. -/
@[simps]
def intentClosedsOrderIso (r : α → β → Prop) :
    (Concept α β r)ᵒᵈ ≃o (intentClosure r).Closeds where
  toFun c := ⟨(ofDual c).intent, intentClosure_isClosed_iff.2 (ofDual c).isIntent_intent⟩
  invFun t := toDual (ofIsIntent r t.1 (intentClosure_isClosed_iff.1 t.2))
  left_inv _ := ext' rfl
  right_inv _ := rfl
  map_rel_iff' := intent_subset_intent_iff

end Concept

namespace FCA

/-! ### The context of a closure operator on attributes -/

section ObjContext

variable (c : ClosureOperator (Set β))

/-- The context of a closure operator `c` on a set `β` of attributes: the objects are the
`c`-closed sets, and a closed set `t` has the attribute `b` iff `b ∈ t`. -/
def closedsObjContext : c.Closeds → β → Prop :=
  fun t b => b ∈ t.1

variable {c}

@[simp]
theorem closedsObjContext_apply {t : c.Closeds} {b : β} : closedsObjContext c t b ↔ b ∈ t.1 :=
  Iff.rfl

variable (c)

/-- The intent closure of a set in `closedsObjContext c` is its `c`-closure. -/
@[simp]
theorem upperPolar_lowerPolar_closedsObjContext (t : Set β) :
    upperPolar (closedsObjContext c) (lowerPolar (closedsObjContext c) t) = c t := by
  ext b
  refine ⟨fun h => h (a := c.toCloseds t) fun _ hb => c.le_closure t hb, fun hb u hu => ?_⟩
  exact c.closure_min (fun _ hx => hu hx) u.2 hb

/-- Every closure operator on a powerset is the intent closure of a context. -/
@[simp]
theorem intentClosure_closedsObjContext : intentClosure (closedsObjContext c) = c :=
  ClosureOperator.ext _ _ (upperPolar_lowerPolar_closedsObjContext c)

variable {c}

/-- The intents of `closedsObjContext c` are exactly the `c`-closed sets. -/
theorem isIntent_closedsObjContext_iff : IsIntent (closedsObjContext c) t ↔ c.IsClosed t := by
  rw [← intentClosure_isClosed_iff, intentClosure_closedsObjContext]

variable (c)

/-- Every closure system on `β` is the system of intents of a context: the closed sets of a
closure operator `c`, ordered by inclusion, are dually isomorphic to the concept lattice of
`closedsObjContext c`. A closed set is sent to the concept having it as intent. -/
def closedsOrderIsoConceptDual : c.Closeds ≃o (Concept c.Closeds β (closedsObjContext c))ᵒᵈ where
  toFun t := toDual (.ofIsIntent _ t.1 (isIntent_closedsObjContext_iff.2 t.2))
  invFun d := ⟨(ofDual d).intent, isIntent_closedsObjContext_iff.1 (ofDual d).isIntent_intent⟩
  left_inv _ := rfl
  right_inv _ := Concept.ext' rfl
  map_rel_iff' := Concept.intent_subset_intent_iff.symm

variable {c}

@[simp]
theorem intent_closedsOrderIsoConceptDual (t : c.Closeds) :
    (ofDual (closedsOrderIsoConceptDual c t)).intent = t :=
  rfl

@[simp]
theorem closedsOrderIsoConceptDual_symm_apply
    (d : (Concept c.Closeds β (closedsObjContext c))ᵒᵈ) :
    ((closedsOrderIsoConceptDual c).symm d : Set β) = (ofDual d).intent :=
  rfl

end ObjContext

/-! ### The context of a closure operator on objects -/

section AttrContext

variable (c : ClosureOperator (Set α))

/-- The context of a closure operator `c` on a set `α` of objects: the attributes are the
`c`-closed sets, and an object `a` has the attribute `s` iff `a ∈ s`. -/
def closedsAttrContext : α → c.Closeds → Prop :=
  fun a s => a ∈ s.1

variable {c}

@[simp]
theorem closedsAttrContext_apply {a : α} {s : c.Closeds} : closedsAttrContext c a s ↔ a ∈ s.1 :=
  Iff.rfl

variable (c)

theorem swap_closedsObjContext : Function.swap (closedsObjContext c) = closedsAttrContext c :=
  rfl

/-- The extent closure of a set in `closedsAttrContext c` is its `c`-closure. -/
@[simp]
theorem lowerPolar_upperPolar_closedsAttrContext (s : Set α) :
    lowerPolar (closedsAttrContext c) (upperPolar (closedsAttrContext c) s) = c s :=
  upperPolar_lowerPolar_closedsObjContext c s

/-- Every closure operator on a powerset is the extent closure of a context. -/
@[simp]
theorem extentClosure_closedsAttrContext : extentClosure (closedsAttrContext c) = c :=
  ClosureOperator.ext _ _ (lowerPolar_upperPolar_closedsAttrContext c)

variable {c}

/-- The extents of `closedsAttrContext c` are exactly the `c`-closed sets. -/
theorem isExtent_closedsAttrContext_iff : IsExtent (closedsAttrContext c) s ↔ c.IsClosed s := by
  rw [← extentClosure_isClosed_iff, extentClosure_closedsAttrContext]

variable (c)

/-- Every closure system on `α` is the system of extents of a context: the closed sets of a
closure operator `c`, ordered by inclusion, are isomorphic to the concept lattice of
`closedsAttrContext c`. A closed set is sent to the concept having it as extent. -/
def closedsOrderIsoConcept : c.Closeds ≃o Concept α c.Closeds (closedsAttrContext c) where
  toFun s := .ofIsExtent _ s.1 (isExtent_closedsAttrContext_iff.2 s.2)
  invFun d := ⟨d.extent, isExtent_closedsAttrContext_iff.1 d.isExtent_extent⟩
  left_inv _ := rfl
  right_inv _ := Concept.ext rfl
  map_rel_iff' := Iff.rfl

variable {c}

@[simp]
theorem extent_closedsOrderIsoConcept (s : c.Closeds) :
    (closedsOrderIsoConcept c s).extent = s :=
  rfl

@[simp]
theorem closedsOrderIsoConcept_symm_apply (d : Concept α c.Closeds (closedsAttrContext c)) :
    ((closedsOrderIsoConcept c).symm d : Set α) = d.extent :=
  rfl

end AttrContext

end FCA
