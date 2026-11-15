/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Morphism.Bond

/-!
# Context isomorphisms and infomorphisms

This file studies two kinds of maps between formal contexts `r₁ : α₁ → β₁ → Prop` and
`r₂ : α₂ → β₂ → Prop`.

A *context isomorphism* is a pair of bijections between the objects and between the attributes
which preserves and reflects the incidence. Isomorphic contexts have isomorphic concept lattices.

An *infomorphism* (also known as a *Chu morphism*) is a pair of maps `f : α₁ → α₂` on objects and
`g : β₂ → β₁` on attributes, in opposite directions, such that `r₁ a (g b) ↔ r₂ (f a) b`.
Preimages of extents under `f` are extents and preimages of intents under `g` are intents, which
yields an adjoint pair of maps between the concept lattices.

## Main definitions

* `FCA.ContextIso r₁ r₂`: isomorphisms of contexts, with `refl`, `symm`, `trans`.
* `FCA.ContextIso.conceptIso`: the order isomorphism of concept lattices induced by a context
  isomorphism.
* `FCA.Infomorphism r₁ r₂`: infomorphisms of contexts, with `id` and `comp`.
* `FCA.Infomorphism.map`: the supremum-preserving map `Concept α₁ β₁ r₁ → Concept α₂ β₂ r₂`
  induced by an infomorphism.
* `FCA.Infomorphism.comap`: the infimum-preserving map `Concept α₂ β₂ r₂ → Concept α₁ β₁ r₁`
  induced by an infomorphism.
* `FCA.Infomorphism.toBond`: the bond of an infomorphism.
* `FCA.ContextIso.toInfomorphism`: a context isomorphism as an infomorphism.

## Main results

* `FCA.Infomorphism.isExtent_preimage`, `FCA.Infomorphism.isIntent_preimage`: preimages of
  extents and of intents under an infomorphism are extents and intents.
* `FCA.Infomorphism.gc_map_comap`: the induced maps form a Galois connection.
* `FCA.Infomorphism.map_comp`, `FCA.Infomorphism.comap_comp`: the induced maps are functorial.
* `FCA.Infomorphism.toBond_comp`: passing to bonds turns composition into the bond product.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [J. Barwise, J. Seligman, *Information Flow: The Logic of Distributed Systems*][barwise1997]
-/

@[expose] public section

open Set Order Function

namespace FCA

variable {α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ : Type*} {r₁ : α₁ → β₁ → Prop} {r₂ : α₂ → β₂ → Prop}
  {r₃ : α₃ → β₃ → Prop} {r₄ : α₄ → β₄ → Prop}

/-! ### Context isomorphisms -/

/-- An isomorphism between the contexts `r₁` and `r₂`: a bijection between the objects and a
bijection between the attributes which preserve and reflect the incidence. -/
structure ContextIso (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) where
  /-- The bijection between the objects. -/
  objEquiv : α₁ ≃ α₂
  /-- The bijection between the attributes. -/
  attrEquiv : β₁ ≃ β₂
  /-- A context isomorphism preserves and reflects the incidence. -/
  rel_iff' : ∀ a b, r₂ (objEquiv a) (attrEquiv b) ↔ r₁ a b

namespace ContextIso

@[ext]
theorem ext {e₁ e₂ : ContextIso r₁ r₂} (hobj : e₁.objEquiv = e₂.objEquiv)
    (hattr : e₁.attrEquiv = e₂.attrEquiv) : e₁ = e₂ := by
  cases e₁
  cases e₂
  congr

theorem rel_iff (e : ContextIso r₁ r₂) {a : α₁} {b : β₁} :
    r₂ (e.objEquiv a) (e.attrEquiv b) ↔ r₁ a b :=
  e.rel_iff' a b

/-- The identity isomorphism of a context. -/
@[simps]
protected def refl (r : α₁ → β₁ → Prop) : ContextIso r r where
  objEquiv := .refl _
  attrEquiv := .refl _
  rel_iff' _ _ := Iff.rfl

instance : Inhabited (ContextIso r₁ r₁) :=
  ⟨.refl r₁⟩

/-- The inverse of a context isomorphism. -/
@[simps]
protected def symm (e : ContextIso r₁ r₂) : ContextIso r₂ r₁ where
  objEquiv := e.objEquiv.symm
  attrEquiv := e.attrEquiv.symm
  rel_iff' a b := by rw [← e.rel_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The composition of context isomorphisms. -/
@[simps]
protected def trans (e₁ : ContextIso r₁ r₂) (e₂ : ContextIso r₂ r₃) : ContextIso r₁ r₃ where
  objEquiv := e₁.objEquiv.trans e₂.objEquiv
  attrEquiv := e₁.attrEquiv.trans e₂.attrEquiv
  rel_iff' _ _ := e₂.rel_iff.trans e₁.rel_iff

/-- A context isomorphism is also an isomorphism between the dual contexts. -/
@[simps]
protected def swap (e : ContextIso r₁ r₂) : ContextIso (swap r₁) (swap r₂) where
  objEquiv := e.attrEquiv
  attrEquiv := e.objEquiv
  rel_iff' _ _ := e.rel_iff

@[simp]
theorem symm_symm (e : ContextIso r₁ r₂) : e.symm.symm = e :=
  rfl

@[simp]
theorem refl_trans (e : ContextIso r₁ r₂) : (ContextIso.refl r₁).trans e = e :=
  rfl

@[simp]
theorem trans_refl (e : ContextIso r₁ r₂) : e.trans (.refl r₂) = e :=
  rfl

theorem trans_assoc (e₁ : ContextIso r₁ r₂) (e₂ : ContextIso r₂ r₃) (e₃ : ContextIso r₃ r₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  rfl

@[simp]
theorem self_trans_symm (e : ContextIso r₁ r₂) : e.trans e.symm = .refl r₁ := by
  ext <;> simp

@[simp]
theorem symm_trans_self (e : ContextIso r₁ r₂) : e.symm.trans e = .refl r₂ := by
  ext <;> simp

variable (e : ContextIso r₁ r₂)

/-- A context isomorphism commutes with upper polars. -/
theorem upperPolar_image (s : Set α₁) :
    upperPolar r₂ (e.objEquiv '' s) = e.attrEquiv '' upperPolar r₁ s := by
  ext b
  refine ⟨fun h => ⟨e.attrEquiv.symm b, fun a ha => e.rel_iff.1 ?_, by simp⟩, ?_⟩
  · simpa using h (mem_image_of_mem _ ha)
  · rintro ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    exact e.rel_iff.2 (hb ha)

/-- A context isomorphism commutes with lower polars. -/
theorem lowerPolar_image (t : Set β₁) :
    lowerPolar r₂ (e.attrEquiv '' t) = e.objEquiv '' lowerPolar r₁ t :=
  e.swap.upperPolar_image t

/-- The image of an extent under a context isomorphism is an extent. -/
theorem isExtent_image_iff {s : Set α₁} : IsExtent r₂ (e.objEquiv '' s) ↔ IsExtent r₁ s := by
  rw [isExtent_iff, isExtent_iff, upperPolar_image, lowerPolar_image,
    e.objEquiv.injective.image_injective.eq_iff]

/-- The image of an intent under a context isomorphism is an intent. -/
theorem isIntent_image_iff {t : Set β₁} : IsIntent r₂ (e.attrEquiv '' t) ↔ IsIntent r₁ t :=
  e.swap.isExtent_image_iff

/-- The image of a concept under a context isomorphism. -/
@[simps]
def mapConcept (c : Concept α₁ β₁ r₁) : Concept α₂ β₂ r₂ where
  extent := e.objEquiv '' c.extent
  intent := e.attrEquiv '' c.intent
  upperPolar_extent := by rw [upperPolar_image, c.upperPolar_extent]
  lowerPolar_intent := by rw [lowerPolar_image, c.lowerPolar_intent]

/-- Isomorphic contexts have isomorphic concept lattices. -/
@[simps]
def conceptIso : Concept α₁ β₁ r₁ ≃o Concept α₂ β₂ r₂ where
  toFun := e.mapConcept
  invFun := e.symm.mapConcept
  left_inv c := Concept.ext (by simp)
  right_inv c := Concept.ext (by simp)
  map_rel_iff' := image_subset_image_iff e.objEquiv.injective

@[simp]
theorem conceptIso_refl : (ContextIso.refl r₁).conceptIso = .refl _ := by
  ext c : 2
  exact Concept.ext (image_id _)

@[simp]
theorem conceptIso_symm : e.symm.conceptIso = e.conceptIso.symm :=
  rfl

@[simp]
theorem conceptIso_trans (e₁ : ContextIso r₁ r₂) (e₂ : ContextIso r₂ r₃) :
    (e₁.trans e₂).conceptIso = e₁.conceptIso.trans e₂.conceptIso := by
  ext c : 2
  exact Concept.ext (image_comp e₂.objEquiv e₁.objEquiv c.extent)

@[simp]
theorem conceptIso_ofObjects (s : Set α₁) :
    e.conceptIso (.ofObjects r₁ s) = .ofObjects r₂ (e.objEquiv '' s) :=
  Concept.ext' (e.upperPolar_image s).symm

@[simp]
theorem conceptIso_ofAttributes (t : Set β₁) :
    e.conceptIso (.ofAttributes r₁ t) = .ofAttributes r₂ (e.attrEquiv '' t) :=
  Concept.ext (e.lowerPolar_image t).symm

end ContextIso

/-! ### Infomorphisms -/

/-- An *infomorphism* (or *Chu morphism*) from the context `r₁` to the context `r₂`: a map on
objects and a map on attributes in the opposite direction which are adjoint with respect to the
incidence relations. -/
structure Infomorphism (r₁ : α₁ → β₁ → Prop) (r₂ : α₂ → β₂ → Prop) where
  /-- The map on objects. -/
  objMap : α₁ → α₂
  /-- The map on attributes, in the opposite direction. -/
  attrMap : β₂ → β₁
  /-- The two maps of an infomorphism are adjoint with respect to the incidence. -/
  rel_iff' : ∀ a b, r₁ a (attrMap b) ↔ r₂ (objMap a) b

namespace Infomorphism

@[ext]
theorem ext {f g : Infomorphism r₁ r₂} (hobj : f.objMap = g.objMap)
    (hattr : f.attrMap = g.attrMap) : f = g := by
  cases f
  cases g
  congr

theorem rel_iff (f : Infomorphism r₁ r₂) {a : α₁} {b : β₂} :
    r₁ a (f.attrMap b) ↔ r₂ (f.objMap a) b :=
  f.rel_iff' a b

/-- The identity infomorphism of a context. -/
@[simps]
protected def id (r : α₁ → β₁ → Prop) : Infomorphism r r where
  objMap := id
  attrMap := id
  rel_iff' _ _ := Iff.rfl

instance : Inhabited (Infomorphism r₁ r₁) :=
  ⟨.id r₁⟩

/-- The composition of infomorphisms. -/
@[simps]
def comp (g : Infomorphism r₂ r₃) (f : Infomorphism r₁ r₂) : Infomorphism r₁ r₃ where
  objMap := g.objMap ∘ f.objMap
  attrMap := f.attrMap ∘ g.attrMap
  rel_iff' _ _ := f.rel_iff.trans g.rel_iff

@[simp]
theorem comp_id (f : Infomorphism r₁ r₂) : f.comp (.id r₁) = f :=
  rfl

@[simp]
theorem id_comp (f : Infomorphism r₁ r₂) : (Infomorphism.id r₂).comp f = f :=
  rfl

theorem comp_assoc (h : Infomorphism r₃ r₄) (g : Infomorphism r₂ r₃) (f : Infomorphism r₁ r₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/-- An infomorphism from `r₁` to `r₂` is an infomorphism between the dual contexts, from
`swap r₂` to `swap r₁`. -/
@[simps]
protected def swap (f : Infomorphism r₁ r₂) : Infomorphism (swap r₂) (swap r₁) where
  objMap := f.attrMap
  attrMap := f.objMap
  rel_iff' _ _ := f.rel_iff.symm

variable (f : Infomorphism r₁ r₂)

/-- The preimage of a lower polar under the object map of an infomorphism. -/
theorem preimage_lowerPolar (t : Set β₂) :
    f.objMap ⁻¹' lowerPolar r₂ t = lowerPolar r₁ (f.attrMap '' t) := by
  ext a
  simp [mem_lowerPolar_iff, f.rel_iff]

/-- The preimage of an upper polar under the attribute map of an infomorphism. -/
theorem preimage_upperPolar (s : Set α₁) :
    f.attrMap ⁻¹' upperPolar r₁ s = upperPolar r₂ (f.objMap '' s) :=
  f.swap.preimage_lowerPolar s

variable {f} in
/-- The preimage of an extent under the object map of an infomorphism is an extent. -/
theorem isExtent_preimage {s : Set α₂} (hs : IsExtent r₂ s) : IsExtent r₁ (f.objMap ⁻¹' s) := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨_, (f.preimage_lowerPolar t).symm⟩

variable {f} in
/-- The preimage of an intent under the attribute map of an infomorphism is an intent. -/
theorem isIntent_preimage {t : Set β₁} (ht : IsIntent r₁ t) : IsIntent r₂ (f.attrMap ⁻¹' t) :=
  f.swap.isExtent_preimage ht

/-! ### The maps between concept lattices induced by an infomorphism -/

/-- The supremum-preserving map between concept lattices induced by an infomorphism: the concept
with intent `B` is sent to the concept whose intent is the preimage of `B` under the attribute
map. -/
def map : sSupHom (Concept α₁ β₁ r₁) (Concept α₂ β₂ r₂) where
  toFun c := .ofIsIntent r₂ (f.attrMap ⁻¹' c.intent) (isIntent_preimage c.isIntent_intent)
  map_sSup' S := Concept.ext' <| by simp [preimage_iInter₂]

@[simp]
theorem intent_map (c : Concept α₁ β₁ r₁) : (f.map c).intent = f.attrMap ⁻¹' c.intent :=
  rfl

@[simp]
theorem extent_map (c : Concept α₁ β₁ r₁) :
    (f.map c).extent = lowerPolar r₂ (f.attrMap ⁻¹' c.intent) :=
  rfl

/-- The infimum-preserving map between concept lattices induced by an infomorphism: the concept
with extent `A` is sent to the concept whose extent is the preimage of `A` under the object
map. -/
def comap : sInfHom (Concept α₂ β₂ r₂) (Concept α₁ β₁ r₁) where
  toFun c := .ofIsExtent r₁ (f.objMap ⁻¹' c.extent) (isExtent_preimage c.isExtent_extent)
  map_sInf' S := Concept.ext <| by simp [preimage_iInter₂]

@[simp]
theorem extent_comap (c : Concept α₂ β₂ r₂) : (f.comap c).extent = f.objMap ⁻¹' c.extent :=
  rfl

@[simp]
theorem intent_comap (c : Concept α₂ β₂ r₂) :
    (f.comap c).intent = upperPolar r₁ (f.objMap ⁻¹' c.extent) :=
  rfl

theorem map_le_iff {c : Concept α₁ β₁ r₁} {d : Concept α₂ β₂ r₂} :
    f.map c ≤ d ↔ c ≤ f.comap d := by
  rw [← Concept.intent_subset_intent_iff, intent_map, ← image_subset_iff,
    ← Concept.extent_subset_extent_iff, extent_comap, ← d.lowerPolar_intent,
    preimage_lowerPolar, ← subset_upperPolar_iff_subset_lowerPolar, c.upperPolar_extent]

/-- The maps between concept lattices induced by an infomorphism form a Galois connection. -/
theorem gc_map_comap : GaloisConnection f.map f.comap :=
  fun _ _ => f.map_le_iff

@[simp]
theorem map_id : (Infomorphism.id r₁).map = sSupHom.id _ :=
  sSupHom.ext fun _ => Concept.ext' rfl

@[simp]
theorem comap_id : (Infomorphism.id r₁).comap = sInfHom.id _ :=
  sInfHom.ext fun _ => Concept.ext rfl

theorem map_comp (g : Infomorphism r₂ r₃) (f : Infomorphism r₁ r₂) :
    (g.comp f).map = g.map.comp f.map :=
  sSupHom.ext fun _ => Concept.ext' rfl

theorem comap_comp (g : Infomorphism r₂ r₃) (f : Infomorphism r₁ r₂) :
    (g.comp f).comap = f.comap.comp g.comap :=
  sInfHom.ext fun _ => Concept.ext rfl

/-! ### Infomorphisms and bonds -/

/-- The bond of an infomorphism `(f, g)`, relating `a` to `d` iff `f a` is incident with `d`, or
equivalently iff `a` is incident with `g d`. -/
def toBond : Bond r₁ r₂ where
  rel a d := r₂ (f.objMap a) d
  isIntent_upperPolar_singleton a := by
    convert isIntent_upperPolar (r := r₂) (s := {f.objMap a})
    ext d
    simp
  isExtent_lowerPolar_singleton d := by
    convert isExtent_lowerPolar (r := r₁) (t := {f.attrMap d})
    ext a
    simp [f.rel_iff]

theorem toBond_rel_iff {a : α₁} {d : β₂} : f.toBond.rel a d ↔ r₂ (f.objMap a) d :=
  Iff.rfl

theorem toBond_rel_iff' {a : α₁} {d : β₂} : f.toBond.rel a d ↔ r₁ a (f.attrMap d) :=
  f.rel_iff.symm

@[simp]
theorem toBond_id : (Infomorphism.id r₁).toBond = .refl r₁ :=
  rfl

/-- The map of concept lattices induced by the bond of an infomorphism is the map induced by the
infomorphism. -/
@[simp]
theorem map_toBond : f.toBond.map = f.map := by
  refine sSupHom.ext fun c => Concept.ext' ?_
  rw [Bond.intent_map, intent_map, ← c.upperPolar_extent, preimage_upperPolar]
  ext d
  simp [mem_upperPolar_iff, toBond_rel_iff]

@[simp]
theorem comap_toBond : f.toBond.comap = f.comap := by
  refine sInfHom.ext fun c => Concept.ext ?_
  rw [Bond.extent_comap, extent_comap, ← c.lowerPolar_intent, preimage_lowerPolar]
  ext a
  simp [mem_lowerPolar_iff, toBond_rel_iff']

/-- Passing from infomorphisms to bonds turns composition into the bond product. -/
theorem toBond_comp (g : Infomorphism r₂ r₃) (f : Infomorphism r₁ r₂) :
    (g.comp f).toBond = f.toBond.trans g.toBond :=
  Bond.equivSSupHom.injective <| by
    simp only [Bond.equivSSupHom_apply, Bond.map_trans, map_toBond, map_comp]

end Infomorphism

/-- A context isomorphism is an infomorphism. -/
@[simps]
def ContextIso.toInfomorphism (e : ContextIso r₁ r₂) : Infomorphism r₁ r₂ where
  objMap := e.objEquiv
  attrMap := e.attrEquiv.symm
  rel_iff' a b := by rw [← e.rel_iff, Equiv.apply_symm_apply]

/-- The map of concept lattices induced by a context isomorphism, viewed as an infomorphism, is
the induced isomorphism of concept lattices. -/
theorem ContextIso.toInfomorphism_map_apply (e : ContextIso r₁ r₂) (c : Concept α₁ β₁ r₁) :
    e.toInfomorphism.map c = e.conceptIso c :=
  Concept.ext' (e.attrEquiv.image_eq_preimage_symm c.intent).symm

end FCA
