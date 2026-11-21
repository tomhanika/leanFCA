/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem
public import FCA.ScaleMeasure.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The lattice of scale-measures

The scale-measures of a context `r`, ordered by refinement and identified up to equivalence, form
the *scale-hierarchy* of `r`. Following Hanika and Hirth, *On the Lattice of Conceptual
Measurements*, this file shows that the scale-hierarchy is isomorphic to the lattice of
closure systems contained in the system of extents of `r`.

## Main definitions

* `FCA.ClosureSubsystem (IsExtent r)`: the closure systems on the objects consisting of
  extents of `r`, a complete lattice under inclusion. The general theory of
  `FCA.ClosureSubsystem p` for a closure system `p` lives in `FCA.Order.ClosureSubsystem`.
* `FCA.ClosureSubsystem.context`: the canonical scale context `(G, 𝒜, ∈)` of a closure system.
* `FCA.IsScaleMeasure.closureSubsystem`: the closure system of extents reflected by a
  scale-measure.
* `FCA.ScaleMeasure r`: bundled scale-measures of `r`, a preorder under refinement.
* `FCA.ScaleHierarchy r`: scale-measures up to equivalence.

## Main results

* `FCA.ClosureSubsystem.isExtent_context_iff`: the extents of `(G, 𝒜, ∈)` are the members of `𝒜`
  (Lemma 8).
* `FCA.ClosureSubsystem.isScaleMeasure_context`: the identity is a scale-measure into the
  canonical context (Lemma 9).
* `FCA.IsScaleMeasure.scaleEquiv_context`: every scale-measure is equivalent to its canonical
  representation (Proposition 10).
* `FCA.scaleHierarchyIso`: the scale-hierarchy is isomorphic to the lattice of closure
  subsystems (Proposition 11), hence a complete lattice (Corollary 12).
* `FCA.ClosureSubsystem.mem_inf`, `FCA.ClosureSubsystem.mem_sup`: meet and join
  (Proposition 13).

## Implementation notes

In the literature the scale-measures of a context form a proper class, since the scale may be any
context. `FCA.ScaleMeasure r` therefore bundles only scales living in the universe of the objects
of `r`. By the canonical representation this loses no equivalence classes:
see `FCA.IsScaleMeasure.scaleEquiv_context`, which is universe polymorphic.

## References

* [T. Hanika, J. Hirth, *On the Lattice of Conceptual Measurements*][hanika2022]
-/

@[expose] public section

open Set Function Order

universe u v

namespace FCA

variable {α : Type u} {β : Type v} {γ δ ε ζ : Type*} {r : α → β → Prop} {s : γ → δ → Prop}
  {t : ε → ζ → Prop} {σ : α → γ} {ψ : α → ε}

/-! ### Closure systems of extents -/

/-- The extents of a context form a closure system. -/
instance : IsClosureSystem (IsExtent r) :=
  ⟨fun _ hS ↦ .sInter hS⟩

/-- The extents of a context with finitely many attributes satisfy the ascending chain
condition, whatever the number of objects. -/
instance [Finite β] : IsNoetherianClosureSystem (IsExtent r) :=
  ⟨Subrelation.wf (r := InvImage (· < ·) fun A : {A : Set α // IsExtent r A} ↦ upperPolar r A)
    (fun {B A} hAB ↦ (upperPolar_anti r hAB.subset).lt_of_ne fun h ↦
      hAB.ne (by rw [← A.2.eq, ← B.2.eq, h]))
    (InvImage.wf _ wellFounded_lt)⟩

namespace ClosureSubsystem

theorem isExtent {𝒜 : ClosureSubsystem (IsExtent r)} {A : Set α} (hA : A ∈ 𝒜) : IsExtent r A :=
  𝒜.isClosed hA

/-- The closure system of all extents of a context. -/
abbrev extents (r : α → β → Prop) : ClosureSubsystem (IsExtent r) :=
  closeds (IsExtent r)

variable {𝒜 ℬ : ClosureSubsystem (IsExtent r)} {A B : Set α}

/-! ### The canonical scale of a closure system -/

/-- The canonical scale context `(G, 𝒜, ∈)` of a closure system `𝒜`: its attributes are the
closed sets, and an object has the attribute `A` if it belongs to `A`. -/
def context (𝒜 : ClosureSubsystem (IsExtent r)) : α → {A // A ∈ 𝒜} → Prop :=
  fun a A ↦ a ∈ A.1

theorem lowerPolar_context (T : Set {A // A ∈ 𝒜}) :
    lowerPolar 𝒜.context T = ⋂₀ (Subtype.val '' T) := by
  ext a
  simp [mem_lowerPolar_iff, context]

/-- The extents of the canonical scale of `𝒜` are exactly the members of `𝒜`. -/
@[simp]
theorem isExtent_context_iff : IsExtent 𝒜.context A ↔ A ∈ 𝒜 := by
  constructor
  · rintro ⟨T, rfl⟩
    rw [lowerPolar_context]
    refine 𝒜.sInter_mem ?_
    rintro _ ⟨B, -, rfl⟩
    exact B.2
  · intro hA
    refine ⟨{⟨A, hA⟩}, ?_⟩
    simp [lowerPolar_context]

/-- The identity is a scale-measure into the canonical scale of a closure system of extents. -/
theorem isScaleMeasure_context (𝒜 : ClosureSubsystem (IsExtent r)) :
    IsScaleMeasure r 𝒜.context id :=
  fun _ hA ↦ 𝒜.isExtent (isExtent_context_iff.1 hA)

@[simp]
theorem scaleExtents_context (𝒜 : ClosureSubsystem (IsExtent r)) :
    scaleExtents 𝒜.context id = 𝒜.carrier := by
  ext A
  simp [scaleExtents]

end ClosureSubsystem

/-! ### The closure system of a scale-measure -/

/-- The closure system of the extents reflected by a scale-measure. -/
def IsScaleMeasure.closureSubsystem (h : IsScaleMeasure r s σ) : ClosureSubsystem (IsExtent r) where
  carrier := scaleExtents s σ
  sInter_mem' _ hS := sInter_mem_scaleExtents hS
  isClosed' _ hA := isScaleMeasure_iff_scaleExtents_subset.1 h hA

@[simp]
theorem IsScaleMeasure.mem_closureSubsystem (h : IsScaleMeasure r s σ) {A : Set α} :
    A ∈ h.closureSubsystem ↔ A ∈ scaleExtents s σ :=
  Iff.rfl

/-- **Canonical representation**: every scale-measure is equivalent to the identity measure
into the canonical scale of its reflected extents. -/
theorem IsScaleMeasure.scaleEquiv_context (h : IsScaleMeasure r s σ) :
    ScaleEquiv s σ h.closureSubsystem.context id :=
  (ClosureSubsystem.scaleExtents_context h.closureSubsystem).symm

@[simp]
theorem ClosureSubsystem.closureSubsystem_context (𝒜 : ClosureSubsystem (IsExtent r)) :
    𝒜.isScaleMeasure_context.closureSubsystem = 𝒜 :=
  ClosureSubsystem.ext 𝒜.scaleExtents_context

/-- Refinement of scale-measures is inclusion of the associated closure systems. -/
theorem scaleCoarser_iff_closureSubsystem_le (hσ : IsScaleMeasure r s σ)
    (hψ : IsScaleMeasure r t ψ) :
    ScaleCoarser s σ t ψ ↔ hσ.closureSubsystem ≤ hψ.closureSubsystem :=
  Iff.rfl

theorem scaleEquiv_iff_closureSubsystem_eq (hσ : IsScaleMeasure r s σ)
    (hψ : IsScaleMeasure r t ψ) :
    ScaleEquiv s σ t ψ ↔ hσ.closureSubsystem = hψ.closureSubsystem :=
  ⟨fun h ↦ ClosureSubsystem.ext h, fun h ↦ congrArg ClosureSubsystem.carrier h⟩

/-- The identity measure of a context into itself is the finest scale-measure. -/
@[simp]
theorem closureSubsystem_id (r : α → β → Prop) : (isScaleMeasure_id r).closureSubsystem = ⊤ := by
  rw [ClosureSubsystem.top_eq]
  exact ClosureSubsystem.ext (scaleExtents_id r)

/-- The join of two scale-measures with the same measure map is their apposition. -/
theorem IsScaleMeasure.closureSubsystem_apposition {s₂ : γ → ζ → Prop}
    (h₁ : IsScaleMeasure r s σ) (h₂ : IsScaleMeasure r s₂ σ) :
    (h₁.apposition h₂).closureSubsystem = h₁.closureSubsystem ⊔ h₂.closureSubsystem := by
  rw [ClosureSubsystem.sup_eq]
  exact ClosureSubsystem.ext (scaleExtents_apposition s s₂ σ)

/-- The join of two arbitrary scale-measures, as a scale-measure in canonical form. -/
theorem IsScaleMeasure.scaleExtents_sup (hσ : IsScaleMeasure r s σ)
    (hψ : IsScaleMeasure r t ψ) :
    scaleExtents (hσ.closureSubsystem ⊔ hψ.closureSubsystem).context id =
      {C | ∃ A ∈ scaleExtents s σ, ∃ B ∈ scaleExtents t ψ, A ∩ B = C} := by
  rw [ClosureSubsystem.scaleExtents_context, ClosureSubsystem.sup_eq]
  rfl

/-- The meet of two arbitrary scale-measures, as a scale-measure in canonical form. -/
theorem IsScaleMeasure.scaleExtents_inf (hσ : IsScaleMeasure r s σ)
    (hψ : IsScaleMeasure r t ψ) :
    scaleExtents (hσ.closureSubsystem ⊓ hψ.closureSubsystem).context id =
      scaleExtents s σ ∩ scaleExtents t ψ := by
  rw [ClosureSubsystem.scaleExtents_context]
  ext A
  exact ClosureSubsystem.mem_inf

/-! ### The scale-hierarchy -/

/-- A bundled scale-measure of the context `r`, whose scale lives in the universe of the objects
of `r`. -/
structure ScaleMeasure (r : α → β → Prop) where
  /-- The objects of the scale. -/
  Obj : Type u
  /-- The attributes of the scale. -/
  Attr : Type u
  /-- The scale context. -/
  scale : Obj → Attr → Prop
  /-- The measure map. -/
  toFun : α → Obj
  /-- The measure map reflects extents. -/
  isScaleMeasure : IsScaleMeasure r scale toFun

namespace ScaleMeasure

/-- The closure system of extents reflected by a bundled scale-measure. -/
def closureSubsystem (m : ScaleMeasure r) : ClosureSubsystem (IsExtent r) :=
  m.isScaleMeasure.closureSubsystem

/-- Scale-measures are preordered by refinement: `m ≤ n` if `m` is coarser than `n`. -/
instance : Preorder (ScaleMeasure r) :=
  .lift closureSubsystem

theorem le_iff_scaleCoarser {m n : ScaleMeasure r} :
    m ≤ n ↔ ScaleCoarser m.scale m.toFun n.scale n.toFun :=
  Iff.rfl

theorem le_iff_closureSubsystem_le {m n : ScaleMeasure r} :
    m ≤ n ↔ m.closureSubsystem ≤ n.closureSubsystem :=
  Iff.rfl

/-- The canonical scale-measure of a closure system of extents. -/
def canonical (𝒜 : ClosureSubsystem (IsExtent r)) : ScaleMeasure r where
  Obj := α
  Attr := {A // A ∈ 𝒜}
  scale := 𝒜.context
  toFun := id
  isScaleMeasure := 𝒜.isScaleMeasure_context

@[simp]
theorem closureSubsystem_canonical (𝒜 : ClosureSubsystem (IsExtent r)) :
    (canonical 𝒜).closureSubsystem = 𝒜 :=
  𝒜.closureSubsystem_context

/-- Every scale-measure is equivalent to its canonical representation. -/
theorem antisymmRel_canonical (m : ScaleMeasure r) :
    AntisymmRel (· ≤ ·) (canonical m.closureSubsystem) m := by
  simp [AntisymmRel, le_iff_closureSubsystem_le]

end ScaleMeasure

/-- The *scale-hierarchy* of a context: its scale-measures up to equivalence, ordered by
refinement. -/
abbrev ScaleHierarchy (r : α → β → Prop) : Type _ :=
  Antisymmetrization (ScaleMeasure r) (· ≤ ·)

/-- The scale-hierarchy of a context is isomorphic to the lattice of closure systems of extents
of the context. -/
noncomputable def scaleHierarchyIso (r : α → β → Prop) :
    ClosureSubsystem (IsExtent r) ≃o ScaleHierarchy r :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff
      (fun 𝒜 ↦ toAntisymmetrization (· ≤ ·) (ScaleMeasure.canonical 𝒜)) fun 𝒜 ℬ ↦ by
        rw [toAntisymmetrization_le_toAntisymmetrization_iff,
          ScaleMeasure.le_iff_closureSubsystem_le, ScaleMeasure.closureSubsystem_canonical,
          ScaleMeasure.closureSubsystem_canonical])
    fun x ↦ by
      induction x using Quotient.inductionOn with
      | _ m => exact ⟨m.closureSubsystem, Quotient.sound m.antisymmRel_canonical⟩

@[simp]
theorem scaleHierarchyIso_apply (𝒜 : ClosureSubsystem (IsExtent r)) :
    scaleHierarchyIso r 𝒜 = toAntisymmetrization (· ≤ ·) (ScaleMeasure.canonical 𝒜) :=
  rfl

@[simp]
theorem scaleHierarchyIso_symm_apply (m : ScaleMeasure r) :
    (scaleHierarchyIso r).symm (toAntisymmetrization (· ≤ ·) m) = m.closureSubsystem := by
  rw [OrderIso.symm_apply_eq, scaleHierarchyIso_apply]
  exact (Quotient.sound m.antisymmRel_canonical).symm

/-- The scale-hierarchy of a context is a complete lattice. -/
noncomputable instance : CompleteLattice (ScaleHierarchy r) :=
  (scaleHierarchyIso r).toGaloisInsertion.liftCompleteLattice

end FCA
