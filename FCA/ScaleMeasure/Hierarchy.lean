/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

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

* `FCA.ClosureSubsystem r`: the closure systems on the objects consisting of extents of `r`,
  a complete lattice under inclusion.
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

/-- A closure system on the objects of the context `r` all of whose members are extents of
`r`. -/
@[ext]
structure ClosureSubsystem (r : α → β → Prop) where
  /-- The closed sets of the closure system. -/
  carrier : Set (Set α)
  /-- A closure system is closed under arbitrary intersections. -/
  sInter_mem' : ∀ ⦃S : Set (Set α)⦄, S ⊆ carrier → ⋂₀ S ∈ carrier
  /-- All closed sets are extents. -/
  isExtent' : ∀ ⦃A : Set α⦄, A ∈ carrier → IsExtent r A

namespace ClosureSubsystem

variable {𝒜 ℬ : ClosureSubsystem r} {A B : Set α}

instance : Membership (Set α) (ClosureSubsystem r) :=
  ⟨fun 𝒜 A ↦ A ∈ 𝒜.carrier⟩

@[simp]
theorem mem_carrier : A ∈ 𝒜.carrier ↔ A ∈ 𝒜 :=
  Iff.rfl

@[simp]
theorem mem_mk {C : Set (Set α)} {h₁ h₂} : A ∈ (⟨C, h₁, h₂⟩ : ClosureSubsystem r) ↔ A ∈ C :=
  Iff.rfl

theorem carrier_injective : Injective (carrier : ClosureSubsystem r → Set (Set α)) :=
  fun _ _ ↦ ClosureSubsystem.ext

instance : PartialOrder (ClosureSubsystem r) :=
  .lift carrier carrier_injective

theorem le_def : 𝒜 ≤ ℬ ↔ ∀ ⦃A⦄, A ∈ 𝒜 → A ∈ ℬ :=
  Iff.rfl

theorem sInter_mem {S : Set (Set α)} (hS : ∀ A ∈ S, A ∈ 𝒜) : ⋂₀ S ∈ 𝒜 :=
  𝒜.sInter_mem' hS

theorem isExtent (hA : A ∈ 𝒜) : IsExtent r A :=
  𝒜.isExtent' hA

theorem univ_mem (𝒜 : ClosureSubsystem r) : univ ∈ 𝒜 := by
  simpa using 𝒜.sInter_mem (S := ∅) (by simp)

theorem inter_mem (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) : A ∩ B ∈ 𝒜 := by
  simpa using 𝒜.sInter_mem (S := {A, B}) (by simp [hA, hB])

/-- The closure system of all extents of a context. -/
def extents (r : α → β → Prop) : ClosureSubsystem r where
  carrier := {A | IsExtent r A}
  sInter_mem' _ hS := .sInter hS
  isExtent' _ hA := hA

/-- The closure system consisting only of the whole object set. -/
def trivial (r : α → β → Prop) : ClosureSubsystem r where
  carrier := {univ}
  sInter_mem' S hS := by
    rw [mem_singleton_iff, sInter_eq_univ]
    exact fun A hA ↦ hS hA
  isExtent' := by
    rintro _ rfl
    exact .univ

instance : InfSet (ClosureSubsystem r) where
  sInf 𝒮 :=
    { carrier := {A | IsExtent r A ∧ ∀ 𝒜 ∈ 𝒮, A ∈ 𝒜}
      sInter_mem' := fun _ hS ↦
        ⟨.sInter fun _ hA ↦ (hS hA).1, fun 𝒜 h𝒜 ↦ 𝒜.sInter_mem fun _ hA ↦ (hS hA).2 𝒜 h𝒜⟩
      isExtent' := fun _ hA ↦ hA.1 }

theorem mem_sInf {𝒮 : Set (ClosureSubsystem r)} :
    A ∈ sInf 𝒮 ↔ IsExtent r A ∧ ∀ 𝒜 ∈ 𝒮, A ∈ 𝒜 :=
  Iff.rfl

/-- The closure systems of extents of a context form a complete lattice under inclusion. -/
instance : CompleteLattice (ClosureSubsystem r) :=
  completeLatticeOfInf _ fun _ ↦
    ⟨fun _ h𝒜 ↦ le_def.2 fun _ hA ↦ (mem_sInf.1 hA).2 _ h𝒜, fun _ hℬ ↦ le_def.2 fun _ hA ↦
      mem_sInf.2 ⟨isExtent hA, fun _ h𝒜 ↦ le_def.1 (hℬ h𝒜) hA⟩⟩

@[simp]
theorem mem_top : A ∈ (⊤ : ClosureSubsystem r) ↔ IsExtent r A :=
  ⟨isExtent, fun hA ↦ le_top (a := extents r) hA⟩

theorem top_eq : (⊤ : ClosureSubsystem r) = extents r :=
  ClosureSubsystem.ext (Set.ext fun _ ↦ mem_top)

@[simp]
theorem mem_bot : A ∈ (⊥ : ClosureSubsystem r) ↔ A = univ :=
  ⟨fun hA ↦ bot_le (a := trivial r) hA, fun hA ↦ hA ▸ univ_mem _⟩

theorem bot_eq : (⊥ : ClosureSubsystem r) = trivial r :=
  ClosureSubsystem.ext (Set.ext fun _ ↦ mem_bot)

/-- The intersection of two closure systems. -/
def inter (𝒜 ℬ : ClosureSubsystem r) : ClosureSubsystem r where
  carrier := {A | A ∈ 𝒜 ∧ A ∈ ℬ}
  sInter_mem' _ hS :=
    ⟨𝒜.sInter_mem fun _ hA ↦ (hS hA).1, ℬ.sInter_mem fun _ hA ↦ (hS hA).2⟩
  isExtent' _ hA := 𝒜.isExtent hA.1

/-- The meet of two closure systems is their intersection. -/
@[simp]
theorem mem_inf : A ∈ 𝒜 ⊓ ℬ ↔ A ∈ 𝒜 ∧ A ∈ ℬ :=
  ⟨fun hA ↦ ⟨le_def.1 inf_le_left hA, le_def.1 inf_le_right hA⟩, fun hA ↦
    le_def.1 (le_inf (le_def.2 fun _ h ↦ h.1) (le_def.2 fun _ h ↦ h.2) : inter 𝒜 ℬ ≤ _) hA⟩

/-- The closure system of all intersections of a member of `𝒜` with a member of `ℬ`. -/
def pairwiseInter (𝒜 ℬ : ClosureSubsystem r) : ClosureSubsystem r where
  carrier := {C | ∃ A ∈ 𝒜, ∃ B ∈ ℬ, A ∩ B = C}
  sInter_mem' S hS := by
    have hS' : ∀ C, C ∈ S → ∃ A, A ∈ 𝒜 ∧ ∃ B, B ∈ ℬ ∧ A ∩ B = C := fun C hC ↦ hS hC
    choose! f hf g hg hfg using hS'
    refine ⟨⋂₀ (f '' S), 𝒜.sInter_mem ?_, ⋂₀ (g '' S), ℬ.sInter_mem ?_, ?_⟩
    · rintro _ ⟨C, hC, rfl⟩
      exact hf C hC
    · rintro _ ⟨C, hC, rfl⟩
      exact hg C hC
    · ext x
      simp only [mem_inter_iff, mem_sInter, forall_mem_image]
      refine ⟨fun h C hC ↦ ?_, fun h ↦ ⟨fun C hC ↦ ?_, fun C hC ↦ ?_⟩⟩
      · rw [← hfg C hC]
        exact ⟨h.1 hC, h.2 hC⟩
      · have := h C hC
        rw [← hfg C hC] at this
        exact this.1
      · have := h C hC
        rw [← hfg C hC] at this
        exact this.2
  isExtent' := by
    rintro _ ⟨A, hA, B, hB, rfl⟩
    exact (𝒜.isExtent hA).inter (ℬ.isExtent hB)

/-- The join of two closure systems consists of the pairwise intersections of their members. -/
theorem mem_sup : A ∈ 𝒜 ⊔ ℬ ↔ ∃ A₁ ∈ 𝒜, ∃ A₂ ∈ ℬ, A₁ ∩ A₂ = A := by
  constructor
  · refine fun hA ↦ le_def.1 (sup_le (le_def.2 fun C hC ↦ ?_) (le_def.2 fun C hC ↦ ?_) :
      𝒜 ⊔ ℬ ≤ pairwiseInter 𝒜 ℬ) hA
    · exact ⟨C, hC, univ, ℬ.univ_mem, inter_univ C⟩
    · exact ⟨univ, 𝒜.univ_mem, C, hC, univ_inter C⟩
  · rintro ⟨A₁, hA₁, A₂, hA₂, rfl⟩
    exact inter_mem (le_def.1 le_sup_left hA₁) (le_def.1 le_sup_right hA₂)

theorem sup_eq : 𝒜 ⊔ ℬ = pairwiseInter 𝒜 ℬ :=
  ClosureSubsystem.ext (Set.ext fun _ ↦ mem_sup)

/-! ### The canonical scale of a closure system -/

/-- The canonical scale context `(G, 𝒜, ∈)` of a closure system `𝒜`: its attributes are the
closed sets, and an object has the attribute `A` if it belongs to `A`. -/
def context (𝒜 : ClosureSubsystem r) : α → {A // A ∈ 𝒜} → Prop :=
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
theorem isScaleMeasure_context (𝒜 : ClosureSubsystem r) : IsScaleMeasure r 𝒜.context id :=
  fun _ hA ↦ 𝒜.isExtent (isExtent_context_iff.1 hA)

@[simp]
theorem scaleExtents_context (𝒜 : ClosureSubsystem r) :
    scaleExtents 𝒜.context id = 𝒜.carrier := by
  ext A
  simp [scaleExtents]

end ClosureSubsystem

/-! ### The closure system of a scale-measure -/

/-- The closure system of the extents reflected by a scale-measure. -/
def IsScaleMeasure.closureSubsystem (h : IsScaleMeasure r s σ) : ClosureSubsystem r where
  carrier := scaleExtents s σ
  sInter_mem' _ hS := sInter_mem_scaleExtents hS
  isExtent' _ hA := isScaleMeasure_iff_scaleExtents_subset.1 h hA

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
theorem ClosureSubsystem.closureSubsystem_context (𝒜 : ClosureSubsystem r) :
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
def closureSubsystem (m : ScaleMeasure r) : ClosureSubsystem r :=
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
def canonical (𝒜 : ClosureSubsystem r) : ScaleMeasure r where
  Obj := α
  Attr := {A // A ∈ 𝒜}
  scale := 𝒜.context
  toFun := id
  isScaleMeasure := 𝒜.isScaleMeasure_context

@[simp]
theorem closureSubsystem_canonical (𝒜 : ClosureSubsystem r) :
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
noncomputable def scaleHierarchyIso (r : α → β → Prop) : ClosureSubsystem r ≃o ScaleHierarchy r :=
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
theorem scaleHierarchyIso_apply (𝒜 : ClosureSubsystem r) :
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
