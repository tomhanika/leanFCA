/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Context.Constructions
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ferrers relations and Ferrers covers

A *Ferrers relation* is a relation `F` such that `F a b` and `F a' b'` imply `F a b'` or
`F a' b`. Equivalently, the extents of `F` form a chain. The *Ferrers dimension* of a context is
the least number of Ferrers relations whose intersection is the incidence. Since cardinalities of
index types are awkward to work with, this file uses the predicate `FCA.HasFerrersCover r ι`: the
incidence `r` is the intersection of a family of Ferrers relations indexed by `ι`, that is, `r`
has Ferrers dimension at most the cardinality of `ι`.

## Main definitions

* `FCA.IsFerrers F`: `F` is a Ferrers relation.
* `FCA.IsFerrers.linearOrderExtents`: the extents of a Ferrers relation form a chain.
* `FCA.HasFerrersCover r ι`: the incidence `r` is the intersection of a family of Ferrers
  relations indexed by `ι`.

## Main results

* `FCA.IsFerrers.isExtent_total`: the extents of a Ferrers relation are totally ordered by
  inclusion.
* `FCA.HasFerrersCover.apposition`: the Ferrers dimension of an apposition is at most the sum of
  the Ferrers dimensions of its parts.
* `FCA.hasFerrersCover_ne_iff`: the contranominal scale on `α` has a Ferrers cover indexed by `ι`
  if and only if `α` embeds into `ι`, i.e. its Ferrers dimension is the cardinality of `α`.
* `FCA.hasFerrersCover_apposition_ne_inl_ne_inr_iff`: the bound for appositions is sharp.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Function Order

namespace FCA

variable {α β γ δ ζ ι κ : Type*} {r : α → β → Prop}

/-! ### Ferrers relations -/

/-- A relation `F` is a *Ferrers relation* if `F a b` and `F a' b'` imply `F a b'` or
`F a' b`. -/
def IsFerrers (F : α → β → Prop) : Prop :=
  ∀ ⦃a b a' b'⦄, F a b → F a' b' → F a b' ∨ F a' b

theorem IsFerrers.comp {F : α → β → Prop} (hF : IsFerrers F) (f : γ → α) (g : δ → β) :
    IsFerrers fun c d ↦ F (f c) (g d) :=
  fun _ _ _ _ h h' ↦ hF h h'

theorem isFerrers_top : IsFerrers fun (_ : α) (_ : β) ↦ True :=
  fun _ _ _ _ _ _ ↦ .inl trivial

/-- The extents of a Ferrers relation are totally ordered by inclusion. -/
theorem IsFerrers.isExtent_total {F : α → β → Prop} (hF : IsFerrers F) {A B : Set α}
    (hA : IsExtent F A) (hB : IsExtent F B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨T, rfl⟩ := hA
  obtain ⟨T', rfl⟩ := hB
  refine or_iff_not_imp_left.2 fun h b hb m hm ↦ ?_
  obtain ⟨a, ha, ha'⟩ := not_subset.1 h
  obtain ⟨m', hm', ham'⟩ : ∃ m' ∈ T', ¬ F a m' := by
    by_contra! hc
    exact ha' fun m' hm' ↦ hc m' hm'
  exact (hF (ha hm) (hb hm')).resolve_left ham'

/-- The extents of a Ferrers relation form a chain under inclusion. -/
@[implicit_reducible]
noncomputable def IsFerrers.linearOrderExtents {F : α → β → Prop} (hF : IsFerrers F) :
    LinearOrder {A // IsExtent F A} where
  le_total A B := hF.isExtent_total A.2 B.2
  toDecidableLE := Classical.decRel _

/-! ### Ferrers covers -/

/-- The incidence `r` is the intersection of a family of Ferrers relations indexed by `ι`. -/
def HasFerrersCover (r : α → β → Prop) (ι : Type*) : Prop :=
  ∃ F : ι → α → β → Prop, (∀ i, IsFerrers (F i)) ∧ ∀ a b, r a b ↔ ∀ i, F i a b

/-- A Ferrers cover restricts along maps of objects and attributes. -/
theorem HasFerrersCover.comp (h : HasFerrersCover r ι) (f : γ → α) (g : δ → β) :
    HasFerrersCover (fun c d ↦ r (f c) (g d)) ι :=
  let ⟨F, hF, hr⟩ := h
  ⟨fun i c d ↦ F i (f c) (g d), fun i ↦ (hF i).comp f g, fun _ _ ↦ hr _ _⟩

/-- A Ferrers cover can be reindexed along a surjection. -/
theorem HasFerrersCover.of_surjective (h : HasFerrersCover r ι) (e : κ → ι)
    (he : Surjective e) : HasFerrersCover r κ :=
  let ⟨F, hF, hr⟩ := h
  ⟨fun k ↦ F (e k), fun k ↦ hF (e k), fun a b ↦ (hr a b).trans he.forall⟩

/-- The Ferrers dimension of an apposition is at most the sum of the Ferrers dimensions. -/
theorem HasFerrersCover.apposition {r₂ : α → ζ → Prop} (h₁ : HasFerrersCover r ι)
    (h₂ : HasFerrersCover r₂ κ) : HasFerrersCover (apposition r r₂) (ι ⊕ κ) := by
  obtain ⟨F, hF, hr⟩ := h₁
  obtain ⟨F', hF', hr'⟩ := h₂
  refine ⟨Sum.elim (fun i a ↦ Sum.elim (F i a) fun _ ↦ True)
    (fun k a ↦ Sum.elim (fun _ ↦ True) (F' k a)), ?_, ?_⟩
  · rintro (i | k) a (b | b) a' (b' | b') h h' <;>
      first | exact hF i h h' | exact hF' k h h' | exact .inl trivial | exact .inr trivial
  · rintro a (b | b) <;> simp [hr, hr']

/-- The Ferrers dimension of an apposition, for finite dimensions. -/
theorem HasFerrersCover.apposition_fin {r₂ : α → ζ → Prop} {m n : ℕ}
    (h₁ : HasFerrersCover r (Fin m)) (h₂ : HasFerrersCover r₂ (Fin n)) :
    HasFerrersCover (FCA.apposition r r₂) (Fin (m + n)) :=
  (h₁.apposition h₂).of_surjective finSumFinEquiv.symm finSumFinEquiv.symm.surjective

/-! ### The Ferrers dimension of contranominal scales -/

/-- A context whose incidence is `a ≠ g b` for an injective map `g` from the attributes to the
objects has a Ferrers cover indexed by `ι` if and only if the attributes embed into `ι`: a
Ferrers relation containing the incidence omits at most one of the pairs `(g b, b)`. -/
theorem hasFerrersCover_ne_comp_iff {g : β → α} (hg : Injective g) :
    HasFerrersCover (fun a b ↦ a ≠ g b) ι ↔ Nonempty (β ↪ ι) := by
  constructor
  · rintro ⟨F, hF, hr⟩
    have h : ∀ b, ∃ i, ¬ F i (g b) b := fun b ↦ by
      by_contra! hc
      exact (hr (g b) b).2 hc rfl
    choose e he using h
    refine ⟨⟨e, fun b b' hbb' ↦ ?_⟩⟩
    by_contra hne
    rcases hF (e b) ((hr (g b) b').1 (hg.ne hne) _) ((hr (g b') b).1 (hg.ne (Ne.symm hne)) _)
      with h | h
    · exact he b h
    · exact he b' (hbb' ▸ h)
  · rintro ⟨e⟩
    refine ⟨fun i a b ↦ ¬ (e b = i ∧ a = g b), fun i a b a' b' h h' ↦ ?_, fun a b ↦
      ⟨fun h i hi ↦ h hi.2, fun h hab ↦ h (e b) ⟨rfl, hab⟩⟩⟩
    by_contra! hc
    obtain ⟨⟨rfl, rfl⟩, hb, -⟩ := hc
    exact h ⟨hb, congrArg g (e.injective hb.symm)⟩

/-- The contranominal scale on `α` has a Ferrers cover indexed by `ι` if and only if `α` embeds
into `ι`. In other words, its Ferrers dimension is the cardinality of `α`. -/
theorem hasFerrersCover_ne_iff :
    HasFerrersCover (fun a b : α ↦ a ≠ b) ι ↔ Nonempty (α ↪ ι) :=
  hasFerrersCover_ne_comp_iff injective_id

/-- The bound `FCA.HasFerrersCover.apposition` is sharp: the contranominal scale on `β ⊕ ζ` is
the apposition of two contexts of Ferrers dimension `β` and `ζ`
(by `FCA.hasFerrersCover_ne_comp_iff`), and it has Ferrers dimension `β ⊕ ζ`. -/
theorem hasFerrersCover_apposition_ne_inl_ne_inr_iff :
    HasFerrersCover (apposition (fun (a : β ⊕ ζ) (b : β) ↦ a ≠ .inl b)
      fun (a : β ⊕ ζ) (c : ζ) ↦ a ≠ .inr c) ι ↔ Nonempty (β ⊕ ζ ↪ ι) := by
  have h : apposition (fun (a : β ⊕ ζ) (b : β) ↦ a ≠ .inl b)
      (fun (a : β ⊕ ζ) (c : ζ) ↦ a ≠ .inr c) = fun a b ↦ a ≠ b := by
    ext a (b | c) <;> rfl
  rw [h, hasFerrersCover_ne_iff]

end FCA
