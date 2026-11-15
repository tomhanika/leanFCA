/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Armstrong rules: syntactic derivation of implications

This file introduces a syntactic notion of derivability of an implication from a set `L` of
implications, by means of the *Armstrong rules*, and shows that it coincides with semantic
entailment `FCA.Implication.Entails` whenever the sets involved are finite.

The rules are

* *axiom*: every implication of `L` is derivable;
* *reflexivity*: `s → t` is derivable whenever `t ⊆ s`;
* *augmentation*: from `s → t` derive `s ∪ u → t ∪ u`;
* *transitivity*: from `s → t` and `t → u` derive `s → u`.

All rules are finitary, hence completeness cannot hold for arbitrary sets of attributes: a
derivation only ever uses finitely many implications of `L`, whereas an implication with an
infinite premise or conclusion may need infinitely many of them. Completeness is therefore proved
under the hypothesis that all premises of `L` and the conclusion of the implication in question
are finite, which in particular holds if the attribute type is finite.

## Main definitions

* `FCA.Implication.Derivable`: derivability from a set of implications by the Armstrong rules.

## Main results

* `FCA.Implication.Derivable.entails`: soundness of the Armstrong rules.
* `FCA.Implication.Entails.derivable`: completeness of the Armstrong rules for sets of
  implications with finite premises and implications with finite conclusion.
* `FCA.Implication.derivable_iff_entails`: over a finite attribute type, derivability and
  entailment coincide.
* `FCA.Implication.Derivable.union`, `FCA.Implication.Derivable.mono_right`,
  `FCA.Implication.Derivable.pseudo_trans`: the derived rules of additivity, projectivity and
  pseudo-transitivity.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [W. W. Armstrong, *Dependency structures of data base relationships*][armstrong1974]
-/

@[expose] public section

open Set

namespace FCA

namespace Implication

variable {β : Type*} {L L' : Set (Implication β)} {i : Implication β} {s s' t t' u v : Set β}

/-- An implication is *derivable* from a set `L` of implications if it can be obtained from the
implications in `L` by the Armstrong rules: reflexivity, augmentation and transitivity. -/
inductive Derivable (L : Set (Implication β)) : Implication β → Prop
  /-- Every implication of `L` is derivable from `L`. -/
  | ax {i : Implication β} : i ∈ L → Derivable L i
  /-- Reflexivity: `s → t` is derivable whenever `t ⊆ s`. -/
  | refl {s t : Set β} : t ⊆ s → Derivable L ⟨s, t⟩
  /-- Augmentation: from `s → t` derive `s ∪ u → t ∪ u`. -/
  | augment {s t : Set β} (u : Set β) : Derivable L ⟨s, t⟩ → Derivable L ⟨s ∪ u, t ∪ u⟩
  /-- Transitivity: from `s → t` and `t → u` derive `s → u`. -/
  | trans {s t u : Set β} : Derivable L ⟨s, t⟩ → Derivable L ⟨t, u⟩ → Derivable L ⟨s, u⟩

namespace Derivable

/-! ### Soundness -/

/-- Soundness of the Armstrong rules: every derivable implication is entailed. -/
theorem entails (h : Derivable L i) : Entails L i := by
  induction h with
  | ax hi => exact entails_of_mem hi
  | refl h => exact fun _ _ hp => h.trans hp
  | augment u _ ih =>
    exact fun t ht hp =>
      union_subset (ih t ht (subset_union_left.trans hp)) (subset_union_right.trans hp)
  | trans _ _ ih₁ ih₂ => exact fun t ht hp => ih₂ t ht (ih₁ t ht hp)

/-! ### Derived rules -/

/-- Derivability is monotone in the set of implications. -/
theorem mono (h : Derivable L i) (hL : L ⊆ L') : Derivable L' i := by
  induction h with
  | ax hi => exact .ax (hL hi)
  | refl h => exact .refl h
  | augment u _ ih => exact ih.augment u
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The implication `s → s` is derivable. -/
protected theorem rfl : Derivable L ⟨s, s⟩ :=
  .refl Subset.rfl

/-- Weakening of the premise: from `s → t` derive `s' → t` for `s ⊆ s'`. -/
theorem mono_left (h : Derivable L ⟨s, t⟩) (hs : s ⊆ s') : Derivable L ⟨s', t⟩ :=
  (refl hs).trans h

/-- Projectivity (decomposition): from `s → t` derive `s → t'` for `t' ⊆ t`. -/
theorem mono_right (h : Derivable L ⟨s, t⟩) (ht : t' ⊆ t) : Derivable L ⟨s, t'⟩ :=
  h.trans (refl ht)

/-- Additivity (union): from `s → t` and `s → u` derive `s → t ∪ u`. -/
theorem union (ht : Derivable L ⟨s, t⟩) (hu : Derivable L ⟨s, u⟩) : Derivable L ⟨s, t ∪ u⟩ :=
  have h₁ : Derivable L ⟨s, t ∪ s⟩ := (ht.augment s).mono_left (union_self s).subset
  have h₂ : Derivable L ⟨t ∪ s, t ∪ u⟩ :=
    ((hu.augment t).mono_left (union_comm s t).subset).mono_right (union_comm t u).subset
  h₁.trans h₂

/-- Decomposition: from `s → t ∪ u` derive `s → t`. -/
theorem of_union_left (h : Derivable L ⟨s, t ∪ u⟩) : Derivable L ⟨s, t⟩ :=
  h.mono_right subset_union_left

/-- Decomposition: from `s → t ∪ u` derive `s → u`. -/
theorem of_union_right (h : Derivable L ⟨s, t ∪ u⟩) : Derivable L ⟨s, u⟩ :=
  h.mono_right subset_union_right

/-- `s → t ∪ u` is derivable iff both `s → t` and `s → u` are. -/
theorem union_iff : Derivable L ⟨s, t ∪ u⟩ ↔ Derivable L ⟨s, t⟩ ∧ Derivable L ⟨s, u⟩ :=
  ⟨fun h => ⟨h.of_union_left, h.of_union_right⟩, fun h => h.1.union h.2⟩

/-- Pseudo-transitivity: from `s → t` and `t ∪ u → v` derive `s ∪ u → v`. -/
theorem pseudo_trans (h₁ : Derivable L ⟨s, t⟩) (h₂ : Derivable L ⟨t ∪ u, v⟩) :
    Derivable L ⟨s ∪ u, v⟩ :=
  (h₁.augment u).trans h₂

/-- Composition: from `s → t` and `u → v` derive `s ∪ u → t ∪ v`. -/
theorem union_union (h₁ : Derivable L ⟨s, t⟩) (h₂ : Derivable L ⟨u, v⟩) :
    Derivable L ⟨s ∪ u, t ∪ v⟩ :=
  (h₁.mono_left subset_union_left).union (h₂.mono_left subset_union_right)

/-- Accumulation: from `s → t` derive `s → s ∪ t`. -/
theorem union_self_left (h : Derivable L ⟨s, t⟩) : Derivable L ⟨s, s ∪ t⟩ :=
  Derivable.rfl.union h

/-- Finite additivity: if `t` is finite and `s → {b}` is derivable for all `b ∈ t`, then `s → t`
is derivable. -/
theorem of_forall_singleton (ht : t.Finite) (h : ∀ b ∈ t, Derivable L ⟨s, {b}⟩) :
    Derivable L ⟨s, t⟩ := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact .refl (empty_subset s)
  | @insert b t _ _ ih =>
    exact ((h b (mem_insert b t)).union (ih fun c hc => h c (mem_insert_of_mem b hc))).mono_right
      (singleton_union (a := b) (s := t)).ge

/-- For a finite conclusion `t`, the implication `s → t` is derivable iff `s → {b}` is derivable
for all `b ∈ t`. -/
theorem iff_forall_singleton (ht : t.Finite) :
    Derivable L ⟨s, t⟩ ↔ ∀ b ∈ t, Derivable L ⟨s, {b}⟩ :=
  ⟨fun h _ hb => h.mono_right (singleton_subset_iff.2 hb), of_forall_singleton ht⟩

end Derivable

/-! ### Completeness -/

/-- The set of attributes `b` such that `s → {b}` is derivable from `L` is a model of `L`,
provided that all premises of `L` are finite. -/
theorem isModel_setOf_derivable_singleton (hL : ∀ j ∈ L, j.premise.Finite) (s : Set β) :
    IsModel L {b | Derivable L ⟨s, {b}⟩} := fun j hj hp _ hb =>
  ((Derivable.of_forall_singleton (hL j hj) fun _ hc => hp hc).trans (.ax hj)).mono_right
    (singleton_subset_iff.2 hb)

/-- Completeness of the Armstrong rules: if all premises of `L` are finite, every implication with
finite conclusion entailed by `L` is derivable from `L`. -/
theorem Entails.derivable (h : Entails L i) (hL : ∀ j ∈ L, j.premise.Finite)
    (hi : i.conclusion.Finite) : Derivable L i :=
  Derivable.of_forall_singleton hi <|
    h _ (isModel_setOf_derivable_singleton hL i.premise) fun _ hb =>
      .refl (singleton_subset_iff.2 hb)

/-- If all premises of `L` are finite, an implication with finite conclusion is derivable from
`L` iff it is entailed by `L`. -/
theorem derivable_iff_entails_of_finite (hL : ∀ j ∈ L, j.premise.Finite)
    (hi : i.conclusion.Finite) : Derivable L i ↔ Entails L i :=
  ⟨Derivable.entails, fun h => h.derivable hL hi⟩

/-- Soundness and completeness of the Armstrong rules over a finite attribute type: an implication
is derivable from `L` iff it is entailed by `L`. -/
theorem derivable_iff_entails [Finite β] : Derivable L i ↔ Entails L i :=
  derivable_iff_entails_of_finite (fun _ _ => toFinite _) (toFinite _)

/-- Over a finite attribute type, `s → t` is derivable from `L` iff `t` is contained in the
`L`-closure of `s`. -/
theorem derivable_iff_subset_closure [Finite β] :
    Derivable L i ↔ i.conclusion ⊆ closure L i.premise :=
  derivable_iff_entails.trans entails_iff

/-- Over a finite attribute type, the implications derivable from a sound and complete set of
implications of a formal context are exactly the implications holding in the context. -/
theorem derivable_iff_holds [Finite β] {α : Type*} {r : α → β → Prop} (hs : IsSound r L)
    (hc : IsComplete r L) : Derivable L i ↔ Holds r i :=
  derivable_iff_entails.trans (entails_iff_holds hs hc)

end Implication

end FCA
