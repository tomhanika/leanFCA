/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.CanonicalBase

/-!
# Minimality of the canonical base

The canonical (Duquenne–Guigues) base of a formal context with finitely many attributes is
*non-redundant*: no implication of it is entailed by the others. Moreover it has *minimum
cardinality* among all sound and complete sets of implications of the context: every such set
contains, for each pseudo-intent `p`, an implication whose premise `s` satisfies `s ⊆ p` and
`s'' ⊈ p`, and distinct pseudo-intents need distinct implications.

Soundness cannot be dropped in the second statement: `{∅ → univ}` is complete (in the sense of
`FCA.Implication.IsComplete`) for every context.

## Main results

* `FCA.isIntent_inter_of_not_subset`: the intersection of two incomparable sets, each of which is
  an intent or a pseudo-intent, is an intent.
* `FCA.not_entails_canonicalBase_diff_singleton`: no implication of the canonical base is entailed
  by the remaining ones.
* `FCA.not_isComplete_of_ssubset_canonicalBase`: no proper subset of the canonical base is
  complete.
* `FCA.IsPseudoIntent.exists_mem_of_isSound_of_isComplete`: a sound and complete set of
  implications contains, for each pseudo-intent `p`, an implication with premise `s ⊆ p` such that
  `s'' ⊈ p`.
* `FCA.exists_injective_of_isSound_of_isComplete`: the pseudo-intents inject into every sound and
  complete set of implications.
* `FCA.encard_canonicalBase_le`, `FCA.ncard_canonicalBase_le`: the canonical base has at most as
  many elements as any sound and complete set of implications.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
* [J.-L. Guigues, V. Duquenne, *Familles minimales d'implications informatives résultant d'un
  tableau de données binaires*][guigues1986]
-/

@[expose] public section

open Set Order Function

namespace FCA

variable {α β : Type*} {r : α → β → Prop} {p q s : Set β} {L : Set (Implication β)}
  {i : Implication β}

instance Implication.instFinite [Finite β] : Finite (Implication β) :=
  Finite.of_injective (fun i : Implication β => (i.premise, i.conclusion)) fun _ _ h =>
    Implication.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Completeness is preserved when enlarging a set of implications. -/
theorem Implication.IsComplete.mono {L' : Set (Implication β)} (h : Implication.IsComplete r L)
    (hL : L ⊆ L') : Implication.IsComplete r L' :=
  fun i hi => (h i hi).mono hL

variable [Finite β]

/-! ### Intersections of pseudo-intents -/

/-- A set which is an intent or a pseudo-intent contains the closure of every pseudo-intent
properly contained in it. -/
theorem upperPolar_lowerPolar_subset_of_ssubset (hp : IsIntent r p ∨ IsPseudoIntent r p)
    (hq : IsPseudoIntent r q) (hqp : q ⊂ p) : upperPolar r (lowerPolar r q) ⊆ p :=
  hp.elim (fun h => h.upperPolar_lowerPolar_subset hqp.subset) fun h => h.closure_subset hqp hq

/-- If each of `p` and `q` is an intent or a pseudo-intent, and neither is contained in the other,
then `p ∩ q` is an intent. -/
theorem isIntent_inter_of_not_subset (hp : IsIntent r p ∨ IsPseudoIntent r p)
    (hq : IsIntent r q ∨ IsPseudoIntent r q) (hpq : ¬p ⊆ q) (hqp : ¬q ⊆ p) :
    IsIntent r (p ∩ q) := by
  refine isIntent_of_isModel_canonicalBase fun i hi hsub => ?_
  obtain ⟨hi, hc⟩ := hi
  rw [hc]
  have h₁ : i.premise ⊂ p := (hsub.trans inter_subset_left).ssubset_of_ne fun h =>
    hpq (h ▸ hsub.trans inter_subset_right)
  have h₂ : i.premise ⊂ q := (hsub.trans inter_subset_right).ssubset_of_ne fun h =>
    hqp (h ▸ hsub.trans inter_subset_left)
  exact subset_inter (upperPolar_lowerPolar_subset_of_ssubset hp hi h₁)
    (upperPolar_lowerPolar_subset_of_ssubset hq hi h₂)

/-- The intersection of two incomparable pseudo-intents is an intent. -/
theorem IsPseudoIntent.isIntent_inter (hp : IsPseudoIntent r p) (hq : IsPseudoIntent r q)
    (hpq : ¬p ⊆ q) (hqp : ¬q ⊆ p) : IsIntent r (p ∩ q) :=
  isIntent_inter_of_not_subset (.inr hp) (.inr hq) hpq hqp

/-- If `s` is a subset of a pseudo-intent `p` whose closure `s''` is not contained in `p`, then
`s` and `p` have the same closure. -/
theorem IsPseudoIntent.upperPolar_lowerPolar_eq (hp : IsPseudoIntent r p) (hsp : s ⊆ p)
    (hs : ¬upperPolar r (lowerPolar r s) ⊆ p) :
    upperPolar r (lowerPolar r s) = upperPolar r (lowerPolar r p) := by
  refine (upperPolar_anti r (lowerPolar_anti r hsp)).antisymm
    (isIntent_upperPolar.upperPolar_lowerPolar_subset ?_)
  by_contra hps
  exact hs (((isIntent_inter_of_not_subset (.inr hp) (.inl isIntent_upperPolar) hps
    hs).upperPolar_lowerPolar_subset
      (subset_inter hsp (subset_upperPolar_lowerPolar r s))).trans inter_subset_left)

/-- Two pseudo-intents `p` and `q` which have a common subset `s` whose closure `s''` is contained
in neither `p` nor `q` are equal. -/
theorem IsPseudoIntent.eq_of_subset_of_not_subset (hp : IsPseudoIntent r p)
    (hq : IsPseudoIntent r q) (hsp : s ⊆ p) (hsq : s ⊆ q)
    (hp' : ¬upperPolar r (lowerPolar r s) ⊆ p) (hq' : ¬upperPolar r (lowerPolar r s) ⊆ q) :
    p = q := by
  by_contra hne
  by_cases hpq : p ⊆ q
  · exact hq' ((upperPolar_anti r (lowerPolar_anti r hsp)).trans
      (hq.closure_subset (hpq.ssubset_of_ne hne) hp))
  by_cases hqp : q ⊆ p
  · exact hp' ((upperPolar_anti r (lowerPolar_anti r hsq)).trans
      (hp.closure_subset (hqp.ssubset_of_ne (Ne.symm hne)) hq))
  · exact hp' (((hp.isIntent_inter hq hpq hqp).upperPolar_lowerPolar_subset
      (subset_inter hsp hsq)).trans inter_subset_left)

/-! ### Non-redundancy -/

/-- A pseudo-intent `p` is a model of the canonical base without the implication `p → p''`. -/
theorem IsPseudoIntent.isModel_canonicalBase_diff_singleton (hp : IsPseudoIntent r p) :
    Implication.IsModel (canonicalBase r \ {⟨p, upperPolar r (lowerPolar r p)⟩}) p := by
  rintro j ⟨⟨hj, hc⟩, hne⟩ hsub
  rw [hc]
  refine hp.closure_subset (hsub.ssubset_of_ne fun heq => hne ?_) hj
  exact mem_singleton_iff.2 (Implication.ext heq (hc.trans (by rw [heq])))

/-- The canonical base is non-redundant: none of its implications is entailed by the others. -/
theorem not_entails_canonicalBase_diff_singleton (hi : i ∈ canonicalBase r) :
    ¬Implication.Entails (canonicalBase r \ {i}) i := by
  obtain ⟨p, c⟩ := i
  obtain ⟨hp, hc⟩ := hi
  dsimp only at hp hc
  subst hc
  intro h
  have hsub := h p hp.isModel_canonicalBase_diff_singleton Subset.rfl
  exact hp.not_isIntent (isIntent_iff.2 (hsub.antisymm (subset_upperPolar_lowerPolar r p)))

/-- Removing an implication from the canonical base destroys completeness. -/
theorem not_isComplete_canonicalBase_diff_singleton (hi : i ∈ canonicalBase r) :
    ¬Implication.IsComplete r (canonicalBase r \ {i}) :=
  fun h => not_entails_canonicalBase_diff_singleton hi (h i (isSound_canonicalBase r i hi))

/-- No proper subset of the canonical base is complete. -/
theorem not_isComplete_of_ssubset_canonicalBase (hL : L ⊂ canonicalBase r) :
    ¬Implication.IsComplete r L := by
  obtain ⟨i, hi, hiL⟩ := exists_of_ssubset hL
  exact fun h => not_isComplete_canonicalBase_diff_singleton hi
    (h.mono (subset_sdiff_singleton hL.subset hiL))

/-! ### Minimum cardinality -/

/-- A sound and complete set of implications contains, for every pseudo-intent `p`, an implication
whose premise `s` is contained in `p` while its closure `s''` is not. -/
theorem IsPseudoIntent.exists_mem_of_isSound_of_isComplete (hp : IsPseudoIntent r p)
    (hs : Implication.IsSound r L) (hc : Implication.IsComplete r L) :
    ∃ i ∈ L, i.premise ⊆ p ∧ ¬upperPolar r (lowerPolar r i.premise) ⊆ p := by
  by_contra hcon
  refine hp.not_isIntent (Implication.isComplete_iff.1 hc p fun i hi hsub => ?_)
  by_contra hi'
  exact hcon ⟨i, hi, hsub, fun h =>
    hi' ((Implication.holds_iff_subset_closure.1 (hs i hi)).trans h)⟩

/-- A sound and complete set of implications contains, for every pseudo-intent `p`, an implication
whose premise is contained in `p` and has the same closure as `p`. -/
theorem IsPseudoIntent.exists_mem_upperPolar_lowerPolar_eq (hp : IsPseudoIntent r p)
    (hs : Implication.IsSound r L) (hc : Implication.IsComplete r L) :
    ∃ i ∈ L, i.premise ⊆ p ∧
      upperPolar r (lowerPolar r i.premise) = upperPolar r (lowerPolar r p) :=
  let ⟨i, hi, hsub, hnot⟩ := hp.exists_mem_of_isSound_of_isComplete hs hc
  ⟨i, hi, hsub, hp.upperPolar_lowerPolar_eq hsub hnot⟩

/-- The pseudo-intents of a context inject into every sound and complete set of implications. -/
theorem exists_injective_of_isSound_of_isComplete (hs : Implication.IsSound r L)
    (hc : Implication.IsComplete r L) : ∃ f : {p // IsPseudoIntent r p} → L, Injective f := by
  choose f hfL hfsub hfnot using fun p : {p // IsPseudoIntent r p} =>
    p.2.exists_mem_of_isSound_of_isComplete hs hc
  refine ⟨fun p => ⟨f p, hfL p⟩, fun p q h => Subtype.ext ?_⟩
  have h' : f p = f q := congrArg Subtype.val h
  refine p.2.eq_of_subset_of_not_subset q.2 (hfsub p) ?_ (hfnot p) ?_
  · rw [h']
    exact hfsub q
  · rw [h']
    exact hfnot q

/-- The canonical base injects into every sound and complete set of implications. -/
theorem exists_injective_canonicalBase (hs : Implication.IsSound r L)
    (hc : Implication.IsComplete r L) : ∃ f : canonicalBase r → L, Injective f := by
  obtain ⟨f, hf⟩ := exists_injective_of_isSound_of_isComplete hs hc
  refine ⟨fun i => f ⟨i.1.premise, i.2.1⟩, fun i j h => Subtype.ext ?_⟩
  have h' : i.1.premise = j.1.premise := congrArg Subtype.val (hf h)
  exact Implication.ext h' (i.2.2.trans
    ((congrArg (fun s => upperPolar r (lowerPolar r s)) h').trans j.2.2.symm))

/-- The canonical base has minimum cardinality among the sound and complete sets of
implications. -/
theorem encard_canonicalBase_le (hs : Implication.IsSound r L)
    (hc : Implication.IsComplete r L) : (canonicalBase r).encard ≤ L.encard :=
  let ⟨f, hf⟩ := exists_injective_canonicalBase hs hc
  Function.Embedding.encard_le ⟨f, hf⟩

/-- The canonical base has minimum cardinality among the sound and complete sets of
implications. -/
theorem ncard_canonicalBase_le (hs : Implication.IsSound r L)
    (hc : Implication.IsComplete r L) : (canonicalBase r).ncard ≤ L.ncard :=
  ENat.toNat_le_toNat (encard_canonicalBase_le hs hc) (toFinite L).encard_lt_top.ne

end FCA
