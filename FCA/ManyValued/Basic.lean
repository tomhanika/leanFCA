/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Implication.Basic

/-!
# Many-valued contexts and plain conceptual scaling

A *many-valued context* `(G, M, W, I)` assigns to an object `g` and a many-valued attribute `m` at
most one value `m(g) ∈ W`. In *conceptual scaling* every many-valued attribute `m` is interpreted
by a *scale*, a formal context whose objects are the values of `m`; *plain scaling* combines these
into an ordinary (one-valued) formal context, the *derived context*.

## Design

In the same spirit in which a formal context is a bare relation `r : α → β → Prop` throughout this
library, a many-valued context with objects `α`, many-valued attributes `M` and values `W m` of
the attribute `m` is a bare dependent function

`v : α → (m : M) → W m`.

* The value type depends on the attribute, which is how many-valued data is typed in practice and
  which makes a single untyped value set `W` (take `W` constant) a special case.
* The function is total, i.e. the many-valued context is *complete*. Partial many-valued contexts
  need no separate notion: use `Option (V m)` as value type and lift the scales along
  `FCA.optionScale`, under which a missing value has no scale attribute.
* A scale for the attribute `m` is a relation `s m : W m → S m → Prop`, e.g. one of the standard
  scales of `FCA.Scale.Standard`. Unlike Ganter and Wille we do not require the scale objects to
  form a superset of the values taken by `m`; they are exactly the values of type `W m`.

## Main definitions

* `FCA.plainScaling v s`: the derived one-valued context with attribute type `Σ m, S m`.
* `FCA.optionScale s`: the lift of a scale to optional values.
* `FCA.FunDep v X Y`: the functional dependency `X → Y` between sets of many-valued attributes.
* `FCA.agreement v`: the context on pairs of objects in which a pair has the attribute `m` iff
  the two objects agree on `m`.

## Main results

* `FCA.funDep_iff_exists_function`: a functional dependency holds iff the dependent values are
  a function of the determining values.
* `FCA.lowerPolar_plainScaling`, `FCA.upperPolar_plainScaling`: the derivation operators of the
  derived context in terms of those of the scales.
* `FCA.isExtent_plainScaling_iff`: the extents of the derived context are the intersections of
  preimages of scale extents.
* `FCA.funDep_iff_holds_agreement`: a functional dependency holds iff the corresponding
  implication holds in the agreement context.

## References

* [B. Ganter, R. Wille, *Formal Concept Analysis: Mathematical Foundations*][ganter1999]
-/

@[expose] public section

open Set Order

namespace FCA

variable {α M : Type*} {W S : M → Type*}

/-! ### Plain scaling -/

section PlainScaling

variable {v : α → (m : M) → W m} {s : (m : M) → W m → S m → Prop}

/-- The context derived from the many-valued context `v` by *plain scaling* with the scales `s`:
its attributes are the pairs `⟨m, n⟩` of a many-valued attribute `m` and a scale attribute `n` of
`s m`, and an object `a` has the attribute `⟨m, n⟩` iff its value `v a m` has the scale attribute
`n`. -/
def plainScaling (v : α → (m : M) → W m) (s : (m : M) → W m → S m → Prop) :
    α → (Σ m, S m) → Prop :=
  fun a n => s n.1 (v a n.1) n.2

@[simp]
theorem plainScaling_mk {a : α} {m : M} {n : S m} : plainScaling v s a ⟨m, n⟩ ↔ s m (v a m) n :=
  Iff.rfl

instance [∀ m, DecidableRel (s m)] : DecidableRel (plainScaling v s) :=
  fun _ n => inferInstanceAs (Decidable (s n.1 _ n.2))

theorem mem_lowerPolar_plainScaling {t : Set (Σ m, S m)} {a : α} :
    a ∈ lowerPolar (plainScaling v s) t ↔
      ∀ m, v a m ∈ lowerPolar (s m) (Sigma.mk m ⁻¹' t) :=
  ⟨fun h _ _ hn => h hn, fun h n hn => h n.1 hn⟩

/-- The objects of the derived context sharing a set `t` of attributes are those whose value
under each many-valued attribute `m` has all scale attributes that `t` selects for `m`. -/
theorem lowerPolar_plainScaling (v : α → (m : M) → W m) (s : (m : M) → W m → S m → Prop)
    (t : Set (Σ m, S m)) :
    lowerPolar (plainScaling v s) t =
      ⋂ m, (v · m) ⁻¹' lowerPolar (s m) (Sigma.mk m ⁻¹' t) := by
  ext a
  simp [mem_lowerPolar_plainScaling]

theorem mem_upperPolar_plainScaling {A : Set α} {n : Σ m, S m} :
    n ∈ upperPolar (plainScaling v s) A ↔ n.2 ∈ upperPolar (s n.1) ((v · n.1) '' A) :=
  ⟨fun h _ ⟨_, ha, hw⟩ => hw ▸ h ha, fun h _ ha => h (mem_image_of_mem (v · n.1) ha)⟩

/-- The attributes of the derived context common to a set `A` of objects are, for each
many-valued attribute `m`, the scale attributes common to the values of `m` on `A`. -/
theorem upperPolar_plainScaling (v : α → (m : M) → W m) (s : (m : M) → W m → S m → Prop)
    (A : Set α) :
    upperPolar (plainScaling v s) A =
      ⋃ m, Sigma.mk m '' upperPolar (s m) ((v · m) '' A) := by
  ext ⟨m, n⟩
  rw [mem_iUnion]
  constructor
  · exact fun h => ⟨m, n, mem_upperPolar_plainScaling.1 h, rfl⟩
  · rintro ⟨_, _, h, ⟨⟩⟩
    exact mem_upperPolar_plainScaling.2 h

theorem preimage_mk_upperPolar_plainScaling (v : α → (m : M) → W m)
    (s : (m : M) → W m → S m → Prop) (A : Set α) (m : M) :
    Sigma.mk m ⁻¹' upperPolar (plainScaling v s) A = upperPolar (s m) ((v · m) '' A) := by
  ext n
  exact mem_upperPolar_plainScaling

/-- The preimage of a scale extent under a many-valued attribute is the extent of the
corresponding attributes of the derived context. -/
theorem preimage_lowerPolar_eq_lowerPolar_plainScaling (v : α → (m : M) → W m)
    (s : (m : M) → W m → S m → Prop) (m : M) (u : Set (S m)) :
    (v · m) ⁻¹' lowerPolar (s m) u = lowerPolar (plainScaling v s) (Sigma.mk m '' u) := by
  ext a
  exact ⟨fun h _ ⟨_, hn, hn'⟩ => hn' ▸ h hn, fun h _ hn => h (mem_image_of_mem (Sigma.mk m) hn)⟩

/-- The preimage of a scale extent under a many-valued attribute is an extent of the derived
context. -/
theorem isExtent_preimage_plainScaling (v : α → (m : M) → W m) {m : M} {E : Set (W m)}
    (hE : IsExtent (s m) E) : IsExtent (plainScaling v s) ((v · m) ⁻¹' E) := by
  obtain ⟨u, rfl⟩ := hE
  exact ⟨_, (preimage_lowerPolar_eq_lowerPolar_plainScaling v s m u).symm⟩

/-- The extents of the context derived by plain scaling are precisely the intersections of
preimages of scale extents, one for each many-valued attribute. -/
theorem isExtent_plainScaling_iff {A : Set α} :
    IsExtent (plainScaling v s) A ↔
      ∃ E : (m : M) → Set (W m), (∀ m, IsExtent (s m) (E m)) ∧ A = ⋂ m, (v · m) ⁻¹' E m := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fun m => lowerPolar (s m) (Sigma.mk m ⁻¹' t), fun m => isExtent_lowerPolar,
      lowerPolar_plainScaling v s t⟩
  · rintro ⟨E, hE, rfl⟩
    exact IsExtent.iInter _ fun m => isExtent_preimage_plainScaling v (hE m)

/-- An object `a` lies in the extent closure of a set `A` of objects of the derived context iff
for every many-valued attribute `m` the value of `a` lies in the scale extent generated by the
values of `A`. -/
theorem mem_extentClosure_plainScaling {A : Set α} {a : α} :
    a ∈ lowerPolar (plainScaling v s) (upperPolar (plainScaling v s) A) ↔
      ∀ m, v a m ∈ lowerPolar (s m) (upperPolar (s m) ((v · m) '' A)) := by
  simp_rw [mem_lowerPolar_plainScaling, preimage_mk_upperPolar_plainScaling]

end PlainScaling

/-! ### Missing values -/

section Option

variable {V T : Type*} {s : V → T → Prop}

/-- The lift of a scale `s` to optional values: a missing value has no scale attribute. Scaling a
partial many-valued context `v : α → (m : M) → Option (V m)` with the scales
`fun m => optionScale (s m)` is plain scaling in the sense of Ganter and Wille, where an object
without a value for `m` has no attribute of the form `⟨m, n⟩`. -/
def optionScale (s : V → T → Prop) (o : Option V) (n : T) : Prop :=
  ∃ w ∈ o, s w n

@[simp]
theorem optionScale_some {w : V} {n : T} : optionScale s (some w) n ↔ s w n := by
  simp [optionScale]

@[simp]
theorem not_optionScale_none {n : T} : ¬optionScale s none n := by
  simp [optionScale]

instance [DecidableRel s] : DecidableRel (optionScale s)
  | none, _ => isFalse not_optionScale_none
  | some _, _ => decidable_of_iff _ optionScale_some.symm

theorem mem_lowerPolar_optionScale_some {t : Set T} {w : V} :
    some w ∈ lowerPolar (optionScale s) t ↔ w ∈ lowerPolar s t := by
  simp [mem_lowerPolar_iff]

theorem none_mem_lowerPolar_optionScale {t : Set T} :
    none ∈ lowerPolar (optionScale s) t ↔ t = ∅ := by
  simp [mem_lowerPolar_iff, eq_empty_iff_forall_notMem]

/-- The objects of a lifted scale having a nonempty set of attributes are the values of the
original scale having these attributes. -/
theorem lowerPolar_optionScale_of_nonempty {t : Set T} (ht : t.Nonempty) :
    lowerPolar (optionScale s) t = some '' lowerPolar s t := by
  ext (_ | w)
  · simpa [none_mem_lowerPolar_optionScale] using ht.ne_empty
  · simp [mem_lowerPolar_optionScale_some]

end Option

/-! ### Functional dependencies -/

section FunDep

variable {v : α → (m : M) → W m} {X Y Z : Set M}

/-- The *functional dependency* `X → Y` holds in the many-valued context `v` if any two objects
that agree on all attributes in `X` also agree on all attributes in `Y`. -/
def FunDep (v : α → (m : M) → W m) (X Y : Set M) : Prop :=
  ∀ a b, (∀ m ∈ X, v a m = v b m) → ∀ m ∈ Y, v a m = v b m

/-- The *agreement context* of a many-valued context: its objects are the pairs of objects, and a
pair has the attribute `m` iff both objects have the same value under `m`. -/
def agreement (v : α → (m : M) → W m) (p : α × α) (m : M) : Prop :=
  v p.1 m = v p.2 m

instance [∀ m, DecidableEq (W m)] : DecidableRel (agreement v) :=
  fun p m => inferInstanceAs (Decidable (v p.1 m = v p.2 m))

theorem mem_lowerPolar_agreement {p : α × α} :
    p ∈ lowerPolar (agreement v) X ↔ ∀ m ∈ X, v p.1 m = v p.2 m :=
  Iff.rfl

/-- The pairs of the form `(a, a)` have all attributes of the agreement context. -/
theorem agreement_self (v : α → (m : M) → W m) (a : α) (m : M) : agreement v (a, a) m :=
  rfl

/-- A functional dependency holds in a many-valued context iff the corresponding implication
holds in the agreement context. -/
theorem funDep_iff_holds_agreement : FunDep v X Y ↔ Implication.Holds (agreement v) ⟨X, Y⟩ := by
  rw [Implication.holds_iff_lowerPolar_subset]
  exact ⟨fun h p hp => h p.1 p.2 hp, fun h a b hab => h (a := (a, b)) hab⟩

/-- A functional dependency `X → Y` holds iff `Y` is contained in the intent closure of `X` in
the agreement context. -/
theorem funDep_iff_subset_closure :
    FunDep v X Y ↔ Y ⊆ upperPolar (agreement v) (lowerPolar (agreement v) X) :=
  funDep_iff_holds_agreement.trans Implication.holds_iff_subset_closure

theorem funDep_of_subset (v : α → (m : M) → W m) (h : Y ⊆ X) : FunDep v X Y :=
  fun _ _ hX m hm => hX m (h hm)

theorem FunDep.trans (h₁ : FunDep v X Y) (h₂ : FunDep v Y Z) : FunDep v X Z :=
  fun a b hX => h₂ a b (h₁ a b hX)

theorem FunDep.union (h₁ : FunDep v X Y) (h₂ : FunDep v X Z) : FunDep v X (Y ∪ Z) :=
  fun a b hX m hm => hm.elim (h₁ a b hX m) (h₂ a b hX m)

theorem FunDep.mono_left {X' : Set M} (h : FunDep v X Y) (hX : X ⊆ X') : FunDep v X' Y :=
  fun a b hX' => h a b fun m hm => hX' m (hX hm)

theorem FunDep.mono_right {Y' : Set M} (h : FunDep v X Y) (hY : Y' ⊆ Y) : FunDep v X Y' :=
  fun a b hX m hm => h a b hX m (hY hm)

/-- The functional dependency `X → Y` holds iff the values of the attributes in `Y` are a function
of the values of the attributes in `X`. -/
theorem funDep_iff_exists_function [Nonempty α] :
    FunDep v X Y ↔
      ∃ f : ((m : X) → W m) → (m : Y) → W m, ∀ a, f (fun m => v a m) = fun m : Y => v a m := by
  classical
  constructor
  · intro h
    refine ⟨fun x => if hx : ∃ a, (fun m : X => v a m) = x then fun m => v hx.choose m
      else fun m => v (Classical.arbitrary α) m, fun a => ?_⟩
    have hx : ∃ b, (fun m : X => v b m) = fun m : X => v a m := ⟨a, rfl⟩
    dsimp only
    rw [dite_eq_left_of_eq_true (eq_true hx)]
    exact funext fun m => h _ _ (fun n hn => congrFun hx.choose_spec ⟨n, hn⟩) m m.2
  · rintro ⟨f, hf⟩ a b hX m hm
    have hab : (fun m : X => v a m) = fun m : X => v b m := funext fun m => hX m m.2
    have h := hf a
    rw [hab, hf b] at h
    exact (congrFun h ⟨m, hm⟩).symm

end FunDep

end FCA
