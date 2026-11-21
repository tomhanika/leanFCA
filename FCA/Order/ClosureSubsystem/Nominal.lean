/-
Copyright (c) 2026 Tom Hanika. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Hanika
-/
module

public import FCA.Order.ClosureSubsystem.Truncation
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Order.Setoid.Partition

/-!
# Nominal closure systems and nominal covers

A closure system is *nominal* if it consists of the whole set, the empty set and the blocks of a
partition. These are the closure systems induced by a map into a nominal scale. A closure system
has *nominal scaling dimension* at most `|ι|` if it is the join of `ι` nominal closure systems.

Under the ascending chain condition this is the case if and only if the empty set is closed and
the nonempty `⋂`-irreducible closed sets can be distributed over `ι` partitions into closed sets.
For the closure system of the vertices and edges of a graph this specialises to proper edge
colourings: partitions into closed sets are matchings.

## Main definitions

* `FCA.ClosureSubsystem.IsNominal`: the closure system consists of `univ`, `∅` and the blocks of
  a partition.
* `FCA.ClosureSubsystem.ofPartition`: the nominal closure system of a partition.
* `FCA.ClosureSubsystem.HasNominalCover 𝒜 ι`: `𝒜` is the join of `ι` nominal closure systems.
* `FCA.ClosureSubsystem.irreducibleGraph`: the graph of intersecting `⋂`-irreducible closed
  sets.
* `FCA.ClosureSubsystem.edgeSystem G`: the closure system of the whole vertex set, the sets with
  at most one vertex, and the edges of a graph `G`.

## Main results

* `FCA.ClosureSubsystem.hasNominalCover_iff`: under the ascending chain condition, `𝒜` is a join
  of `ι` nominal closure systems iff `∅ ∈ 𝒜` and there are `ι` partitions into closed sets of `𝒜`
  containing all nonempty `⋂`-irreducible closed sets of `𝒜`.
* `FCA.ClosureSubsystem.hasNominalCover_iff_coloring`,
  `FCA.ClosureSubsystem.hasNominalCover_iff_irreducibleGraph`: under the ascending chain
  condition, `𝒜` is a join of `ι` nominal closure systems iff `∅ ∈ 𝒜`, the closures of points are
  pairwise equal or disjoint, and the graph `FCA.ClosureSubsystem.irreducibleGraph` of
  intersecting `⋂`-irreducible closed sets has a colouring with colours `ι`.
* `FCA.ClosureSubsystem.hasNominalCover_set_iff`: under the ascending chain condition, `𝒜` is a
  join of nominal closure systems iff `∅ ∈ 𝒜` and the closures of points are pairwise equal or
  disjoint.
* `FCA.ClosureSubsystem.hasNominalCover_top_powerset`,
  `FCA.ClosureSubsystem.card_le_of_hasNominalCover_top_powerset`: the powerset of a finite type
  `α` with at least three elements is a join of `|α|` nominal closure systems and not of fewer.
* `FCA.ClosureSubsystem.hasNominalCover_edgeSystem_iff`: for a finite graph `G` with at least
  three vertices and at least two colours, `edgeSystem G` is a join of `ι` nominal closure systems
  iff the line graph of `G` has a colouring with colours `ι`, that is, `G` has a proper edge
  colouring with colours `ι`.

## References

* [B. Ganter, T. Hanika, J. Hirth, *Scaling Dimension*][ganter2023]
-/

@[expose] public section

open Set Function Order

namespace FCA

namespace ClosureSubsystem

variable {α ι : Type*} {p : Set α → Prop} [IsClosureSystem p] {𝒜 : ClosureSubsystem p}
  {A : Set α}

/-! ### Nominal closure systems -/

/-- Two distinct sets, each empty or a block of a partition, are disjoint. -/
theorem inter_eq_empty_of_isPartition {c : Set (Set α)} (hc : Setoid.IsPartition c)
    {A B : Set α} (hA : A ∈ insert ∅ c) (hB : B ∈ insert ∅ c) (hne : A ≠ B) : A ∩ B = ∅ := by
  rcases hA with rfl | hA
  · exact empty_inter _
  rcases hB with rfl | hB
  · exact inter_empty _
  exact eq_empty_of_forall_notMem fun x hx ↦ hne ((hc.2 x).unique ⟨hA, hx.1⟩ ⟨hB, hx.2⟩)

/-- The closure system of the whole set, the empty set and the blocks of a partition into closed
sets. -/
def ofPartition (c : Set (Set α)) (hc : Setoid.IsPartition c) (h0 : p ∅)
    (hp : ∀ B ∈ c, p B) : ClosureSubsystem p where
  carrier := insert univ (insert ∅ c)
  sInter_mem' S hS := by
    by_cases h1 : ∀ A ∈ S, A = univ
    · exact .inl (sInter_eq_univ.2 h1)
    push Not at h1
    obtain ⟨A, hA, hAu⟩ := h1
    have hA' : A ∈ insert ∅ c := (hS hA).resolve_left hAu
    by_cases h2 : ∀ B ∈ S, B = univ ∨ B = A
    · have heq : ⋂₀ S = A := Subset.antisymm (sInter_subset_of_mem hA)
        (subset_sInter fun B hB ↦ (h2 B hB).elim (fun h ↦ h ▸ subset_univ _) fun h ↦ h.ge)
      rw [heq]
      exact hS hA
    · push Not at h2
      obtain ⟨B, hB, hBu, hBA⟩ := h2
      have hB' : B ∈ insert ∅ c := (hS hB).resolve_left hBu
      have hsub : ⋂₀ S ⊆ A ∩ B := subset_inter (sInter_subset_of_mem hA) (sInter_subset_of_mem hB)
      rw [inter_eq_empty_of_isPartition hc hA' hB' (Ne.symm hBA)] at hsub
      exact .inr (.inl (subset_empty_iff.1 hsub))
  isClosed' A hA := by
    rcases hA with rfl | rfl | hA
    · exact IsClosureSystem.univ_mem
    · exact h0
    · exact hp A hA

@[simp]
theorem mem_ofPartition {c : Set (Set α)} {hc : Setoid.IsPartition c} {h0 : p ∅}
    {hp : ∀ B ∈ c, p B} : A ∈ ofPartition c hc h0 hp ↔ A = univ ∨ A = ∅ ∨ A ∈ c :=
  Iff.rfl

/-- A closure system is *nominal* if it consists of the whole set, the empty set and the blocks
of a partition. -/
def IsNominal (𝒜 : ClosureSubsystem p) : Prop :=
  ∃ c : Set (Set α), Setoid.IsPartition c ∧ 𝒜.carrier = insert univ (insert ∅ c)

theorem isNominal_ofPartition {c : Set (Set α)} (hc : Setoid.IsPartition c) (h0 : p ∅)
    (hp : ∀ B ∈ c, p B) : (ofPartition c hc h0 hp).IsNominal :=
  ⟨c, hc, rfl⟩

/-- The nominal scaling dimension of `𝒜` is at most the cardinality of `ι`: `𝒜` is the join of
`ι` nominal closure systems. -/
abbrev HasNominalCover (𝒜 : ClosureSubsystem p) (ι : Type*) : Prop :=
  HasCover IsNominal 𝒜 ι

/-! ### Partitions containing the irreducible closed sets -/

omit [IsClosureSystem p] in
/-- The whole set is never `⋂`-irreducible. -/
theorem univ_notMem_irreducibles : univ ∉ 𝒜.irreducibles := fun h ↦
  h.2 (sInter_eq_univ.2 fun _ hB ↦ univ_subset_iff.1 hB.2.subset)

/-- A join of a nonempty family of nominal closure systems contains the empty set. -/
theorem HasNominalCover.empty_mem [Nonempty ι] (h : 𝒜.HasNominalCover ι) : ∅ ∈ 𝒜 := by
  obtain ⟨f, hf, rfl⟩ := h
  obtain ⟨c, -, hcar⟩ := hf (Classical.arbitrary ι)
  refine le_def.1 (le_iSup f (Classical.arbitrary ι)) ?_
  change (∅ : Set α) ∈ (f (Classical.arbitrary ι)).carrier
  rw [hcar]
  exact .inr (.inl rfl)

/-- In a nominal cover of `𝒜` by `ι` closure systems, the nonempty `⋂`-irreducible closed sets of
`𝒜` are blocks of `ι` partitions into closed sets of `𝒜`. -/
theorem HasNominalCover.exists_partitions (h : 𝒜.HasNominalCover ι) :
    ∃ c : ι → Set (Set α), (∀ i, Setoid.IsPartition (c i)) ∧ (∀ i, ∀ B ∈ c i, B ∈ 𝒜) ∧
      ∀ A ∈ 𝒜.irreducibles, A = ∅ ∨ ∃ i, A ∈ c i := by
  obtain ⟨f, hf, rfl⟩ := h
  choose c hc hcar using hf
  refine ⟨c, hc, fun i B hB ↦ le_def.1 (le_iSup f i) ?_, fun A hA ↦ ?_⟩
  · change B ∈ (f i).carrier
    rw [hcar]
    exact .inr (.inr hB)
  · obtain ⟨i, hi⟩ := exists_mem_of_mem_irreducibles hA
    have hi' : A ∈ (f i).carrier := hi
    rw [hcar i] at hi'
    rcases hi' with rfl | rfl | hi'
    · exact (univ_notMem_irreducibles hA).elim
    · exact .inl rfl
    · exact .inr ⟨i, hi'⟩

/-- If the closed sets satisfy the ascending chain condition, `𝒜` is the join of `ι` nominal
closure systems iff the empty set is closed in `𝒜` and there are `ι` partitions into closed sets
of `𝒜` which contain all nonempty `⋂`-irreducible closed sets of `𝒜`. -/
theorem hasNominalCover_iff [IsNoetherianClosureSystem p] [Nonempty ι] :
    𝒜.HasNominalCover ι ↔ ∅ ∈ 𝒜 ∧ ∃ c : ι → Set (Set α), (∀ i, Setoid.IsPartition (c i)) ∧
      (∀ i, ∀ B ∈ c i, B ∈ 𝒜) ∧ ∀ A ∈ 𝒜.irreducibles, A = ∅ ∨ ∃ i, A ∈ c i := by
  refine ⟨fun h ↦ ⟨h.empty_mem, h.exists_partitions⟩, fun ⟨h0, c, hc, hmem, hirr⟩ ↦ ?_⟩
  refine ⟨fun i ↦ ofPartition (c i) (hc i) (𝒜.isClosed h0) fun B hB ↦ 𝒜.isClosed (hmem i B hB),
    fun i ↦ isNominal_ofPartition _ _ _, le_antisymm (iSup_le fun i ↦ le_def.2 fun A hA ↦ ?_)
      (𝒜.le_generate_irreducibles.trans (generate_le_iff.2 fun A hA _ ↦ ?_))⟩
  · rcases mem_ofPartition.1 hA with rfl | rfl | hA
    · exact 𝒜.univ_mem
    · exact h0
    · exact hmem i A hA
  · rcases hirr A hA with rfl | ⟨i, hi⟩
    · exact le_def.1 (le_iSup (fun i ↦ ofPartition (c i) (hc i) (𝒜.isClosed h0)
        fun B hB ↦ 𝒜.isClosed (hmem i B hB)) (Classical.arbitrary ι))
        (mem_ofPartition.2 (.inr (.inl rfl)))
    · exact le_def.1 (le_iSup (fun i ↦ ofPartition (c i) (hc i) (𝒜.isClosed h0)
        fun B hB ↦ 𝒜.isClosed (hmem i B hB)) i) (mem_ofPartition.2 (.inr (.inr hi)))

/-! ### Colourings of the irreducible closed sets -/

omit [IsClosureSystem p] in
/-- If the closures of points are pairwise equal or disjoint, a closed set meeting the closure of
a point contains that point. -/
theorem mem_of_mem_closure_singleton (hb : ∀ g h, h ∈ 𝒜.closure {g} → g ∈ 𝒜.closure {h})
    {B : Set α} (hB : B ∈ 𝒜) {g h : α} (hg : h ∈ 𝒜.closure {g}) (hh : h ∈ B) : g ∈ B :=
  closure_subset hB (singleton_subset_iff.2 hh) (hb g h hg)

/-- In a nominal cover, the closures of points are pairwise equal or disjoint. -/
theorem HasNominalCover.mem_closure_singleton_symm [IsNoetherianClosureSystem p]
    (h : 𝒜.HasNominalCover ι) {g h' : α} (hh : h' ∈ 𝒜.closure {g}) : g ∈ 𝒜.closure {h'} := by
  obtain ⟨c, hc, hmem, hirr⟩ := h.exists_partitions
  refine mem_sInter.2 fun B hB ↦ ?_
  obtain ⟨T, hT, -, rfl⟩ := mem_generate.1 (le_def.1 𝒜.le_generate_irreducibles hB.1)
  refine mem_sInter.2 fun C hC ↦ ?_
  have hhC : h' ∈ C := mem_sInter.1 (hB.2 rfl) C hC
  rcases hirr C (hT hC) with rfl | ⟨i, hi⟩
  · exact hhC.elim
  obtain ⟨B', ⟨hB', hgB'⟩, -⟩ := (hc i).2 g
  have hhB' : h' ∈ B' := closure_subset (hmem i B' hB') (singleton_subset_iff.2 hgB') hh
  rwa [(hc i).2 h' |>.unique ⟨hi, hhC⟩ ⟨hB', hhB'⟩]

/-- If the closed sets satisfy the ascending chain condition, `𝒜` is the join of `ι` nominal
closure systems iff the empty set is closed in `𝒜`, the closures of points are pairwise equal or
disjoint, and the `⋂`-irreducible closed sets of `𝒜` can be coloured by `ι` such that distinct
intersecting ones get different colours. -/
theorem hasNominalCover_iff_coloring [IsNoetherianClosureSystem p] [Nonempty ι] :
    𝒜.HasNominalCover ι ↔ ∅ ∈ 𝒜 ∧ (∀ g h, h ∈ 𝒜.closure {g} → g ∈ 𝒜.closure {h}) ∧
      ∃ col : Set α → ι, ∀ A ∈ 𝒜.irreducibles, ∀ B ∈ 𝒜.irreducibles, A ≠ B →
        (A ∩ B).Nonempty → col A ≠ col B := by
  classical
  constructor
  · intro h
    refine ⟨h.empty_mem, fun g h' hh ↦ h.mem_closure_singleton_symm hh, ?_⟩
    obtain ⟨c, hc, -, hirr⟩ := h.exists_partitions
    refine ⟨fun A ↦ if hA : ∃ i, A ∈ c i then hA.choose else Classical.arbitrary ι,
      fun A hA B hB hne ⟨x, hxA, hxB⟩ heq ↦ hne ?_⟩
    have hA' : ∃ i, A ∈ c i := (hirr A hA).resolve_left fun h0 ↦ by simp [h0] at hxA
    have hB' : ∃ i, B ∈ c i := (hirr B hB).resolve_left fun h0 ↦ by simp [h0] at hxB
    simp only [hA', hB', ↓reduceDIte] at heq
    have h1 := hA'.choose_spec
    have h2 := hB'.choose_spec
    rw [← heq] at h2
    exact (hc _).2 x |>.unique ⟨h1, hxA⟩ ⟨h2, hxB⟩
  · rintro ⟨h0, hb, col, hcol⟩
    refine hasNominalCover_iff.2 ⟨h0, fun i ↦ {A | A ∈ 𝒜.irreducibles ∧ A.Nonempty ∧ col A = i} ∪
      {D | ∃ g, D = 𝒜.closure {g} ∧ ∀ A ∈ 𝒜.irreducibles, col A = i → g ∉ A}, fun i ↦ ?_,
      fun i B hB ↦ ?_, fun A hA ↦ ?_⟩
    · refine ⟨?_, fun a ↦ ?_⟩
      · rintro (⟨-, hne, -⟩ | ⟨g, hg, -⟩)
        · exact hne.ne_empty rfl
        · exact notMem_empty g (hg ▸ subset_closure (mem_singleton g))
      · have huniq : ∀ b b', b ∈ ({A | A ∈ 𝒜.irreducibles ∧ A.Nonempty ∧ col A = i} ∪
            {D | ∃ g, D = 𝒜.closure {g} ∧ ∀ A ∈ 𝒜.irreducibles, col A = i → g ∉ A} :
              Set (Set α)) →
            b' ∈ ({A | A ∈ 𝒜.irreducibles ∧ A.Nonempty ∧ col A = i} ∪
            {D | ∃ g, D = 𝒜.closure {g} ∧ ∀ A ∈ 𝒜.irreducibles, col A = i → g ∉ A} :
              Set (Set α)) → a ∈ b → a ∈ b' → b = b' := by
          rintro b b' (⟨hb1, -, hb3⟩ | ⟨g, rfl, hg⟩) (⟨hb1', -, hb3'⟩ | ⟨g', rfl, hg'⟩) ha ha'
          · by_contra hne
            exact hcol b hb1 b' hb1' hne ⟨a, ha, ha'⟩ (hb3.trans hb3'.symm)
          · exact (hg' b hb1 hb3 (mem_of_mem_closure_singleton hb hb1.1 ha' ha)).elim
          · exact (hg b' hb1' hb3' (mem_of_mem_closure_singleton hb hb1'.1 ha ha')).elim
          · have key : ∀ g, a ∈ 𝒜.closure {g} → 𝒜.closure {g} = 𝒜.closure {a} := fun g hag ↦
              Subset.antisymm (closure_subset closure_mem (singleton_subset_iff.2 (hb g a hag)))
                (closure_subset closure_mem (singleton_subset_iff.2 hag))
            rw [key g ha, key g' ha']
        by_cases hex : ∃ A ∈ 𝒜.irreducibles, col A = i ∧ a ∈ A
        · obtain ⟨A, hA, hAi, haA⟩ := hex
          exact ⟨A, ⟨.inl ⟨hA, ⟨a, haA⟩, hAi⟩, haA⟩, fun b' hb' ↦
            huniq b' A hb'.1 (.inl ⟨hA, ⟨a, haA⟩, hAi⟩) hb'.2 haA⟩
        · push Not at hex
          have hmem : 𝒜.closure {a} ∈ ({A | A ∈ 𝒜.irreducibles ∧ A.Nonempty ∧ col A = i} ∪
              {D | ∃ g, D = 𝒜.closure {g} ∧ ∀ A ∈ 𝒜.irreducibles, col A = i → g ∉ A} :
                Set (Set α)) := .inr ⟨a, rfl, hex⟩
          exact ⟨𝒜.closure {a}, ⟨hmem, subset_closure (mem_singleton a)⟩, fun b' hb' ↦
            huniq b' _ hb'.1 hmem hb'.2 (subset_closure (mem_singleton a))⟩
    · rcases hB with ⟨hB, -, -⟩ | ⟨g, rfl, -⟩
      · exact hB.1
      · exact closure_mem
    · rcases A.eq_empty_or_nonempty with rfl | hne
      · exact .inl rfl
      · exact .inr ⟨col A, .inl ⟨hA, hne, rfl⟩⟩

/-- If the closed sets satisfy the ascending chain condition, `𝒜` is a join of nominal closure
systems iff the empty set is closed in `𝒜` and the closures of points are pairwise equal or
disjoint. -/
theorem hasNominalCover_set_iff [IsNoetherianClosureSystem p] :
    𝒜.HasNominalCover (Set α) ↔
      ∅ ∈ 𝒜 ∧ ∀ g h, h ∈ 𝒜.closure {g} → g ∈ 𝒜.closure {h} :=
  ⟨fun h ↦ ⟨(hasNominalCover_iff_coloring.1 h).1, (hasNominalCover_iff_coloring.1 h).2.1⟩,
    fun h ↦ hasNominalCover_iff_coloring.2 ⟨h.1, h.2, id, fun _ _ _ _ hne _ ↦ hne⟩⟩

/-- The graph on the `⋂`-irreducible closed sets of `𝒜` in which two distinct sets are adjacent
iff they intersect. -/
def irreducibleGraph (𝒜 : ClosureSubsystem p) : SimpleGraph 𝒜.irreducibles where
  Adj A B := A ≠ B ∧ ((A : Set α) ∩ B).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, inter_comm _ _ ▸ h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- If the closed sets satisfy the ascending chain condition, `𝒜` is the join of `ι` nominal
closure systems iff the empty set is closed in `𝒜`, the closures of points are pairwise equal or
disjoint, and the graph of intersecting `⋂`-irreducible closed sets has a colouring with colours
`ι`. -/
theorem hasNominalCover_iff_irreducibleGraph [IsNoetherianClosureSystem p] [Nonempty ι] :
    𝒜.HasNominalCover ι ↔ ∅ ∈ 𝒜 ∧ (∀ g h, h ∈ 𝒜.closure {g} → g ∈ 𝒜.closure {h}) ∧
      Nonempty (𝒜.irreducibleGraph.Coloring ι) := by
  classical
  rw [hasNominalCover_iff_coloring]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun ⟨col, hcol⟩ ↦ ?_, fun ⟨C⟩ ↦ ?_⟩
  · exact ⟨SimpleGraph.Coloring.mk (fun A ↦ col A) fun {A B} hAB ↦
      hcol A A.2 B B.2 (fun h ↦ hAB.1 (Subtype.ext h)) hAB.2⟩
  · refine ⟨fun A ↦ if hA : A ∈ 𝒜.irreducibles then C ⟨A, hA⟩ else Classical.arbitrary ι,
      fun A hA B hB hne hAB ↦ ?_⟩
    simp only [hA, hB, ↓reduceDIte]
    exact C.valid (v := ⟨A, hA⟩) (w := ⟨B, hB⟩) ⟨fun h ↦ hne (congrArg Subtype.val h), hAB⟩

/-! ### The powerset -/


/-- In a finite type with more than two elements, any two elements miss a third one. -/
theorem exists_ne_ne_of_two_lt_card [Fintype α] (h : 2 < Fintype.card α) (a b : α) :
    ∃ x, x ≠ a ∧ x ≠ b := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset α) ⊆ {a, b} := fun x _ ↦ by
    by_cases hx : x = a
    · simp [hx]
    · simp [hne x hx]
  have hcard := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ] at hcard
  omega

/-- A singleton and its complement form a partition of a nontrivial type. -/
theorem isPartition_singleton_compl [Nontrivial α] (a : α) :
    Setoid.IsPartition ({{a}, {a}ᶜ} : Set (Set α)) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · exact singleton_ne_empty a h.symm
    · obtain ⟨b, hb⟩ := exists_ne a
      have hmem : b ∈ ({a}ᶜ : Set α) := hb
      rw [← h] at hmem
      exact hmem
  · by_cases hx : x = a
    · refine ⟨{a}, ⟨by simp, hx⟩, ?_⟩
      rintro B ⟨hB, hxB⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hB
      rcases hB with rfl | rfl
      · rfl
      · exact absurd hx hxB
    · refine ⟨{a}ᶜ, ⟨by simp, hx⟩, ?_⟩
      rintro B ⟨hB, hxB⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hB
      rcases hB with rfl | rfl
      · exact absurd hxB hx
      · rfl

/-- The powerset of a finite nontrivial type `α` is the join of `|α|` nominal closure
systems. -/
theorem hasNominalCover_top_powerset [Finite α] [Nontrivial α] :
    (⊤ : ClosureSubsystem fun _ : Set α ↦ True).HasNominalCover α := by
  refine hasNominalCover_iff.2 ⟨mem_top.2 True.intro, fun a ↦ {{a}, {a}ᶜ},
    isPartition_singleton_compl, fun _ _ _ ↦ mem_top.2 True.intro, fun A hA ↦ ?_⟩
  rw [irreducibles_top_powerset] at hA
  obtain ⟨a, rfl⟩ := hA
  exact .inr ⟨a, by simp⟩

/-- A cover of the powerset of a finite type `α` with more than two elements by nominal closure
systems needs at least `|α|` of them: two complements of singletons are never blocks of the same
partition. -/
theorem card_le_of_hasNominalCover_top_powerset [Fintype α] [Fintype ι]
    (h3 : 2 < Fintype.card α)
    (h : (⊤ : ClosureSubsystem fun _ : Set α ↦ True).HasNominalCover ι) :
    Fintype.card α ≤ Fintype.card ι := by
  obtain ⟨c, hc, -, hirr⟩ := h.exists_partitions
  have hmem : ∀ a : α, ∃ i, ({a}ᶜ : Set α) ∈ c i := fun a ↦ by
    refine (hirr _ (by rw [irreducibles_top_powerset]; exact ⟨a, rfl⟩)).resolve_left fun h0 ↦ ?_
    obtain ⟨x, hxa, -⟩ := exists_ne_ne_of_two_lt_card h3 a a
    have hx : x ∈ ({a}ᶜ : Set α) := hxa
    rw [h0] at hx
    exact hx
  choose f hf using hmem
  refine Fintype.card_le_of_injective f fun a b hab ↦ ?_
  obtain ⟨x, hxa, hxb⟩ := exists_ne_ne_of_two_lt_card h3 a b
  have hb : ({b}ᶜ : Set α) ∈ c (f a) := by rw [hab]; exact hf b
  have heq : ({a}ᶜ : Set α) = {b}ᶜ := ((hc (f a)).2 x).unique ⟨hf a, hxa⟩ ⟨hb, hxb⟩
  exact singleton_injective (compl_injective heq)

/-! ### Graphs: nominal covers and edge colourings -/

section Graph

variable {V : Type*} {G : SimpleGraph V}

/-- A subset of an unordered pair has at most one element or is the whole pair. -/
theorem subsingleton_or_eq_of_subset_sym2 {T : Set V} (e : Sym2 V) (h : T ⊆ (e : Set V)) :
    T.Subsingleton ∨ T = (e : Set V) := by
  revert h
  refine Sym2.ind (fun v w h ↦ ?_) e
  rw [Sym2.coe_mk] at h ⊢
  by_cases hv : v ∈ T
  · by_cases hw : w ∈ T
    · refine .inr (Subset.antisymm h fun x hx ↦ ?_)
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · refine .inl fun x hx y hy ↦ ?_
      have hx' : x = v := (h hx).resolve_right fun hxw ↦ hw (mem_singleton_iff.1 hxw ▸ hx)
      have hy' : y = v := (h hy).resolve_right fun hyw ↦ hw (mem_singleton_iff.1 hyw ▸ hy)
      rw [hx', hy']
  · refine .inl fun x hx y hy ↦ ?_
    have hx' : x = w := (h hx).resolve_left fun hxv ↦ hv (hxv ▸ hx)
    have hy' : y = w := (h hy).resolve_left fun hyv ↦ hv (hyv ▸ hy)
    rw [hx', hy']

theorem sym2_coe_ne_empty (e : Sym2 V) : (e : Set V) ≠ ∅ :=
  Sym2.ind (fun v w ↦ by rw [Sym2.coe_mk]; exact (insert_nonempty v {w}).ne_empty) e

/-- An edge of a graph has two distinct vertices. -/
theorem not_subsingleton_coe_of_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ¬(e : Set V).Subsingleton := by
  revert he
  refine Sym2.ind (fun v w he hs ↦ ?_) e
  rw [Sym2.coe_mk] at hs
  exact G.ne_of_adj he (hs (mem_insert v {w}) (mem_insert_of_mem v rfl))

/-- An edge contained in an unordered pair is that pair. -/
theorem eq_of_coe_subset_coe {e e' : Sym2 V} (he : e ∈ G.edgeSet)
    (h : (e : Set V) ⊆ (e' : Set V)) : e' = e := by
  revert he h
  refine Sym2.ind (fun v w he h ↦ ?_) e
  rw [Sym2.coe_mk] at h
  exact (Sym2.mem_and_mem_iff (G.ne_of_adj he)).1
    ⟨h (mem_insert v {w}), h (mem_insert_of_mem v rfl)⟩

/-- A vertex of an edge, as a singleton, is a proper subset of the edge. -/
theorem singleton_ssubset_coe {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (hv : v ∈ e) :
    ({v} : Set V) ⊂ (e : Set V) :=
  ⟨singleton_subset_iff.2 hv, fun h ↦
    not_subsingleton_coe_of_mem_edgeSet he (subsingleton_singleton.anti h)⟩

theorem sym2_coe_ne_univ [Fintype V] (h3 : 2 < Fintype.card V) (e : Sym2 V) :
    (e : Set V) ≠ univ := by
  refine Sym2.ind (fun v w h ↦ ?_) e
  obtain ⟨x, hxv, hxw⟩ := exists_ne_ne_of_two_lt_card h3 v w
  have hx : x ∈ ((s(v, w) : Sym2 V) : Set V) := by rw [h]; exact mem_univ x
  rw [Sym2.coe_mk] at hx
  rcases hx with hx | hx
  · exact hxv hx
  · exact hxw hx

/-- The closure system of a graph: the whole vertex set, the sets with at most one vertex, and
the edges. -/
def edgeSystem (G : SimpleGraph V) : ClosureSubsystem fun _ : Set V ↦ True where
  carrier := {A | A = univ ∨ A.Subsingleton ∨ ∃ e ∈ G.edgeSet, A = (e : Set V)}
  sInter_mem' S hS := by
    by_cases h1 : ∀ A ∈ S, A = univ
    · exact .inl (sInter_eq_univ.2 h1)
    push Not at h1
    obtain ⟨A, hA, hAu⟩ := h1
    rcases (hS hA).resolve_left hAu with hsub | ⟨e, he, rfl⟩
    · exact .inr (.inl (hsub.anti (sInter_subset_of_mem hA)))
    · rcases subsingleton_or_eq_of_subset_sym2 e (sInter_subset_of_mem hA) with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨e, he, h⟩)
  isClosed' _ _ := True.intro

theorem mem_edgeSystem {A : Set V} :
    A ∈ edgeSystem G ↔ A = univ ∨ A.Subsingleton ∨ ∃ e ∈ G.edgeSet, A = (e : Set V) :=
  Iff.rfl

/-- In a graph with more than two vertices, the edges are `⋂`-irreducible in `edgeSystem G`. -/
theorem coe_mem_irreducibles_edgeSystem [Fintype V] (h3 : 2 < Fintype.card V) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : (e : Set V) ∈ (edgeSystem G).irreducibles := by
  refine ⟨.inr (.inr ⟨e, he, rfl⟩), fun h ↦ ?_⟩
  have huniv : ⋂₀ {B | B ∈ edgeSystem G ∧ (e : Set V) ⊂ B} = univ := by
    refine sInter_eq_univ.2 fun B hB ↦ ?_
    rcases hB.1 with h | h | ⟨e', -, rfl⟩
    · exact h
    · exact absurd (h.anti hB.2.subset) (not_subsingleton_coe_of_mem_edgeSet he)
    · exact absurd (by rw [eq_of_coe_subset_coe he hB.2.subset]) hB.2.ne
  rw [huniv] at h
  exact sym2_coe_ne_univ h3 e h.symm

/-- A nominal cover of `edgeSystem G` by `ι` closure systems yields a proper edge colouring of
`G` with colours `ι`: two edges with a common vertex are not blocks of the same partition. -/
theorem HasNominalCover.nonempty_lineGraph_coloring [Fintype V] (h3 : 2 < Fintype.card V)
    (h : (edgeSystem G).HasNominalCover ι) : Nonempty (G.lineGraph.Coloring ι) := by
  obtain ⟨c, hc, -, hirr⟩ := h.exists_partitions
  have hmem : ∀ e : G.edgeSet, ∃ i, ((e : Sym2 V) : Set V) ∈ c i := fun e ↦
    (hirr _ (coe_mem_irreducibles_edgeSystem h3 e.2)).resolve_left (sym2_coe_ne_empty _)
  choose col hcol using hmem
  refine ⟨SimpleGraph.Coloring.mk col fun {e e'} hadj heq ↦ ?_⟩
  obtain ⟨hne, x, hx, hx'⟩ := SimpleGraph.lineGraph_adj_iff_exists.1 hadj
  have he' : ((e' : Sym2 V) : Set V) ∈ c (col e) := by rw [heq]; exact hcol e'
  have hset : ((e : Sym2 V) : Set V) = ((e' : Sym2 V) : Set V) :=
    ((hc (col e)).2 x).unique ⟨hcol e, hx⟩ ⟨he', hx'⟩
  exact hne (Subtype.ext (SetLike.coe_injective hset))

/-- A proper edge colouring of a finite graph `G` with at least two colours `ι` yields a nominal
cover of `edgeSystem G` by `ι` closure systems: each colour class, a matching, is completed to a
partition by the singletons of the vertices it does not cover. -/
theorem hasNominalCover_edgeSystem_of_coloring [Finite V] [Nontrivial ι]
    (C : G.lineGraph.Coloring ι) : (edgeSystem G).HasNominalCover ι := by
  refine hasNominalCover_iff.2 ⟨.inr (.inl subsingleton_empty),
    fun i ↦ {B | (∃ e : G.edgeSet, C e = i ∧ B = ((e : Sym2 V) : Set V)) ∨
      ∃ v, B = {v} ∧ ∀ e : G.edgeSet, C e = i → v ∉ (e : Sym2 V)}, fun i ↦ ⟨?_, fun x ↦ ?_⟩,
    ?_, fun A hA ↦ ?_⟩
  · rintro (⟨e, -, h⟩ | ⟨v, h, -⟩)
    · exact sym2_coe_ne_empty _ h.symm
    · exact singleton_ne_empty v h.symm
  · by_cases hx : ∃ e : G.edgeSet, C e = i ∧ x ∈ (e : Sym2 V)
    · obtain ⟨e, hei, hxe⟩ := hx
      refine ⟨((e : Sym2 V) : Set V), ⟨.inl ⟨e, hei, rfl⟩, hxe⟩, ?_⟩
      rintro B ⟨⟨e', he'i, rfl⟩ | ⟨v, rfl, hv⟩, hxB⟩
      · by_contra hne
        have hee : e' ≠ e := fun h ↦ hne (by rw [h])
        exact C.valid (SimpleGraph.lineGraph_adj_iff_exists.2 ⟨hee, x, hxB, hxe⟩)
          (he'i.trans hei.symm)
      · rw [mem_singleton_iff.1 hxB] at hxe
        exact absurd hxe (hv e hei)
    · push Not at hx
      refine ⟨{x}, ⟨.inr ⟨x, rfl, hx⟩, rfl⟩, ?_⟩
      rintro B ⟨⟨e', he'i, rfl⟩ | ⟨v, rfl, hv⟩, hxB⟩
      · exact absurd hxB (hx e' he'i)
      · rw [mem_singleton_iff.1 hxB]
  · rintro i B (⟨e, -, rfl⟩ | ⟨v, rfl, -⟩)
    · exact .inr (.inr ⟨e, e.2, rfl⟩)
    · exact .inr (.inl subsingleton_singleton)
  · rcases hA.1 with rfl | hsub | ⟨e, he, rfl⟩
    · exact (univ_notMem_irreducibles hA).elim
    · rcases hsub.eq_empty_or_singleton with rfl | ⟨v, rfl⟩
      · exact .inl rfl
      · refine .inr ?_
        by_contra hno
        push Not at hno
        have hex : ∀ i, ∃ e : G.edgeSet, C e = i ∧ v ∈ (e : Sym2 V) := fun i ↦ by
          by_contra h
          push Not at h
          exact hno i (.inr ⟨v, rfl, h⟩)
        obtain ⟨i, j, hij⟩ := exists_pair_ne ι
        obtain ⟨e₁, h₁, hv₁⟩ := hex i
        obtain ⟨e₂, h₂, hv₂⟩ := hex j
        have hne : e₁ ≠ e₂ := fun h ↦ hij (by rw [← h₁, ← h₂, h])
        refine hA.2 (Subset.antisymm (fun x hx ↦ ?_) (subset_sInter fun B hB ↦ hB.2.subset))
        have hx₁ : x ∈ (e₁ : Sym2 V) :=
          hx _ ⟨.inr (.inr ⟨e₁, e₁.2, rfl⟩), singleton_ssubset_coe e₁.2 hv₁⟩
        have hx₂ : x ∈ (e₂ : Sym2 V) :=
          hx _ ⟨.inr (.inr ⟨e₂, e₂.2, rfl⟩), singleton_ssubset_coe e₂.2 hv₂⟩
        by_contra hxv
        have hxv' : x ≠ v := fun h ↦ hxv (mem_singleton_iff.2 h)
        have he₁ := (Sym2.mem_and_mem_iff hxv').1 ⟨hx₁, hv₁⟩
        have he₂ := (Sym2.mem_and_mem_iff hxv').1 ⟨hx₂, hv₂⟩
        exact hne (Subtype.ext (he₁.trans he₂.symm))
    · exact .inr ⟨C ⟨e, he⟩, .inl ⟨⟨e, he⟩, rfl, rfl⟩⟩

/-- For a finite graph `G` with more than two vertices and at least two colours `ι`, the closure
system `edgeSystem G` is a join of `ι` nominal closure systems iff `G` has a proper edge
colouring with colours `ι`, that is, a colouring of its line graph. -/
theorem hasNominalCover_edgeSystem_iff [Fintype V] [Nontrivial ι] (h3 : 2 < Fintype.card V) :
    (edgeSystem G).HasNominalCover ι ↔ Nonempty (G.lineGraph.Coloring ι) :=
  ⟨fun h ↦ h.nonempty_lineGraph_coloring h3, fun ⟨C⟩ ↦ hasNominalCover_edgeSystem_of_coloring C⟩

end Graph

end ClosureSubsystem

end FCA
