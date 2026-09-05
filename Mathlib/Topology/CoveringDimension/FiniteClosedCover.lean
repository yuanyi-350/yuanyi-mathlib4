/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.ClosedUnion

/-! # Covering dimension and finite closed covers -/

public section

open scoped CoveringDimension

universe u v

/-- Helper for Corollary 50.3: the copy of `A` inside a containing subtype `B`
has the same covering dimension as `A`. -/
private lemma coveringDimension_nestedSubtype
    {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    dim ((Subtype.val : B → X) ⁻¹' A) = dim A := by
  exact (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by simpa using hAB)).coveringDimension_congr

/-- Helper for Corollary 50.3: the covering dimension of the union of two
closed subsets is the maximum of their covering dimensions. -/
private lemma coveringDimension_closedUnion
    {X : Type u} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsClosed T) :
    dim (S ∪ T : Set X) = max (dim S) (dim T) := by
  -- Apply Theorem 50.2 inside the union subtype and hide its nested-subtype pieces.
  let U : Set X := S ∪ T
  let S' : Set U := (Subtype.val : U → X) ⁻¹' S
  let T' : Set U := (Subtype.val : U → X) ⁻¹' T
  have hS' : IsClosed S' := hS.preimage continuous_subtype_val
  have hT' : IsClosed T' := hT.preimage continuous_subtype_val
  have hcover : S' ∪ T' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases x.2 with hxS | hxT
    · exact Or.inl hxS
    · exact Or.inr hxT
  have hSsub : S ⊆ U := Set.subset_union_left
  have hTsub : T ⊆ U := Set.subset_union_right
  calc
    dim (S ∪ T : Set X) = dim U := rfl
    _ = max (dim S') (dim T') := coveringDimension_union_closed hS' hT' hcover
    _ = max (dim S) (dim T) := congrArg₂ max
      (coveringDimension_nestedSubtype hSsub)
      (coveringDimension_nestedSubtype hTsub)

/-- Helper for Corollary 50.3: covering dimension turns a finite union of
closed subsets into the finite supremum of their dimensions. -/
private lemma coveringDimension_finset_iUnion_closed
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (Y : I → Set X) (s : Finset I) (hclosed : ∀ i ∈ s, IsClosed (Y i)) :
    dim (⋃ i ∈ s, Y i) = s.sup fun i ↦ dim (Y i) := by
  classical
  -- Induct on the finite family, using the binary closed-union interface at each insertion.
  revert hclosed
  refine Finset.induction_on s ?_ ?_
  · intro _
    have hEmptyUnion : (⋃ i ∈ (∅ : Finset I), Y i) = (∅ : Set X) := by
      ext x
      simp
    have hempty : IsEmpty (∅ : Set X) := inferInstance
    rw [hEmptyUnion, Finset.sup_empty]
    exact (coveringDimension_eq_bot_iff (∅ : Set X)).mpr hempty
  · intro a t hat ih hclosed
    have hYa : IsClosed (Y a) := hclosed a (Finset.mem_insert_self a t)
    have htClosed : IsClosed (⋃ i ∈ t, Y i) := by
      apply isClosed_biUnion_finset
      intro i hi
      exact hclosed i (Finset.mem_insert_of_mem hi)
    have htDimension : dim (⋃ i ∈ t, Y i) = t.sup fun i ↦ dim (Y i) := by
      apply ih
      intro i hi
      exact hclosed i (Finset.mem_insert_of_mem hi)
    calc
      dim (⋃ i ∈ insert a t, Y i) = dim (Y a ∪ ⋃ i ∈ t, Y i : Set X) := by
        rw [Finset.set_biUnion_insert]
      _ = max (dim (Y a)) (dim (⋃ i ∈ t, Y i)) :=
        coveringDimension_closedUnion hYa htClosed
      _ = max (dim (Y a)) (t.sup fun i ↦ dim (Y i)) := congrArg (max (dim (Y a))) htDimension
      _ = (insert a t).sup fun i ↦ dim (Y i) := by
        rw [Finset.sup_insert]

/-- Corollary 50.3. The covering dimension of a finite closed cover is the
maximum of the covering dimensions of its members. -/
theorem coveringDimension_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ) :
    dim X = Finset.univ.sup fun i ↦ dim (Y i) := by
  -- Identify `X` with its universal subtype, then apply the finite-union formula.
  have hfiniteCover : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = Set.univ := by
    simpa using hcover
  calc
    dim X = dim (Set.univ : Set X) :=
      (Homeomorph.Set.univ X).coveringDimension_congr.symm
    _ = dim (⋃ i ∈ (Finset.univ : Finset ι), Y i) :=
      congrArg (fun S : Set X ↦ dim S) hfiniteCover.symm
    _ = Finset.univ.sup fun i ↦ dim (Y i) :=
      coveringDimension_finset_iUnion_closed Y Finset.univ fun i _ ↦ hclosed i
