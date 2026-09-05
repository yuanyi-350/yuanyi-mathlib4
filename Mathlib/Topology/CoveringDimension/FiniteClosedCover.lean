/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.ClosedUnion
import Mathlib.Data.Fintype.Lattice

/-! # Covering dimension and finite closed covers -/

public section

open scoped CoveringDimension

universe u v

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
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hSsub)).coveringDimension_congr
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hTsub)).coveringDimension_congr

/-- Helper for Corollary 50.3: covering dimension turns a finite union of
closed subsets into the finite supremum of their dimensions. -/
private lemma coveringDimension_finset_iUnion_closed
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (Y : I → Set X) (s : Finset I) (hclosed : ∀ i ∈ s, IsClosed (Y i)) :
    dim (⋃ i ∈ s, Y i) = s.sup fun i ↦ dim (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sup_insert]
      have hs : ∀ i ∈ s, IsClosed (Y i) := fun i hi ↦ hclosed i (Finset.mem_insert_of_mem hi)
      rw [coveringDimension_closedUnion (hclosed a (Finset.mem_insert_self _ _))
        (isClosed_biUnion_finset hs), ih hs]

/-- The covering dimension of a finite union of closed subsets is the supremum of their
covering dimensions. -/
theorem coveringDimension_iUnion_of_isClosed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i)) :
    dim (⋃ i, Y i) = ⨆ i, dim (Y i) := by
  let _ := Fintype.ofFinite ι
  have hunion : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = ⋃ i, Y i := by simp
  rw [← hunion, coveringDimension_finset_iUnion_closed Y Finset.univ (fun i _ ↦ hclosed i),
    Finset.sup_univ_eq_iSup]

/-- Corollary 50.3. The covering dimension of a finite closed cover is the
maximum of the covering dimensions of its members. -/
theorem coveringDimension_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ) :
    dim X = Finset.univ.sup fun i ↦ dim (Y i) := by
  rw [Finset.sup_univ_eq_iSup, ← coveringDimension_iUnion_of_isClosed Y hclosed, hcover]
  exact (Homeomorph.Set.univ X).coveringDimension_congr.symm
