/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.FiniteClosedCover
public import Mathlib.Topology.CoveringDimension.ClosedSubspace

/-! # Covering dimension of finite closed unions -/

public section

open Set

universe u v

/-- Helper for Definition 50.8: a finite closed cover inherits the common
covering-dimension bound. -/
lemma HasCoveringDimensionLE.finite_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ)
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE X n := by
  -- Convert the finite closed-union formula into numerical upper bounds.
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_closed Y hclosed hcover,
    Finset.sup_le_iff]
  intro i _
  exact (coveringDimension_le_iff (Y i) n).mpr (hdim i)

/-- Helper for Definition 50.8: a finite union of closed subspaces with a common
covering-dimension bound has that same bound. -/
lemma HasCoveringDimensionLE.finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE (⋃ i, Y i) n := by
  -- Cover the union subtype by closed preimage pieces and identify each piece once.
  let Z : Set X := ⋃ i, Y i
  let Zi : ι → Set Z := fun i ↦ Subtype.val ⁻¹' Y i
  apply HasCoveringDimensionLE.finite_iUnion_closed Zi
  · intro i
    exact (hclosed i).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro z
    rw [Set.mem_iUnion]
    have hz : z.1 ∈ ⋃ i, Y i := z.2
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    exact ⟨i, hzi⟩
  · intro i
    -- The original member and its preimage piece contain exactly the same ambient points.
    let hYZ : Y i ⊆ Z := fun _ hy ↦ Set.mem_iUnion.mpr ⟨i, hy⟩
    let inc : Y i → Z := Set.inclusion hYZ
    let f : Y i → Zi i := fun y ↦ ⟨inc y, y.2⟩
    have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hYZ
    have hf : Topology.IsEmbedding f := hinc.codRestrict _ fun y ↦ y.2
    have hfsurj : Function.Surjective f := by
      intro z
      refine ⟨⟨z.1.1, z.2⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)
    exact (hf.toHomeomorphOfSurjective hfsurj).hasCoveringDimensionLE_of (hdim i)

/-- Helper for Definition 50.8: the strict covering-dimension bound is preserved by finite
unions of closed subspaces. -/
lemma hasCoveringDimensionLT_finiteUnionClosedSubtypes
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hdim : ∀ i, HasCoveringDimensionLT (Y i) n) :
    HasCoveringDimensionLT (⋃ i, Y i) n := by
  -- At zero every member is empty; at a successor use the non-strict union theorem.
  cases n with
  | zero =>
      apply (hasCoveringDimensionLT_zero_iff _).mpr
      constructor
      intro z
      have hz : z.1 ∈ ⋃ i, Y i := z.2
      rw [Set.mem_iUnion] at hz
      obtain ⟨i, hzi⟩ := hz
      exact ((hasCoveringDimensionLT_zero_iff _).mp (hdim i)).false ⟨z.1, hzi⟩
  | succ n =>
      exact HasCoveringDimensionLE.finiteUnionClosedSubtypes Y hclosed hdim

/-- Helper for Definition 50.8: a closed subspace of a space with a strict
covering-dimension bound inherits that bound. -/
lemma HasCoveringDimensionLT.closedSubset
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (h : HasCoveringDimensionLT Z n) (hYZ : Y ⊆ Z) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  -- Split off the empty-space case; successor bounds use the closed-subtype theorem.
  cases n with
  | zero =>
      apply (hasCoveringDimensionLT_zero_iff _).mpr
      constructor
      intro y
      exact ((hasCoveringDimensionLT_zero_iff _).mp h).false ⟨y.1, hYZ y.2⟩
  | succ n =>
      let P : Set Z := Subtype.val ⁻¹' Y
      have hPclosed : IsClosed P := hY.preimage continuous_subtype_val
      have hP : HasCoveringDimensionLE P n := h.closedSubtype hPclosed
      let hYZ' : Y ⊆ Z := hYZ
      let inc : Y → Z := Set.inclusion hYZ'
      let f : Y → P := fun y ↦ ⟨inc y, y.2⟩
      have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hYZ'
      have hf : Topology.IsEmbedding f := hinc.codRestrict _ fun y ↦ y.2
      have hfsurj : Function.Surjective f := by
        intro z
        refine ⟨⟨z.1.1, z.2⟩, ?_⟩
        exact Subtype.ext (Subtype.ext rfl)
      exact (hf.toHomeomorphOfSurjective hfsurj).symm.hasCoveringDimensionLE_of hP
