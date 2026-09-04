/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Embedding
public import Mathlib.Topology.CoveringDimension.Euclidean

/-! # Finite covering dimension and Euclidean embeddings -/

public section

universe u

/-- A compact space embedded in a finite-dimensional real Euclidean space has
finite covering dimension. -/
theorem finiteCoveringDimension_of_euclideanEmbedding
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {N : ℕ}
    {f : X → EuclideanSpace ℝ (Fin N)} (hf : Topology.IsEmbedding f) :
    FiniteCoveringDimension X := by
  -- Bound the compact range by its Euclidean dimension, then transport the bound to `X`.
  rw [finiteCoveringDimension_iff]
  refine ⟨N, hf.toHomeomorph.symm.hasCoveringDimensionLE_of ?_⟩
  exact compactSubset_euclideanSpace_hasCoveringDimensionLE (Set.range f)
    (isCompact_range hf.continuous)

/-- A compact metrizable space of finite covering dimension embeds in some
finite-dimensional real Euclidean space. -/
theorem existsEuclideanEmbedding_of_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (hdim : FiniteCoveringDimension X) :
    ∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f := by
  rw [finiteCoveringDimension_iff] at hdim
  obtain ⟨m, hm⟩ := hdim
  obtain ⟨f, hf⟩ := existsEuclideanEmbedding_of_hasCoveringDimensionLE hm
  exact ⟨2 * m + 1, f, hf⟩

/-- Corollary 50.9. A compact metrizable space embeds in some finite-dimensional real
Euclidean space if and only if it has finite covering dimension. -/
theorem existsEuclideanEmbedding_iff_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    (∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f) ↔
      FiniteCoveringDimension X := by
  constructor
  · rintro ⟨N, f, hf⟩
    exact finiteCoveringDimension_of_euclideanEmbedding hf
  · exact existsEuclideanEmbedding_of_finiteCoveringDimension
