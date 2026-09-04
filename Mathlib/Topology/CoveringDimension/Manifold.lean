/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.CoveringDimension.Euclidean
public import Mathlib.Topology.CoveringDimension.FiniteClosedUnion
public import Mathlib.Topology.ShrinkingLemma

/-! # Covering dimension of compact topological manifolds -/

public section

open Set

universe u

/-- A compact subset of a Euclidean-charted locally compact Hausdorff space is an exact finite
union of compact closed sets lying in chart sources. -/
private lemma existsFiniteClosedChartCover {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    ∃ (t : Finset M) (C : t → Set M), K = ⋃ i, C i ∧
      (∀ i, IsClosed (C i)) ∧ (∀ i, IsCompact (C i)) ∧
      ∀ i, C i ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source := by
  classical
  have h_chart_open : ∀ x : M,
      IsOpen (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x
    exact (chartAt (EuclideanSpace ℝ (Fin m)) x).open_source
  have h_chart_cover :
      K ⊆ ⋃ x : M, (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin m)) x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin m)) x).source)
    h_chart_open h_chart_cover
  let U : t → Set M := fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source
  have hKU : K ⊆ ⋃ i, U i := by
    intro x hx
    have hx_cover := ht hx
    simp only [Set.mem_iUnion] at hx_cover ⊢
    obtain ⟨i, hi, hxi⟩ := hx_cover
    exact ⟨⟨i, hi⟩, hxi⟩
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    exact (chartAt (EuclideanSpace ℝ (Fin m)) i.1).open_source
  have hU_pointFinite : ∀ x ∈ K, {i | x ∈ U i}.Finite := by
    intro _ _
    exact Set.toFinite _
  obtain ⟨V, hKV, hV_closed, hV_subset, hV_compact⟩ :=
    exists_subset_iUnion_compact_subset_t2space (u := U) hK hU_open hU_pointFinite hKU
  let C : t → Set M := fun i ↦ K ∩ V i
  refine ⟨t, C, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hxK
      have hxV := hKV hxK
      rw [Set.mem_iUnion] at hxV ⊢
      obtain ⟨i, hxi⟩ := hxV
      exact ⟨i, hxK, hxi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact hxi.1
  · intro i
    exact hK.isClosed.inter (hV_closed i)
  · intro i
    exact (hV_compact i).inter_left hK.isClosed
  · intro i _ hxi
    exact hV_subset i hxi.2

/-- A compact set contained in one chart source has covering dimension at most the dimension
of the Euclidean model. -/
private lemma compactSubsetChartSourceHasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    (K : Set M) (hK : IsCompact K) (x : M)
    (hK_source : K ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) x).source) :
    HasCoveringDimensionLE K m := by
  have h_image_compact :
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) :=
    hK.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin m)) x).continuousOn.mono hK_source)
  let restrictedChart :
      K ≃ₜ (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K :=
    (chartAt (EuclideanSpace ℝ (Fin m)) x).homeomorphOfImageSubsetSource hK_source rfl
  have h_image_dimension :
      HasCoveringDimensionLE
        ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) m :=
    compactSubset_euclideanSpace_hasCoveringDimensionLE _ h_image_compact
  exact restrictedChart.symm.hasCoveringDimensionLE_of h_image_dimension

/-- The covering dimension of a compact Hausdorff `m`-manifold is at most `m`. -/
theorem compactManifold_coveringDimension_le {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [CompactSpace M] :
    HasCoveringDimensionLE M m := by
  let _ : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  obtain ⟨t, C, hCunion, hCclosed, hCcompact, hCsource⟩ :=
    existsFiniteClosedChartCover (m := m) (Set.univ : Set M)
      CompactSpace.isCompact_univ
  have hCdim : ∀ i, HasCoveringDimensionLE (C i) m := by
    intro i
    exact compactSubsetChartSourceHasCoveringDimensionLE
      (C i) (hCcompact i) i.1 (hCsource i)
  exact HasCoveringDimensionLE.finite_iUnion_closed C hCclosed hCunion.symm hCdim
