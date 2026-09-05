/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.CoveringDimension.Euclidean
public import Mathlib.Topology.CoveringDimension.ClosedUnion
public import Mathlib.Topology.ShrinkingLemma

/-! # Covering dimension of compact topological manifolds -/

public section

open Set

universe u

/-- The covering dimension of a compact Hausdorff `m`-manifold is at most `m`. -/
theorem compactManifold_coveringDimension_le {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [CompactSpace M] :
    HasCoveringDimensionLE M m := by
  classical
  -- Choose finitely many charts and shrink their sources while retaining a cover.
  let e := chartAt (EuclideanSpace ℝ (Fin m)) (M := M)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (e x).source) (fun x ↦ (e x).open_source)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  let U : t → Set M := fun i ↦ (e i.1).source
  have hUcover : ⋃ i, U i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨V, hVcover, _, hVclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i : t ↦ (e i.1).open_source) (fun _ ↦ Set.toFinite _) hUcover
  apply HasCoveringDimensionLE.finite_iUnion_closed (fun i ↦ closure (V i))
    (fun _ ↦ isClosed_closure)
    (by rw [← closure_iUnion_of_finite, hVcover, closure_univ])
  intro i
  -- Each closed shrinking is compact and homeomorphic to its image in one Euclidean chart.
  let K := closure (V i)
  have hK : IsCompact K := isClosed_closure.isCompact
  have hsource : K ⊆ (e i.1).source := hVclosure i
  exact ((e i.1).homeomorphOfImageSubsetSource hsource rfl).symm.hasCoveringDimensionLE_of
    (compactSubset_euclideanSpace_hasCoveringDimensionLE _
      (hK.image_of_continuousOn ((e i.1).continuousOn.mono hsource)))
