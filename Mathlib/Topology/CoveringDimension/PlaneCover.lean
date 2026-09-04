/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Euclidean

/-! # Covering dimension of compact subsets of the plane -/

public section

open scoped CoveringDimension

/-- Every compact subset of the plane has covering dimension at most two. -/
theorem compactSubset_euclideanPlane_coveringDimension_le_two
    (X : Set (ℝ × ℝ)) (hX : IsCompact X) :
    dim X ≤ 2 := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).trans Homeomorph.finTwoArrow
  let Y : Set (EuclideanSpace ℝ (Fin 2)) := e ⁻¹' X
  have hY : IsCompact Y := e.isCompact_preimage.mpr hX
  have hImage : e '' Y = X := by
    simp [Y]
  let eY : Y ≃ₜ X :=
    (Homeomorph.image e Y).trans (Homeomorph.setCongr hImage)
  rw [← eY.coveringDimension_congr]
  exact compactSubset_euclideanSpace_coveringDimension_le Y hY
