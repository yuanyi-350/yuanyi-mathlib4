/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.PointFinite
import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.OpenCover

/-! # Shrinking point-finite open covers -/

public section

open Set TopologicalSpace

universe u v

namespace TopologicalSpace.IsOpenCover

/-- A point-finite open cover of a normal space has an open shrinking whose
closures refine the original cover. -/
theorem exists_shrinking {ι : Type u} {X : Type v} [TopologicalSpace X] [NormalSpace X]
    {U : ι → Opens X} (hU : IsOpenCover U)
    (hUfinite : PointFinite (fun i ↦ (U i : Set X))) :
    ∃ V : ι → Opens X, IsOpenCover V ∧ ∀ i, closure (V i : Set X) ⊆ U i := by
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset (fun i ↦ (U i).2)
      (fun x ↦ hUfinite.finite x) hU.iSup_set_eq_univ
  exact ⟨fun i ↦ ⟨V i, hVopen i⟩, IsOpenCover.of_sets hVopen hVcover, hVclosure⟩

end TopologicalSpace.IsOpenCover

/-- An open cover of a compact normal space has a finite subcover, indexed without repetitions,
and an open shrinking whose closures lie in the selected members. -/
theorem existsFiniteIndexedShrinkingSubcover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
    (𝒜 : Set (Set X)) (hopen : ∀ U ∈ 𝒜, IsOpen U) (hcover : ⋃₀ 𝒜 = Set.univ) :
    ∃ (ι : Type u) (_ : Finite ι) (B C : ι → Opens X),
      IsOpenCover B ∧ IsOpenCover C ∧
      Function.Injective (fun i ↦ (B i : Set X)) ∧
      (∀ i, (B i : Set X) ∈ 𝒜) ∧
      ∀ i, closure (C i : Set X) ⊆ B i := by
  classical
  let A : 𝒜 → Opens X := fun U ↦ ⟨U.1, hopen U.1 U.2⟩
  have hA : IsOpenCover A :=
    IsOpenCover.of_sets _ (by simpa only [← Set.sUnion_eq_iUnion] using hcover)
  obtain ⟨t, ht⟩ := hA.exists_finite_of_compactSpace
  let B : t → Opens X := fun i ↦ A i.1
  have hB : IsOpenCover B := ht
  obtain ⟨C, hC, hCB⟩ := hB.exists_shrinking (pointFinite_iff.mpr fun _ ↦ Set.toFinite _)
  exact ⟨t, inferInstance, B, C, hB, hC,
    Subtype.val_injective.comp Subtype.val_injective, fun i ↦ i.1.2, hCB⟩
