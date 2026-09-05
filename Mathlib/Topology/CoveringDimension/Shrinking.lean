/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.OpenCover

/-! # Finite shrinking subcovers -/

public section

open Set TopologicalSpace

universe u

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
  obtain ⟨C, hCcover, hCopen, hCB⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ (B i).isOpen) (fun _ ↦ Set.toFinite _) hB.iSup_set_eq_univ
  exact ⟨t, inferInstance, B, fun i ↦ ⟨C i, hCopen i⟩,
    hB, IsOpenCover.of_sets hCopen hCcover,
    Subtype.val_injective.comp Subtype.val_injective, fun i ↦ i.1.2, hCB⟩
