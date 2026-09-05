/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Basic
public import Mathlib.Topology.Constructions

/-! # Covering dimension of closed subspaces -/

public section

universe u

namespace HasCoveringDimensionLE

/-- A covering-dimension bound remains valid on a closed subtype. -/
theorem closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLE X n) (hY : IsClosed Y) :
    HasCoveringDimensionLE Y n := by
  rw [hasCoveringDimensionLE_iff] at hX ⊢
  intro 𝒜 h𝒜open h𝒜cover
  -- Extend the open cover to the ambient space and add the complement of `Y`.
  let 𝒰 : Set (Set X) :=
    {U | IsOpen U ∧ (Subtype.val : Y → X) ⁻¹' U ∈ 𝒜} ∪ {Yᶜ}
  have h𝒰open : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U (⟨hU, _⟩ | rfl)
    · exact hU
    · exact hY.isOpen_compl
  have h𝒰cover : ⋃₀ 𝒰 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Y
    · obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp
        (h𝒜cover.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp (h𝒜open A hA)
      exact Set.mem_sUnion.mpr ⟨U, Or.inl ⟨hU, hA⟩, hxA⟩
    · exact Set.mem_sUnion.mpr ⟨Yᶜ, Or.inr rfl, hx⟩
  obtain ⟨ℬ, hℬrefines, hℬopen, hℬcover, hℬorder⟩ := hX 𝒰 h𝒰open h𝒰cover
  -- Restrict the refinement to `Y`; discard the empty restriction of its complement.
  refine ⟨((fun U : Set X ↦ (Subtype.val : Y → X) ⁻¹' U) '' ℬ) \ {∅},
    ?_, ?_, ?_, hℬorder.preimage Subtype.val |>.of_subset Set.sdiff_subset⟩
  · rintro V ⟨⟨B, hB, rfl⟩, hne⟩
    obtain ⟨U, hU, hBU⟩ := hℬrefines hB
    rcases hU with ⟨_, hU⟩ | rfl
    · exact ⟨Subtype.val ⁻¹' U, hU, Set.preimage_mono hBU⟩
    · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact (hBU hy y.2).elim
  · rintro V ⟨⟨B, hB, rfl⟩, _⟩
    exact (hℬopen B hB).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨B, hB, hy⟩ := Set.mem_sUnion.mp (hℬcover.symm ▸ Set.mem_univ y.1)
    exact Set.mem_sUnion.mpr ⟨Subtype.val ⁻¹' B,
      ⟨⟨B, hB, rfl⟩, Set.nonempty_iff_ne_empty.mp ⟨y, hy⟩⟩, hy⟩

end HasCoveringDimensionLE

open scoped CoveringDimension

/-- A closed subspace of a finite-covering-dimensional space has finite covering dimension. -/
theorem IsClosed.finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) (hX : FiniteCoveringDimension X) :
    FiniteCoveringDimension Y := by
  rw [finiteCoveringDimension_iff] at hX ⊢
  obtain ⟨n, hn⟩ := hX
  exact ⟨n, hn.closedSubtype hY⟩

namespace HasCoveringDimensionLT

/-- A strict covering-dimension bound remains valid on a closed subtype. -/
lemma closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLT X n) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  cases n with
  | zero => exact ⟨fun y ↦ hX.false y.1⟩
  | succ n => exact HasCoveringDimensionLE.closedSubtype hX hY

end HasCoveringDimensionLT

/-- The covering dimension of a closed subspace is at most the covering dimension of the
ambient space. -/
theorem IsClosed.coveringDimension_le
    {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y) :
    _root_.coveringDimension Y ≤ _root_.coveringDimension X := by
  rw [coveringDimension_eq_sInf, coveringDimension_eq_sInf]
  refine sInf_le_sInf ?_
  intro d hd n hdn
  exact (hd n hdn).closedSubtype hY
