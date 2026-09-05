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

/-- Helper for Theorem 50.1: the ambient extension of an open cover of a subtype,
with the complement of the subtype added. -/
private def ambientOpenExtensionFamily {X : Type u} [TopologicalSpace X]
    (Y : Set X) (𝒜 : Set (Set Y)) : Set (Set X) :=
  {U | IsOpen U ∧ (Subtype.val : Y → X) ⁻¹' U ∈ 𝒜} ∪ {Yᶜ}

/-- Helper for Theorem 50.1: the ambient extension of a cover of a closed subtype
is an open cover of the ambient space. -/
private lemma ambientOpenExtensionFamilySpec
    {X : Type u} [TopologicalSpace X] {Y : Set X} {𝒜 : Set (Set Y)}
    (hY : IsClosed Y) (h𝒜_open : ∀ A ∈ 𝒜, IsOpen A)
    (h𝒜_cover : ⋃₀ 𝒜 = Set.univ) :
    (∀ U ∈ ambientOpenExtensionFamily Y 𝒜, IsOpen U) ∧
      ⋃₀ ambientOpenExtensionFamily Y 𝒜 = Set.univ := by
  constructor
  · -- Every lifted member is open by construction, and the added complement is open.
    intro U hU
    rw [ambientOpenExtensionFamily] at hU
    rcases hU with hU | hU
    · exact hU.1
    · rw [Set.mem_singleton_iff] at hU
      rw [hU]
      exact hY.isOpen_compl
  · -- A point of `Y` is covered by a lifted member; a point outside `Y` is in its complement.
    rw [Set.sUnion_eq_univ_iff]
    intro x
    by_cases hx : x ∈ Y
    · let y : Y := ⟨x, hx⟩
      have hy_cover : y ∈ ⋃₀ 𝒜 := by
        rw [h𝒜_cover]
        exact Set.mem_univ y
      rw [Set.mem_sUnion] at hy_cover
      obtain ⟨A, hA𝒜, hyA⟩ := hy_cover
      obtain ⟨U, hU_open, hU_preimage⟩ :=
        isOpen_induced_iff.mp (h𝒜_open A hA𝒜)
      have hpreimage_mem : (Subtype.val : Y → X) ⁻¹' U ∈ 𝒜 := by
        rw [hU_preimage]
        exact hA𝒜
      have hyU : y ∈ (Subtype.val : Y → X) ⁻¹' U := by
        rw [hU_preimage]
        exact hyA
      refine ⟨U, ?_, hyU⟩
      rw [ambientOpenExtensionFamily]
      exact Or.inl ⟨hU_open, hpreimage_mem⟩
    · refine ⟨Yᶜ, ?_, hx⟩
      rw [ambientOpenExtensionFamily]
      exact Or.inr (Set.mem_singleton Yᶜ)

/-- Helper for Theorem 50.1: the family of nonempty preimages of members of a
set family. -/
private def nonemptyPreimageFamily {α β : Type*} (f : α → β)
    (ℬ : Set (Set β)) : Set (Set α) :=
  {V | V.Nonempty ∧ ∃ B ∈ ℬ, V = f ⁻¹' B}

/-- Helper for Theorem 50.1: restricting an ambient open refinement to a subtype
preserves coverage, refinement, and the point-multiplicity bound. -/
private lemma restrictedAmbientRefinementSpec
    {X : Type u} [TopologicalSpace X] {Y : Set X} {𝒜 : Set (Set Y)}
    {ℬ : Set (Set X)} {k : ℕ}
    (hℬ_refines : IsCofinalFor ℬ (ambientOpenExtensionFamily Y 𝒜))
    (hℬ_open : ∀ B ∈ ℬ, IsOpen B)
    (hℬ_cover : ⋃₀ ℬ = Set.univ) (hℬ_order : ℬ.HasOrderLE k) :
    IsCofinalFor (nonemptyPreimageFamily (Subtype.val : Y → X) ℬ) 𝒜 ∧
      (∀ V ∈ nonemptyPreimageFamily (Subtype.val : Y → X) ℬ, IsOpen V) ∧
      ⋃₀ nonemptyPreimageFamily (Subtype.val : Y → X) ℬ = Set.univ ∧
        (nonemptyPreimageFamily (Subtype.val : Y → X) ℬ).HasOrderLE k := by
  have ⟨hrestricted_refines, hrestricted_open⟩ :
      IsCofinalFor (nonemptyPreimageFamily (Subtype.val : Y → X) ℬ) 𝒜 ∧
        (∀ V ∈ nonemptyPreimageFamily (Subtype.val : Y → X) ℬ, IsOpen V) := by
    -- Nonempty restrictions cannot refine the added complement, so each refines `𝒜`.
    constructor
    · intro V hV
      rw [nonemptyPreimageFamily] at hV
      obtain ⟨hV_nonempty, B, hBℬ, hV_preimage⟩ := hV
      obtain ⟨U, hUambient, hBU⟩ :=
        hℬ_refines hBℬ
      rw [ambientOpenExtensionFamily] at hUambient
      rcases hUambient with hUambient | hUambient
      · refine ⟨(Subtype.val : Y → X) ⁻¹' U, hUambient.2, ?_⟩
        rw [hV_preimage]
        exact Set.preimage_mono hBU
      · rw [Set.mem_singleton_iff] at hUambient
        rw [hUambient] at hBU
        obtain ⟨y, hyV⟩ := hV_nonempty
        have hy_preimage : y ∈ (Subtype.val : Y → X) ⁻¹' B :=
          hV_preimage ▸ hyV
        have hyB : (y : X) ∈ B := by
          exact hy_preimage
        exact ((hBU hyB) y.property).elim
    · -- Openness descends along the continuous subtype inclusion.
      intro V hV
      rw [nonemptyPreimageFamily] at hV
      obtain ⟨_, B, hBℬ, hV_preimage⟩ := hV
      rw [hV_preimage]
      exact (hℬ_open B hBℬ).preimage continuous_subtype_val
  have hrestricted_cover :
      ⋃₀ nonemptyPreimageFamily (Subtype.val : Y → X) ℬ = Set.univ := by
    -- Restrict an ambient member through each subtype point; it is automatically nonempty.
    rw [Set.sUnion_eq_univ_iff]
    intro y
    have hy_cover : (y : X) ∈ ⋃₀ ℬ := by
      rw [hℬ_cover]
      exact Set.mem_univ y
    rw [Set.mem_sUnion] at hy_cover
    obtain ⟨B, hBℬ, hyB⟩ := hy_cover
    have hpreimage_nonempty : ((Subtype.val : Y → X) ⁻¹' B).Nonempty :=
      ⟨y, hyB⟩
    have hpreimage_eq :
        (Subtype.val : Y → X) ⁻¹' B = (Subtype.val : Y → X) ⁻¹' B := rfl
    refine ⟨(Subtype.val : Y → X) ⁻¹' B, ?_, hyB⟩
    rw [nonemptyPreimageFamily]
    exact ⟨hpreimage_nonempty, B, hBℬ, hpreimage_eq⟩
  have hrestricted_order :
      (nonemptyPreimageFamily (Subtype.val : Y → X) ℬ).HasOrderLE k := by
    apply (hℬ_order.preimage (Subtype.val : Y → X)).of_subset
    rintro V ⟨_, B, hBℬ, rfl⟩
    exact ⟨B, hBℬ, rfl⟩
  exact ⟨hrestricted_refines, hrestricted_open, hrestricted_cover, hrestricted_order⟩

namespace HasCoveringDimensionLE

/-- Helper for Theorem 50.1: a covering-dimension bound remains valid on a closed
subtype. -/
theorem closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLE X n) (hY : IsClosed Y) :
    HasCoveringDimensionLE Y n := by
  -- Extend the subtype cover, refine it in `X`, and restrict the refinement back.
  rw [hasCoveringDimensionLE_iff] at hX ⊢
  intro 𝒜 h𝒜_open h𝒜_cover
  obtain ⟨hambient_open, hambient_cover⟩ :=
    ambientOpenExtensionFamilySpec hY h𝒜_open h𝒜_cover
  obtain ⟨ℬ, hℬ_refines, hℬ_open, hℬ_cover, hℬ_order⟩ :=
    hX (ambientOpenExtensionFamily Y 𝒜) hambient_open hambient_cover
  obtain ⟨hrestricted_refines, hrestricted_open, hrestricted_cover, hrestricted_order⟩ :=
    restrictedAmbientRefinementSpec hℬ_refines hℬ_open hℬ_cover hℬ_order
  exact ⟨nonemptyPreimageFamily (Subtype.val : Y → X) ℬ,
    hrestricted_refines, hrestricted_open, hrestricted_cover, hrestricted_order⟩

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
