/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Lebesgue covering dimension

This file defines the Lebesgue covering dimension of a topological space in terms of open
refinements of bounded order. The dimension takes values in `WithBot ℕ∞`, with `⊥` representing
the empty space and `⊤` representing the absence of a finite bound.

## Main definitions

* `IsRefinement`: one collection of sets refines another.
* `Set.HasOrderLE`: every point belongs to at most a prescribed number of members.
* `HasCoveringDimensionLE`: every open cover has an open refinement of order at most `n + 1`.
* `HasCoveringDimensionLT`: strict finite covering-dimension bounds, including the empty case.
* `coveringDimension`: the Lebesgue covering dimension, valued in `WithBot ℕ∞`.

## References

* James R. Munkres, *Topology*, Section 50.
-/

public section

open Set

universe u v

/-! ### Refinements and order of covers -/

/-- A collection `ℬ` refines `𝒜` when every member of `ℬ` is contained in a member of `𝒜`. -/
class IsRefinement {X : Type u} (ℬ 𝒜 : Set (Set X)) : Prop where
  subset_of_mem {B : Set X} (hB : B ∈ ℬ) : ∃ A ∈ 𝒜, B ⊆ A

/-- The defining condition for a refinement. -/
theorem isRefinement_iff {X : Type u} {ℬ 𝒜 : Set (Set X)} :
    IsRefinement ℬ 𝒜 ↔ ∀ B ∈ ℬ, ∃ A ∈ 𝒜, B ⊆ A := by
  constructor
  · exact fun h B hB ↦ h.subset_of_mem hB
  · exact fun h ↦ ⟨fun hB ↦ h _ hB⟩

namespace IsRefinement

/-- Every collection refines itself. -/
theorem refl {X : Type u} (𝒜 : Set (Set X)) : IsRefinement 𝒜 𝒜 :=
  ⟨fun hA ↦ ⟨_, hA, Subset.rfl⟩⟩

/-- Refinement is transitive. -/
theorem trans {X : Type u} {𝒞 ℬ 𝒜 : Set (Set X)}
    (h𝒞ℬ : IsRefinement 𝒞 ℬ) (hℬ𝒜 : IsRefinement ℬ 𝒜) : IsRefinement 𝒞 𝒜 := by
  constructor
  intro C hC
  obtain ⟨B, hB, hCB⟩ := h𝒞ℬ.subset_of_mem hC
  obtain ⟨A, hA, hBA⟩ := hℬ𝒜.subset_of_mem hB
  exact ⟨A, hA, hCB.trans hBA⟩

end IsRefinement

/-- An open refinement is a refinement all of whose members are open. -/
class IsOpenRefinement {X : Type u} [TopologicalSpace X]
    (ℬ 𝒜 : Set (Set X)) : Prop extends IsRefinement ℬ 𝒜 where
  isOpen_of_mem {B : Set X} (hB : B ∈ ℬ) : IsOpen B

/-- An open refinement canonically determines a refinement. -/
instance {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    [h : IsOpenRefinement ℬ 𝒜] : IsRefinement ℬ 𝒜 := h.toIsRefinement

/-- The defining conditions for an open refinement. -/
theorem isOpenRefinement_iff {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} :
    IsOpenRefinement ℬ 𝒜 ↔ IsRefinement ℬ 𝒜 ∧ ∀ B ∈ ℬ, IsOpen B := by
  constructor
  · exact fun h ↦ ⟨h.toIsRefinement, fun _ hB ↦ h.isOpen_of_mem hB⟩
  · rintro ⟨h_refinement, h_open⟩
    exact { h_refinement with isOpen_of_mem := fun hB ↦ h_open _ hB }

/-- A closed refinement is a refinement all of whose members are closed. -/
class IsClosedRefinement {X : Type u} [TopologicalSpace X]
    (ℬ 𝒜 : Set (Set X)) : Prop extends IsRefinement ℬ 𝒜 where
  isClosed_of_mem {B : Set X} (hB : B ∈ ℬ) : IsClosed B

/-- A closed refinement canonically determines a refinement. -/
instance {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    [h : IsClosedRefinement ℬ 𝒜] : IsRefinement ℬ 𝒜 := h.toIsRefinement

/-- The defining conditions for a closed refinement. -/
theorem isClosedRefinement_iff {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} :
    IsClosedRefinement ℬ 𝒜 ↔ IsRefinement ℬ 𝒜 ∧ ∀ B ∈ ℬ, IsClosed B := by
  constructor
  · exact fun h ↦ ⟨h.toIsRefinement, fun _ hB ↦ h.isClosed_of_mem hB⟩
  · rintro ⟨h_refinement, h_closed⟩
    exact { h_refinement with isClosed_of_mem := fun hB ↦ h_closed _ hB }

namespace Set

/-- A collection has order at most `n` when every point belongs to at most `n` members. -/
def HasOrderLE {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n

/-- The pointwise cardinality characterization of `Set.HasOrderLE`. -/
theorem hasOrderLE_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrderLE n ↔ ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

namespace HasOrderLE

/-- An upper bound on the order remains valid after increasing the bound. -/
theorem mono {X : Type u} {𝒜 : Set (Set X)} {n k : ℕ}
    (h : 𝒜.HasOrderLE n) (hnk : n ≤ k) : 𝒜.HasOrderLE k :=
  fun x ↦ (h x).trans (by simpa using hnk)

end HasOrderLE

/-- A collection has order `n` when the upper bound `n` is attained at some point. -/
def HasOrder {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧ 𝒜.HasOrderLE n

/-- The attained pointwise cardinality characterization of `Set.HasOrder`. -/
theorem hasOrder_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrder n ↔
      (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧
        ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

namespace HasOrder

/-- Exact order gives the corresponding upper bound. -/
theorem le {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    𝒜.HasOrderLE n := h.2

/-- Exact order is attained at some point. -/
theorem exists_eq {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    ∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n := h.1

end HasOrder

end Set

/-! ### Covering dimension -/

/-- A space has covering dimension at most `n` when every open cover has an open refining cover
of point multiplicity at most `n + 1`. -/
abbrev HasCoveringDimensionLE (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ 𝒜 : Set (Set X),
    (∀ U ∈ 𝒜, IsOpen U) →
    ⋃₀ 𝒜 = Set.univ →
    ∃ ℬ : Set (Set X),
      IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (n + 1)

/-- A space has covering dimension less than `0` exactly when it is empty, and has covering
dimension less than `n + 1` exactly when it has covering dimension at most `n`. -/
abbrev HasCoveringDimensionLT (X : Type u) [TopologicalSpace X] : ℕ → Prop
  | 0 => IsEmpty X
  | n + 1 => HasCoveringDimensionLE X n

/-- A space has finite covering dimension when it has some finite covering-dimension bound. -/
abbrev FiniteCoveringDimension (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, HasCoveringDimensionLE X n

/-- The covering dimension of a space, with `⊥` for dimension `-1` and `⊤` when no finite
covering-dimension bound exists. -/
noncomputable def coveringDimension (X : Type u) [TopologicalSpace X] : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ n : ℕ, d < n → HasCoveringDimensionLT X n}

/-- Covering dimension expressed as the infimum of its strict natural-number bounds. -/
theorem coveringDimension_eq_sInf (X : Type u) [TopologicalSpace X] :
    coveringDimension X =
      sInf {d : WithBot ℕ∞ | ∀ n : ℕ, d < n → HasCoveringDimensionLT X n} := by
  rfl

namespace CoveringDimension

/-- Notation for the covering dimension of a space. -/
scoped notation "dim " X:arg => coveringDimension X

end CoveringDimension

/-- The open-cover characterization of `HasCoveringDimensionLE`. -/
theorem hasCoveringDimensionLE_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HasCoveringDimensionLE X n ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) →
        ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (n + 1) := by
  rfl

/-- The point-multiplicity characterization of `HasCoveringDimensionLE`. -/
theorem hasCoveringDimensionLE_iff_pointwise (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HasCoveringDimensionLE X n ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) →
        ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧
            ∀ x : X, Set.encard {V ∈ ℬ | x ∈ V} ≤ (n + 1 : ℕ) := by
  simpa only [Set.hasOrderLE_iff] using hasCoveringDimensionLE_iff X n

namespace HasCoveringDimensionLE

/-- A covering-dimension bound remains valid after increasing the bound. -/
theorem mono {X : Type u} [TopologicalSpace X] {n m : ℕ}
    (h : HasCoveringDimensionLE X n) (hnm : n ≤ m) : HasCoveringDimensionLE X m := by
  intro 𝒜 h𝒜_open h𝒜_cover
  obtain ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order⟩ := h 𝒜 h𝒜_open h𝒜_cover
  exact ⟨ℬ, hℬ_refines, hℬ_cover, hℬ_order.mono (Nat.add_le_add_right hnm 1)⟩

end HasCoveringDimensionLE

@[simp]
theorem hasCoveringDimensionLT_zero_iff (X : Type u) [TopologicalSpace X] :
    HasCoveringDimensionLT X 0 ↔ IsEmpty X := by
  rfl

lemma hasCoveringDimensionLT_of_bound {X : Type u} [TopologicalSpace X] {n k : ℕ}
    (h : HasCoveringDimensionLE X n) (hnk : n < k) : HasCoveringDimensionLT X k := by
  cases k with
  | zero => exact (Nat.not_lt_zero n hnk).elim
  | succ k => exact h.mono (Nat.lt_succ_iff.mp hnk)

lemma hasCoveringDimensionLE_of_isEmpty {X : Type u} [TopologicalSpace X]
    (hX : IsEmpty X) (n : ℕ) : HasCoveringDimensionLE X n := by
  intro 𝒜 _ _
  refine ⟨∅, ?_, ?_, ?_⟩
  · rw [isOpenRefinement_iff]
    exact ⟨⟨fun hB ↦ hB.elim⟩, fun _ hB ↦ hB.elim⟩
  · ext x
    exact (hX.false x).elim
  · intro x
    exact (hX.false x).elim

/-- The existence-of-a-bound characterization of finite covering dimension. -/
theorem finiteCoveringDimension_iff (X : Type u) [TopologicalSpace X] :
    FiniteCoveringDimension X ↔ ∃ n : ℕ, HasCoveringDimensionLE X n := by
  rfl

open scoped CoveringDimension

/-- The numerical covering dimension is at most `n` exactly when `n` is a covering-dimension
bound. -/
theorem coveringDimension_le_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    dim X ≤ (n : WithBot ℕ∞) ↔ HasCoveringDimensionLE X n := by
  constructor
  · intro hdim
    have hdim_succ : dim X < (n + 1 : ℕ) := ENat.WithBot.lt_add_one_iff.mpr hdim
    rw [coveringDimension] at hdim_succ
    obtain ⟨d, hd_bounds, hd_succ⟩ := sInf_lt_iff.mp hdim_succ
    exact hd_bounds (n + 1) hd_succ
  · intro hbound
    rw [coveringDimension]
    apply sInf_le
    intro k hnk
    exact hasCoveringDimensionLT_of_bound hbound (by exact_mod_cast hnk)

/-- The covering dimension has value `-1` exactly for empty spaces. -/
@[simp]
theorem coveringDimension_eq_bot_iff (X : Type u) [TopologicalSpace X] :
    dim X = ⊥ ↔ IsEmpty X := by
  constructor
  · intro hdim
    have hdim_zero : dim X < (0 : WithBot ℕ∞) := by
      rw [hdim]
      exact WithBot.bot_lt_coe 0
    rw [coveringDimension] at hdim_zero
    obtain ⟨d, hd_bounds, hd_zero⟩ := sInf_lt_iff.mp hdim_zero
    exact hd_bounds 0 hd_zero
  · intro hX
    apply le_antisymm
    · rw [coveringDimension]
      apply sInf_le
      intro n _
      cases n with
      | zero => exact hX
      | succ n => exact hasCoveringDimensionLE_of_isEmpty hX n
    · exact bot_le

/-- Finite covering dimension is equivalent to the numerical covering dimension being different
from `⊤`. -/
theorem finiteCoveringDimension_iff_coveringDimension_ne_top
    (X : Type u) [TopologicalSpace X] : FiniteCoveringDimension X ↔ dim X ≠ ⊤ := by
  constructor
  · rintro ⟨n, hn⟩ htop
    have hdim : dim X ≤ (n : WithBot ℕ∞) := (coveringDimension_le_iff X n).mpr hn
    rw [htop] at hdim
    have hn_top : (n : WithBot ℕ∞) = ⊤ := by simpa using hdim
    exact ENat.natCast_ne_top n (WithBot.coe_eq_top.mp hn_top)
  · intro hdim
    have hnot_all : ¬ ∀ n : ℕ, n ≤ dim X := (ENat.WithBot.eq_top_iff_forall_ge.not).mp hdim
    push Not at hnot_all
    obtain ⟨n, hn⟩ := hnot_all
    exact ⟨n, (coveringDimension_le_iff X n).mp hn.le⟩

/-! ### Invariance under homeomorphisms -/

/-- A covering-dimension bound is transported along a homeomorphism. -/
theorem Homeomorph.hasCoveringDimensionLE_of
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒠 h𝒠open h𝒠cover
  let 𝒠' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' 𝒠
  have h𝒠'open : ∀ U ∈ 𝒠', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (h𝒠open V hV).preimage e.continuous
  have h𝒠'cover : ⋃₀ 𝒠' = (_root_.Set.univ : Set A) := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒠 := h𝒠cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
  obtain ⟨𝒯, h𝒯refines, h𝒯cover, h𝒯order⟩ := h 𝒠' h𝒠'open h𝒠'cover
  let 𝒯' : Set (Set B) := (fun U : Set A ↦ e '' U) '' 𝒯
  refine ⟨𝒯', ?_, ?_, ?_⟩
  · rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨U, hU, rfl⟩
      obtain ⟨W, hW, hUW⟩ := h𝒯refines.subset_of_mem hU
      obtain ⟨Z, hZ, rfl⟩ := hW
      refine ⟨Z, hZ, ?_⟩
      rintro y ⟨x, hxU, hxy⟩
      subst y
      exact hUW hxU
    · rintro V ⟨U, hU, rfl⟩
      exact e.isOpen_image.mpr (h𝒯refines.isOpen_of_mem hU)
  · apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ 𝒯 := h𝒯cover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨U, hU, hyU⟩ := hy
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
  · intro y
    let incident : Set (Set A) := {U ∈ 𝒯 | e.symm y ∈ U}
    have hincident : {V ∈ 𝒯' | y ∈ V} = (fun U : Set A ↦ e '' U) '' incident := by
      ext V
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, hyU⟩
        obtain ⟨x, hxU, hxy⟩ := hyU
        have hx : x = e.symm y := by simpa using congrArg e.symm hxy
        exact ⟨U, ⟨hU, hx ▸ hxU⟩, rfl⟩
      · rintro ⟨U, ⟨hU, hyU⟩, rfl⟩
        exact ⟨⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
    rw [hincident, e.injective.image_injective.encard_image]
    exact h𝒯order (e.symm y)

/-- Covering-dimension bounds are preserved by homeomorphisms. -/
protected theorem Homeomorph.hasCoveringDimensionLE
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (n : ℕ) : HasCoveringDimensionLE A n ↔ HasCoveringDimensionLE B n :=
  ⟨e.hasCoveringDimensionLE_of, e.symm.hasCoveringDimensionLE_of⟩

/-- Strict covering-dimension bounds are preserved by homeomorphisms. -/
protected theorem Homeomorph.hasCoveringDimensionLT
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (n : ℕ) : HasCoveringDimensionLT A n ↔ HasCoveringDimensionLT B n := by
  cases n with
  | zero => exact ⟨fun h ↦ Function.isEmpty e.symm, fun h ↦ Function.isEmpty e⟩
  | succ n => exact e.hasCoveringDimensionLE n

/-- Covering dimension is preserved by homeomorphisms. -/
protected theorem Homeomorph.coveringDimension_congr
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : coveringDimension A = coveringDimension B := by
  unfold coveringDimension
  apply congrArg sInf
  ext d
  exact forall_congr' fun n ↦ forall_congr' fun _ ↦ e.hasCoveringDimensionLT n
