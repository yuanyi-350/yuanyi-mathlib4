/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Basic
import Mathlib.Data.Fintype.Lattice

/-! # Covering dimension of finite unions of closed subspaces -/

public section

open scoped CoveringDimension

universe u v

/-- Helper for Theorem 50.2: an open cover can be refined with controlled order at
the points of a closed subspace whose covering dimension is bounded. -/
private lemma existsOpenRefinementWithOrderOnClosedSet
    {X : Type u} [TopologicalSpace X] {S : Set X} {n : ℕ}
    (hSclosed : IsClosed S) (hSdim : HasCoveringDimensionLE S n)
    (𝒜 : Set (Set X)) (h𝒜open : ∀ A ∈ 𝒜, IsOpen A)
    (h𝒜cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X),
      IsCofinalFor ℬ 𝒜 ∧ (∀ B ∈ ℬ, IsOpen B) ∧ ⋃₀ ℬ = Set.univ ∧
        ∀ s : S, Set.encard {B ∈ ℬ | s.1 ∈ B} ≤ (n + 1 : ℕ) := by
  classical
  -- Restrict the ambient cover to `S` and use its covering-dimension bound there.
  let traceCover : Set (Set S) :=
    (fun A : Set X ↦ ((↑) : S → X) ⁻¹' A) '' 𝒜
  have htraceOpen : ∀ A ∈ traceCover, IsOpen A := by
    rintro A ⟨U, hU, rfl⟩
    exact (h𝒜open U hU).preimage continuous_subtype_val
  have htraceCover : ⋃₀ traceCover = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    have hs : s.1 ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ s.1
    rw [Set.mem_sUnion] at hs ⊢
    obtain ⟨A, hA, hsA⟩ := hs
    exact ⟨((↑) : S → X) ⁻¹' A, ⟨A, hA, rfl⟩, hsA⟩
  obtain ⟨traceRefinement, hrefines, hrefinementOpen, hrefinementCover, hrefinementOrder⟩ :=
    (hasCoveringDimensionLE_iff S n).mp hSdim traceCover htraceOpen htraceCover
  -- Choose an original parent and an ambient open representative for each trace member.
  have hparentExists (B : traceRefinement) :
      ∃ A : 𝒜, (B.1 : Set S) ⊆ ((↑) : S → X) ⁻¹' (A.1 : Set X) := by
    obtain ⟨T, hT, hBT⟩ := hrefines B.2
    obtain ⟨A, hA, rfl⟩ := hT
    exact ⟨⟨A, hA⟩, hBT⟩
  choose parent hparent using hparentExists
  have hambientExists (B : traceRefinement) :
      ∃ U : Set X, IsOpen U ∧ ((↑) : S → X) ⁻¹' U = (B.1 : Set S) := by
    exact isOpen_induced_iff.mp (hrefinementOpen B.1 B.2)
  choose ambient hambientOpen hambientTrace using hambientExists
  let extended : traceRefinement → Set X :=
    fun B ↦ ambient B ∩ (parent B : Set X)
  let outside : 𝒜 → Set X := fun A ↦ (A : Set X) \ S
  let ℬ : Set (Set X) := Set.range (Sum.elim extended outside)
  refine ⟨ℬ, ?_, ?_, ?_, ?_⟩
  · -- Intersecting with the chosen parent preserves openness and refinement.
    rintro V ⟨j, rfl⟩
    cases j with
    | inl B =>
        exact ⟨parent B, (parent B).2, Set.inter_subset_right⟩
    | inr A =>
        exact ⟨A, A.2, Set.sdiff_subset⟩
  · rintro V ⟨j, rfl⟩
    cases j with
    | inl B =>
        exact (hambientOpen B).inter (h𝒜open (parent B) (parent B).2)
    | inr A =>
        exact (h𝒜open A A.2).sdiff hSclosed
  · -- Trace members cover `S`, while the original members minus `S` cover its complement.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    by_cases hxS : x ∈ S
    · let s : S := ⟨x, hxS⟩
      have hs : s ∈ ⋃₀ traceRefinement :=
        hrefinementCover.symm ▸ Set.mem_univ s
      rw [Set.mem_sUnion] at hs
      obtain ⟨B, hB, hsB⟩ := hs
      let j : traceRefinement := ⟨B, hB⟩
      have hsAmbient : x ∈ ambient j := by
        have hsPreimage : s ∈ ((↑) : S → X) ⁻¹' ambient j := by
          rw [hambientTrace j]
          exact hsB
        exact hsPreimage
      have hsParent : x ∈ (parent j : Set X) := hparent j hsB
      exact ⟨extended j, ⟨Sum.inl j, rfl⟩, hsAmbient, hsParent⟩
    · have hx : x ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ x
      rw [Set.mem_sUnion] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      let j : 𝒜 := ⟨A, hA⟩
      exact ⟨outside j, ⟨Sum.inr j, rfl⟩, hxA, hxS⟩
  · -- At a point of `S`, outside members disappear and each remaining member has one trace.
    intro s
    let source : Set traceRefinement := {B | s ∈ (B.1 : Set S)}
    have hsub : {V ∈ ℬ | s.1 ∈ V} ⊆ extended '' source := by
      intro V hV
      obtain ⟨j, rfl⟩ := hV.1
      cases j with
      | inl B =>
          have hsTrace : s ∈ (B.1 : Set S) := by
            rw [← hambientTrace B]
            exact hV.2.1
          exact ⟨B, hsTrace, rfl⟩
      | inr A =>
          exact (hV.2.2 s.2).elim
    have hsourceImage :
        ((fun B : traceRefinement ↦ (B.1 : Set S)) '' source) =
          {B ∈ traceRefinement | s ∈ B} := by
      ext B
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.2, hj⟩
      · intro hB
        exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
    calc
      Set.encard {V ∈ ℬ | s.1 ∈ V}
          ≤ Set.encard (extended '' source) := Set.encard_le_encard hsub
      _ ≤ Set.encard source := Set.encard_image_le extended source
      _ = Set.encard {B ∈ traceRefinement | s ∈ B} := by
        rw [← hsourceImage, Subtype.val_injective.encard_image]
      _ ≤ n + 1 := (Set.hasOrderLE_iff.mp hrefinementOrder) s

namespace HasCoveringDimensionLE

/-- Helper for Theorem 50.2: a common covering-dimension bound on two closed
subspaces covering `X` is also a bound on `X`. -/
theorem unionClosed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (hYclosed : IsClosed Y) (hZclosed : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    (hYdim : HasCoveringDimensionLE Y n)
    (hZdim : HasCoveringDimensionLE Z n) :
    HasCoveringDimensionLE X n := by
  classical
  rw [hasCoveringDimensionLE_iff]
  intro 𝒜 h𝒜open h𝒜cover
  -- First control multiplicity on `Y`, then refine once more to control it on `Z`.
  obtain ⟨ℬ, hℬrefines, hℬopen, hℬcover, hℬorderY⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hYclosed hYdim 𝒜 h𝒜open h𝒜cover
  obtain ⟨𝒞, h𝒞refines, h𝒞open, h𝒞cover, h𝒞orderZ⟩ :=
    existsOpenRefinementWithOrderOnClosedSet hZclosed hZdim ℬ
      hℬopen hℬcover
  have hparentExists (C : 𝒞) :
      ∃ B : ℬ, (C.1 : Set X) ⊆ (B.1 : Set X) := by
    obtain ⟨B, hB, hCB⟩ := h𝒞refines C.2
    exact ⟨⟨B, hB⟩, hCB⟩
  choose parent hparent using hparentExists
  -- Group all second-stage members having the same first-stage parent.
  let grouped : ℬ → Set X := fun B ↦
    ⋃ C : {C : 𝒞 // parent C = B}, (C.1.1 : Set X)
  let 𝒟 : Set (Set X) := Set.range grouped
  have h𝒟refinesℬ : IsCofinalFor 𝒟 ℬ := by
    rintro D ⟨B, rfl⟩
    refine ⟨B, B.2, ?_⟩
    intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    rw [← C.2]
    exact hparent C.1 hxC
  have h𝒟open : ∀ D ∈ 𝒟, IsOpen D := by
    rintro D ⟨B, rfl⟩
    apply isOpen_iUnion
    intro C
    exact h𝒞open C.1.1 C.1.2
  refine ⟨𝒟, h𝒟refinesℬ.trans hℬrefines, h𝒟open, ?_, ?_⟩
  · -- Each second-stage member lies in the group indexed by its chosen parent.
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ 𝒞 := h𝒞cover.symm ▸ Set.mem_univ x
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨C, hC, hxC⟩ := hx
    let j : 𝒞 := ⟨C, hC⟩
    have hxGrouped : x ∈ grouped (parent j) := by
      rw [Set.mem_iUnion]
      exact ⟨⟨j, rfl⟩, hxC⟩
    exact ⟨grouped (parent j), ⟨parent j, rfl⟩, hxGrouped⟩
  · -- Over `Y` count parents; over `Z` count chosen second-stage witnesses.
    rw [Set.hasOrderLE_iff]
    intro x
    have hxYZ : x ∈ Y ∪ Z := hcover.symm ▸ Set.mem_univ x
    rcases hxYZ with hxY | hxZ
    · let y : Y := ⟨x, hxY⟩
      let source : Set ℬ := {B | x ∈ (B.1 : Set X)}
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ grouped '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        have hxB : x ∈ (B.1 : Set X) := by
          rw [← C.2]
          exact hparent C.1 hxC
        exact ⟨B, hxB, rfl⟩
      have hsourceImage :
          ((fun B : ℬ ↦ (B.1 : Set X)) '' source) =
            {B ∈ ℬ | x ∈ B} := by
        ext B
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hB
          exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (grouped '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le grouped source
        _ = Set.encard {B ∈ ℬ | x ∈ B} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := hℬorderY y
    · let z : Z := ⟨x, hxZ⟩
      let source : Set 𝒞 := {C | x ∈ (C.1 : Set X)}
      let groupOf : 𝒞 → Set X := fun C ↦ grouped (parent C)
      have hsub : {D ∈ 𝒟 | x ∈ D} ⊆ groupOf '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        refine ⟨C.1, hxC, ?_⟩
        exact congrArg grouped C.2
      have hsourceImage :
          ((fun C : 𝒞 ↦ (C.1 : Set X)) '' source) =
            {C ∈ 𝒞 | x ∈ C} := by
        ext C
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hC
          exact ⟨⟨C, hC.1⟩, hC.2, rfl⟩
      calc
        Set.encard {D ∈ 𝒟 | x ∈ D}
            ≤ Set.encard (groupOf '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le groupOf source
        _ = Set.encard {C ∈ 𝒞 | x ∈ C} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := h𝒞orderZ z

end HasCoveringDimensionLE

/-- Theorem 50.2. If two closed subspaces cover `X`, then the covering dimension
of `X` is the maximum of their covering dimensions. -/
theorem coveringDimension_union_closed
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hY : IsClosed Y) (hZ : IsClosed Z) (hcover : Y ∪ Z = Set.univ) :
    dim X = max (dim Y) (dim Z) := by
  refine eq_of_forall_ge_iff fun d ↦ ?_
  cases d with
  | bot =>
      rw [le_bot_iff, le_bot_iff, max_eq_bot, coveringDimension_eq_bot_iff,
        coveringDimension_eq_bot_iff, coveringDimension_eq_bot_iff]
      constructor
      · intro hX
        exact ⟨⟨fun y ↦ hX.false y.1⟩, ⟨fun z ↦ hX.false z.1⟩⟩
      · rintro ⟨hYempty, hZempty⟩
        refine ⟨fun x ↦ ?_⟩
        rcases (show x ∈ Y ∪ Z from hcover.symm ▸ Set.mem_univ x) with hx | hx
        · exact hYempty.false ⟨x, hx⟩
        · exact hZempty.false ⟨x, hx⟩
  | coe d =>
      cases d with
      | top => simp
      | coe n =>
          change dim X ≤ (n : WithBot ℕ∞) ↔ max (dim Y) (dim Z) ≤ (n : WithBot ℕ∞)
          rw [max_le_iff, coveringDimension_le_iff, coveringDimension_le_iff,
            coveringDimension_le_iff]
          exact ⟨fun h ↦ ⟨h.closedSubtype hY, h.closedSubtype hZ⟩,
            fun h ↦ HasCoveringDimensionLE.unionClosed hY hZ hcover h.1 h.2⟩

/-! ### Finite closed unions -/

/-- Helper for Corollary 50.3: the covering dimension of the union of two
closed subsets is the maximum of their covering dimensions. -/
private lemma coveringDimension_closedUnion
    {X : Type u} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsClosed T) :
    dim (S ∪ T : Set X) = max (dim S) (dim T) := by
  -- Apply Theorem 50.2 inside the union subtype and hide its nested-subtype pieces.
  let U : Set X := S ∪ T
  let S' : Set U := (Subtype.val : U → X) ⁻¹' S
  let T' : Set U := (Subtype.val : U → X) ⁻¹' T
  have hS' : IsClosed S' := hS.preimage continuous_subtype_val
  have hT' : IsClosed T' := hT.preimage continuous_subtype_val
  have hcover : S' ∪ T' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases x.2 with hxS | hxT
    · exact Or.inl hxS
    · exact Or.inr hxT
  have hSsub : S ⊆ U := Set.subset_union_left
  have hTsub : T ⊆ U := Set.subset_union_right
  calc
    dim (S ∪ T : Set X) = dim U := rfl
    _ = max (dim S') (dim T') := coveringDimension_union_closed hS' hT' hcover
    _ = max (dim S) (dim T) := congrArg₂ max
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hSsub)).coveringDimension_congr
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using hTsub)).coveringDimension_congr

/-- Helper for Corollary 50.3: covering dimension turns a finite union of
closed subsets into the finite supremum of their dimensions. -/
private lemma coveringDimension_finset_iUnion_closed
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (Y : I → Set X) (s : Finset I) (hclosed : ∀ i ∈ s, IsClosed (Y i)) :
    dim (⋃ i ∈ s, Y i) = s.sup fun i ↦ dim (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sup_insert]
      have hs : ∀ i ∈ s, IsClosed (Y i) := fun i hi ↦ hclosed i (Finset.mem_insert_of_mem hi)
      rw [coveringDimension_closedUnion (hclosed a (Finset.mem_insert_self _ _))
        (isClosed_biUnion_finset hs), ih hs]

/-- The covering dimension of a finite union of closed subsets is the supremum of their
covering dimensions. -/
theorem coveringDimension_iUnion_of_isClosed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i)) :
    dim (⋃ i, Y i) = ⨆ i, dim (Y i) := by
  let _ := Fintype.ofFinite ι
  have hunion : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = ⋃ i, Y i := by simp
  rw [← hunion, coveringDimension_finset_iUnion_closed Y Finset.univ (fun i _ ↦ hclosed i),
    Finset.sup_univ_eq_iSup]

/-- Corollary 50.3. The covering dimension of a finite closed cover is the
maximum of the covering dimensions of its members. -/
theorem coveringDimension_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ) :
    dim X = Finset.univ.sup fun i ↦ dim (Y i) := by
  rw [Finset.sup_univ_eq_iSup, ← coveringDimension_iUnion_of_isClosed Y hclosed, hcover]
  exact (Homeomorph.Set.univ X).coveringDimension_congr.symm

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
  rw [← coveringDimension_le_iff, coveringDimension_iUnion_of_isClosed Y hclosed, iSup_le_iff]
  exact fun i ↦ (coveringDimension_le_iff (Y i) n).mpr (hdim i)

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
