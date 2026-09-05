/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.GeneralPosition
public import Mathlib.Topology.CoveringDimension.Euclidean
import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Separation.Hausdorff

/-! # Covering dimension and Euclidean embeddings -/

public section

open scoped CoveringDimension

universe u

/-- Helper for Theorem 50.4: a continuous map separates points at scale `δ` when
points at distance at least `δ` have distinct images. -/
def ContinuousMap.SeparatesAtScale {X E : Type*} [TopologicalSpace X]
    [PseudoMetricSpace X] [TopologicalSpace E] (δ : ℝ) (f : C(X, E)) : Prop :=
  ∀ x y, δ ≤ dist x y → f x ≠ f y

/-- Helper for Theorem 50.4: scale-separating continuous maps form an open set
for the uniform metric on maps from a compact pseudometric space. -/
lemma isOpen_setOf_separatesAtScale
    {X E : Type*} [PseudoMetricSpace X] [CompactSpace X] [MetricSpace E]
    {δ : ℝ} : IsOpen {f : C(X, E) | f.SeparatesAtScale δ} := by
  -- At a separating map, minimize image distance on the compact locus of pairs
  -- whose domain distance is at least the prescribed scale.
  rw [Metric.isOpen_iff]
  intro f hf
  let K : Set (X × X) := {p | δ ≤ dist p.1 p.2}
  have hK : IsCompact K := by
    have hKclosed : IsClosed {p : X × X | δ ≤ dist p.1 p.2} :=
      isClosed_le continuous_const continuous_dist
    exact hKclosed.isCompact
  by_cases hKne : K.Nonempty
  · let d : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
    have hd_cont : Continuous d :=
      (f.continuous.comp continuous_fst).dist (f.continuous.comp continuous_snd)
    obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hKne hd_cont.continuousOn
    have hdp : 0 < d p := by
      exact dist_pos.mpr (hf p.1 p.2 hpK)
    refine ⟨d p / 3, by positivity, ?_⟩
    intro g hgf x y hxy hgeq
    have hxyK : (x, y) ∈ K := hxy
    have hmin : d p ≤ d (x, y) := hpmin hxyK
    have hgf_dist : dist f g < d p / 3 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hgf
    have hgx : dist (f x) (g x) < d p / 3 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) hgf_dist
    have hgy : dist (g y) (f y) < d p / 3 := by
      rw [dist_comm]
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist y) hgf_dist
    -- A perturbation smaller than one third of the minimum cannot identify a
    -- pair from the scale-separated locus.
    have hbound : d (x, y) < d p / 3 + 0 + d p / 3 := by
      calc
        d (x, y) = dist (f x) (f y) := rfl
        _ ≤ dist (f x) (g x) + dist (g x) (g y) + dist (g y) (f y) :=
          dist_triangle4 _ _ _ _
        _ = dist (f x) (g x) + 0 + dist (g y) (f y) := by
          rw [hgeq, dist_self]
        _ < d p / 3 + 0 + d p / 3 := by
          gcongr
    linarith
  · -- If there are no pairs at this scale, every map separates vacuously.
    have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    refine ⟨1, by norm_num, ?_⟩
    intro g _ x y hxy
    have hxyK : (x, y) ∈ K := hxy
    rw [hKempty] at hxyK
    exact hxyK.elim

/-- Helper for Theorem 50.4: the active part of a finite subfamily has cardinality
bounded by the corresponding pointwise `encard` bound on the ambient family. -/
private lemma card_filter_mem_le_of_subfamily
    {α : Type*} (s : Finset α) (𝒜 : Set α) (p : α → Prop) [DecidablePred p]
    {k : ℕ} (hs : ∀ a ∈ s, a ∈ 𝒜) (hcard : Set.encard {a ∈ 𝒜 | p a} ≤ k) :
    (s.filter p).card ≤ k := by
  -- Regard the filtered finset as a set and compare it with the ambient active family.
  have hsubset : (s.filter p : Set α) ⊆ {a ∈ 𝒜 | p a} := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact ⟨hs a ha'.1, ha'.2⟩
  have hencard := (Set.encard_mono hsubset).trans hcard
  -- The `encard` of a finset coercion is its ordinary finite cardinality.
  simpa only [Set.encard_coe_eq_coe_finsetCard, ENat.natCast_le_natCast] using hencard

open scoped Classical in
/-- Helper for Theorem 50.4: covering dimension supplies a finite open cover
whose members are small both in the domain and under a prescribed map. -/
private lemma existsFiniteControlledOpenCover
    {X E : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace E]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (f : C(X, E))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ s : Finset (Set X),
      (∀ U ∈ s, IsOpen U) ∧
      (∀ U ∈ s, U.Nonempty) ∧
      (∀ x, ∃ U ∈ s, x ∈ U) ∧
      (∀ x, (s.filter fun U ↦ x ∈ U).card ≤ m + 1) ∧
      (∀ U ∈ s, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ) ∧
      (∀ U ∈ s, ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) < η) := by
  classical
  -- The canonical cover controls domain distance and image distance simultaneously.
  let neighborhood : X → Set X := fun x ↦
    Metric.ball x (δ / 2) ∩ f ⁻¹' Metric.ball (f x) (η / 2)
  let 𝒜 : Set (Set X) := Set.range neighborhood
  have h𝒜_open : ∀ U ∈ 𝒜, IsOpen U := by
    rintro U ⟨x, rfl⟩
    exact Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage f.continuous)
  have h𝒜_cover : ⋃₀ 𝒜 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    refine ⟨neighborhood x, ⟨x, rfl⟩, ?_⟩
    constructor
    · exact Metric.mem_ball.mpr (by simpa using hδ)
    · exact Metric.mem_ball.mpr (by simpa using hη)
  obtain ⟨ℬ, hℬ_refines, hℬ_open, hℬ_cover, hℬ_order⟩ :=
    (hasCoveringDimensionLE_iff X m).mp hdim 𝒜 h𝒜_open h𝒜_cover
  have hℬ_subcover : Set.univ ⊆ ⋃ U : ℬ, U.1 := by
    intro x _
    have hx : x ∈ ⋃₀ ℬ := by
      rw [hℬ_cover]
      exact Set.mem_univ x
    rw [Set.mem_sUnion] at hx
    obtain ⟨U, hUℬ, hxU⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hUℬ⟩, hxU⟩
  obtain ⟨t, ht_cover⟩ := isCompact_univ.elim_finite_subcover
    (fun U : ℬ ↦ U.1) (fun U ↦ hℬ_open U.1 U.2) hℬ_subcover
  let s : Finset (Set X) := (t.filter fun U : ℬ ↦ U.1.Nonempty).image Subtype.val
  refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Every selected member came from the open refinement.
    intro U hUs
    rw [Finset.mem_image] at hUs
    obtain ⟨V, hVt, rfl⟩ := hUs
    exact hℬ_open V.1 V.2
  · -- Empty members were discarded explicitly.
    intro U hUs
    rw [Finset.mem_image] at hUs
    obtain ⟨V, hVt, rfl⟩ := hUs
    exact (Finset.mem_filter.mp hVt).2
  · -- The retained nonempty members still cover, since the member containing a
    -- given point is automatically nonempty.
    intro x
    have hx : x ∈ ⋃ U ∈ t, U.1 := ht_cover (Set.mem_univ x)
    rw [Set.mem_iUnion] at hx
    obtain ⟨V, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hVt, hxV⟩ := hx
    refine ⟨V.1, ?_, hxV⟩
    rw [Finset.mem_image]
    exact ⟨V, Finset.mem_filter.mpr ⟨hVt, ⟨x, hxV⟩⟩, rfl⟩
  · -- Point multiplicity can only decrease when passing to the finite subfamily.
    intro x
    apply card_filter_mem_le_of_subfamily s ℬ (fun U ↦ x ∈ U)
    · intro U hUs
      rw [Finset.mem_image] at hUs
      obtain ⟨V, _, rfl⟩ := hUs
      exact V.2
    · exact Set.hasOrderLE_iff.mp hℬ_order x
  · -- Refinement into one canonical neighborhood gives the domain estimate.
    intro U hUs x hxU y hyU
    have hUℬ : U ∈ ℬ := by
      rw [Finset.mem_image] at hUs
      obtain ⟨V, _, rfl⟩ := hUs
      exact V.2
    obtain ⟨A, ⟨z, rfl⟩, hUA⟩ := hℬ_refines hUℬ
    have hxz : dist x z < δ / 2 := Metric.mem_ball.mp (hUA hxU).1
    have hzy : dist z y < δ / 2 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp (hUA hyU).1
    exact lt_of_le_of_lt (dist_triangle x z y) (by linarith)
  · -- The same refinement estimate in the codomain controls image oscillation.
    intro U hUs x hxU y hyU
    have hUℬ : U ∈ ℬ := by
      rw [Finset.mem_image] at hUs
      obtain ⟨V, _, rfl⟩ := hUs
      exact V.2
    obtain ⟨A, ⟨z, rfl⟩, hUA⟩ := hℬ_refines hUℬ
    have hxz : dist (f x) (f z) < η / 2 := Metric.mem_ball.mp (hUA hxU).2
    have hzy : dist (f z) (f y) < η / 2 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp (hUA hyU).2
    exact lt_of_le_of_lt (dist_triangle (f x) (f z) (f y)) (by linarith)

/-- Helper for Theorem 50.4: a finite open cover admits a subordinate partition
of unity indexed by the subtype of its members. -/
private lemma existsSubordinatePartitionOfUnityForFinset
    {X : Type*} [MetricSpace X] [CompactSpace X] (s : Finset (Set X))
    (hopen : ∀ U ∈ s, IsOpen U) (hcover : ∀ x, ∃ U ∈ s, x ∈ U) :
    ∃ ρ : PartitionOfUnity {U : Set X // U ∈ s} X Set.univ,
      ρ.IsSubordinate fun U ↦ U.1 := by
  -- Compact metric spaces provide the normal and paracompact instances required
  -- by the standard subordinate-partition theorem.
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ
  · intro U
    exact hopen U.1 U.2
  · intro x _
    obtain ⟨U, hUs, hxU⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨⟨U, hUs⟩, hxU⟩

open scoped Classical in
/-- Helper for Theorem 50.4: the active coefficients of a subordinate finite
partition are bounded by the point multiplicity of the cover. -/
private lemma activePartitionIndices_card_le
    {X : Type*} [TopologicalSpace X] {m : ℕ} (s : Finset (Set X))
    (hmult : ∀ x, (s.filter fun U ↦ x ∈ U).card ≤ m + 1)
    (ρ : PartitionOfUnity {U : Set X // U ∈ s} X Set.univ)
    (hρ : ρ.IsSubordinate fun U ↦ U.1) (x : X) :
    (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤ m + 1 := by
  classical
  -- Send each active subtype index to its underlying cover member; subordination
  -- places the image in the pointwise active cover finset.
  have hcard :
      (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤
        (s.filter fun U ↦ x ∈ U).card := by
    apply Finset.card_le_card_of_injOn (fun i ↦ i.1)
    · intro i hi
      have hi_active : ρ i x ≠ 0 := by simpa using hi
      exact Finset.mem_filter.mpr
        ⟨i.2, hρ i (subset_tsupport (ρ i) hi_active)⟩
    · intro i hi j hj hij
      exact Subtype.ext hij
  exact hcard.trans (hmult x)

open scoped Classical in
/-- Helper for Theorem 50.4: the barycentric map is uniformly close when every
active vertex is pointwise close to the reference map. -/
private lemma barycentricMap_close
    {X E ι : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : PartitionOfUnity ι X Set.univ) (f g : C(X, E)) (z : ι → E) {r : ℝ}
    (hg : ∀ x, g x = ∑ i, ρ i x • z i)
    (hz : ∀ i x, ρ i x ≠ 0 → dist (z i) (f x) < r) :
    dist g f < r := by
  classical
  -- Apply the weighted-average estimate pointwise and then use the uniform metric.
  apply ContinuousMap.dist_lt_of_nonempty
  intro x
  rw [hg x]
  simpa only [finsum_eq_sum_of_fintype, Metric.mem_ball] using
    ρ.finsum_smul_mem_convex (g := fun i _ ↦ z i) (Set.mem_univ x)
      (fun i hi ↦ Metric.mem_ball.mpr (hz i x hi))
      (convex_ball (f x) r)

open scoped Classical in
/-- Helper for Theorem 50.4: bounded affine independence of the vertices makes
the associated barycentric map separate points at the controlled scale. -/
private lemma barycentricMap_separatesAtScale
    {X ι E : Type*} [PseudoMetricSpace X] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : PartitionOfUnity ι X Set.univ) (U : ι → Set X)
    (hρ : ρ.IsSubordinate U) (z : ι → E) (g : C(X, E))
    {m : ℕ} {δ : ℝ}
    (hg : ∀ x, g x = ∑ i, ρ i x • z i)
    (hactive : ∀ x, (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤ m + 1)
    (haff : ∀ t : Finset ι, t.card ≤ 2 * m + 2 →
      AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1))
    (hdomain : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, dist x y < δ) :
    g.SeparatesAtScale δ := by
  classical
  intro x y hxy hgeq
  let t := (Finset.univ.filter fun i ↦ ρ i x ≠ 0) ∪
    (Finset.univ.filter fun i ↦ ρ i y ≠ 0)
  have htcard : t.card ≤ 2 * m + 2 := by
    calc
      t.card ≤ _ := Finset.card_union_le _ _
      _ ≤ (m + 1) + (m + 1) := Nat.add_le_add (hactive x) (hactive y)
      _ = 2 * m + 2 := by omega
  have hx_support : ∀ i, ρ i x ≠ 0 → i ∈ t := by
    intro i hi
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hy_support : ∀ i, ρ i y ≠ 0 → i ∈ t := by
    intro i hi
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  -- Restrict both barycentric expressions to the active union and use affine
  -- independence to identify every coefficient.
  have hsum (a : X) (ha : ∀ i, ρ i a ≠ 0 → i ∈ t) :
      (∑ i : {i // i ∈ t}, ρ i.1 a) = 1 := by
    calc
      (∑ i : {i // i ∈ t}, ρ i.1 a) = ∑ i, ρ i a :=
        Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
          (by simpa using fun i hi ↦ not_ne_iff.mp (mt (ha i) hi)) (fun _ ↦ rfl)
      _ = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ a)
  have hweighted_sum (a : X) (ha : ∀ i, ρ i a ≠ 0 → i ∈ t) :
      (∑ i : {i // i ∈ t}, ρ i.1 a • z i.1) = g a := by
    rw [hg a]
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (by simpa using fun i hi ↦ by simp [not_ne_iff.mp (mt (ha i) hi)]) (fun _ ↦ rfl)
  have hweighted :
      (∑ i : {i // i ∈ t}, ρ i.1 x • z i.1) =
        ∑ i : {i // i ∈ t}, ρ i.1 y • z i.1 := by
    rw [hweighted_sum x hx_support, hweighted_sum y hy_support, hgeq]
  have hcoeff_on_t : ∀ i : {i // i ∈ t}, ρ i.1 x = ρ i.1 y := by
    intro i
    exact (haff t htcard).eq_of_sum_eq_sum (s := Finset.univ)
      (by rw [hsum x hx_support, hsum y hy_support]) hweighted i (Finset.mem_univ i)
  have hcoeff : ∀ i, ρ i x = ρ i y := by
    intro i
    by_cases hix : ρ i x = 0
    · by_cases hiy : ρ i y = 0
      · rw [hix, hiy]
      · have hi : i ∈ t := hy_support i hiy
        have := hcoeff_on_t ⟨i, hi⟩
        exact (hix ▸ this)
    · exact hcoeff_on_t ⟨i, hx_support i hix⟩
  -- A positive coefficient exists; its cover member contains both points.
  obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ x)
  have hixU : x ∈ U i := hρ i (subset_tsupport (ρ i) (ne_of_gt hi))
  have hiyU : y ∈ U i := by
    have hiy : ρ i y ≠ 0 := hcoeff i ▸ ne_of_gt hi
    exact hρ i (subset_tsupport (ρ i) hiy)
  exact (not_lt_of_ge hxy) (hdomain i x hixU y hiyU)

/-- Helper for Theorem 50.4: on a nonempty compact metric space of covering
dimension at most `m`, reciprocal-scale separating Euclidean maps are dense. -/
lemma dense_setOf_separatesAtScale_of_nonempty
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (n : ℕ) :
    Dense {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      f.SeparatesAtScale (1 / (n + 1 : ℝ))} := by
  rw [Metric.dense_iff]
  intro f r hr
  have hscale : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hrhalf : 0 < r / 2 := by positivity
  -- First freeze one finite cover controlling both the separation scale and
  -- the image oscillation allowed by the target uniform ball.
  obtain ⟨s, hopen, hnonempty, hcover, hmult, hdomain, himage⟩ :=
    existsFiniteControlledOpenCover hdim f hscale hrhalf
  -- Use the cover-member subtype as the single finite index type for all
  -- subsequent representatives, vertices, and barycentric coefficients.
  obtain ⟨ρ, hρ⟩ := existsSubordinatePartitionOfUnityForFinset s hopen hcover
  have hactive : ∀ x,
      (Finset.univ.filter fun i ↦ ρ i x ≠ 0).card ≤ m + 1 := by
    intro x
    exact activePartitionIndices_card_le s hmult ρ hρ x
  classical
  -- Choose one representative in every nonempty cover member and perturb its
  -- image to the bounded affine-independent vertex family supplied above.
  let a : {U : Set X // U ∈ s} → X := fun i ↦ Classical.choose (hnonempty i.1 i.2)
  have ha_mem : ∀ i, a i ∈ i.1 := fun i ↦ Classical.choose_spec (hnonempty i.1 i.2)
  obtain ⟨z, hz_close, hz_affine⟩ :=
    Theorem50_4.existsNearbyBoundedAffineIndependentFamily (fun i ↦ f (a i)) hrhalf
  have hz_affine' : ∀ t : Finset {U : Set X // U ∈ s}, t.card ≤ 2 * m + 2 →
      AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
    intro t ht
    apply hz_affine t
    omega
  -- Form the finite barycentric sum as a continuous map.
  let g : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun x ↦ ∑ i, ρ i x • z i,
      continuous_finsetSum _ fun i _ ↦ (ρ i).continuous.smul continuous_const⟩
  have hg : ∀ x, g x = ∑ i, ρ i x • z i := fun _ ↦ rfl
  -- An active coefficient places `x` in the same controlled cover member as
  -- its representative, so the vertex and `f x` are less than `r` apart.
  have hz_pointwise : ∀ i x, ρ i x ≠ 0 → dist (z i) (f x) < r := by
    intro i x hix
    have hxU : x ∈ i.1 :=
      hρ i (subset_tsupport (ρ i) hix)
    calc
      dist (z i) (f x) ≤ dist (z i) (f (a i)) + dist (f (a i)) (f x) :=
        dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hz_close i)
        (himage i.1 i.2 (a i) (ha_mem i) x hxU)
      _ = r := by ring
  refine ⟨g, Metric.mem_ball.mpr ?_, ?_⟩
  · -- The weighted-average estimate gives the required uniform approximation.
    exact barycentricMap_close ρ f g z hg hz_pointwise
  · -- Coefficient uniqueness on the union of two active supports gives scale separation.
    exact barycentricMap_separatesAtScale ρ (fun U ↦ U.1) hρ z g hg hactive hz_affine'
      (fun i ↦ hdomain i.1 i.2)

/-- Helper for Theorem 50.4: at every positive reciprocal scale, the separating
continuous maps form an open dense subset of the uniform-metric function space. -/
lemma isOpen_dense_setOf_separatesAtScale
    {X : Type u} [MetricSpace X] [CompactSpace X]
    {m : ℕ} (hdim : HasCoveringDimensionLE X m) (n : ℕ) :
    IsOpen {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      f.SeparatesAtScale (1 / (n + 1 : ℝ))} ∧
    Dense {f : C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) |
      f.SeparatesAtScale (1 / (n + 1 : ℝ))} := by
  -- Openness is the generic compact-domain perturbation result above.
  constructor
  · exact isOpen_setOf_separatesAtScale
  -- Density is vacuous on the empty domain and is the geometric approximation
  -- construction isolated in `dense_setOf_separatesAtScale_of_nonempty` otherwise.
  · cases isEmpty_or_nonempty X with
    | inl hX =>
        let _ : IsEmpty X := hX
        rw [Metric.dense_iff]
        intro f r hr
        refine ⟨f, Metric.mem_ball.mpr ?_, ?_⟩
        · rw [dist_self]
          exact hr
        · intro x
          exact isEmptyElim x
    | inr hX =>
        let _ : Nonempty X := hX
        exact dense_setOf_separatesAtScale_of_nonempty hdim n

/-- Helper for Theorem 50.4: separation at every reciprocal scale forces a map to
be injective. -/
lemma Function.Injective.of_separatesAtAllReciprocalScales
    {X E : Type*} [MetricSpace X] [TopologicalSpace E]
    (f : C(X, E))
    (hf : ∀ n : ℕ, f.SeparatesAtScale (1 / (n + 1 : ℝ))) : Function.Injective f := by
  -- Distinct points have positive distance, so some reciprocal scale lies below it.
  intro x y hxy
  by_contra hne
  have hdist : 0 < dist x y := dist_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdist
  exact hf n x y hn.le hxy

/-- A compact metrizable space of covering dimension at most `m` embeds in
`EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem existsEuclideanEmbedding_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] {m : ℕ}
    (hdim : HasCoveringDimensionLE X m) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsEmbedding f := by
  -- Use a compatible metric once, so compact continuous maps carry the uniform metric.
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let separatingMaps : ℕ → Set C(X, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    fun n ↦ {f | f.SeparatesAtScale (1 / (n + 1 : ℝ))}
  have hopen : ∀ n, IsOpen (separatingMaps n) := by
    intro n
    exact (isOpen_dense_setOf_separatesAtScale hdim n).1
  have hdense : ∀ n, Dense (separatingMaps n) := by
    intro n
    exact (isOpen_dense_setOf_separatesAtScale hdim n).2
  -- Baire's theorem supplies one continuous map separating at every reciprocal scale.
  obtain ⟨f, hf⟩ := (BaireSpace.baire_property separatingMaps hopen hdense).nonempty
  have hfscales : ∀ n : ℕ, f.SeparatesAtScale (1 / (n + 1 : ℝ)) := by
    intro n
    exact Set.mem_iInter.mp hf n
  have hinj : Function.Injective f :=
    Function.Injective.of_separatesAtAllReciprocalScales f hfscales
  -- A continuous injection from a compact space to a Hausdorff space is an embedding.
  exact ⟨f, (f.continuous.isClosedEmbedding hinj).isEmbedding⟩

/-- Theorem 50.4. Every compact metrizable space of covering dimension `m` embeds in
`EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem existsEuclideanEmbedding_of_coveringDimension_eq
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (m : ℕ)
    (hdim : dim X = (m : ℕ∞)) :
    ∃ f : X → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsEmbedding f := by
  apply existsEuclideanEmbedding_of_hasCoveringDimensionLE
  rw [← coveringDimension_le_iff]
  exact le_of_eq hdim

/-! ### Finite covering dimension and Euclidean embeddings -/

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
