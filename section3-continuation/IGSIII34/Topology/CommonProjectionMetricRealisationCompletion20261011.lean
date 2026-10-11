import IGSIII34.Topology.CommonTargetMetricCompactCompletion20261011
import IGSIII.Geometry.FiniteAnchorGluing
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
namespace IGSIII34.Topology
noncomputable section
open Metric Set Filter
open scoped _root_.Topology
universe u

/-- Finite projections with vanishing full distortion admit one compact
complete common realization by genuine isometric embeddings. Every
finite point approaches the embedded value of its given projection. -/
theorem exists_common_isometric_realisation_of_uniform_projection_distortion_completion20261011
    (Sources : ℕ → Type u) [∀ index, MetricSpace (Sources index)]
    [∀ index, Fintype (Sources index)] [∀ index, Nonempty (Sources index)]
    {Target : Type u} [MetricSpace Target] [CompactSpace Target] [Nonempty Target]
    (projections : ∀ index, Sources index → Target)
    (distortionVanish : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ first last, |dist first last - dist (projections index first) (projections index last)| < tolerance) :
    ∃ (Ambient : Type u) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ target : Target → Ambient, Isometry target ∧
      ∃ sources : ∀ index, Sources index → Ambient,
        (∀ index, Isometry (sources index)) ∧
        ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
          ∀ point, dist (sources index point) (target (projections index point)) < tolerance := by
  classical
  let errors : ℕ → ℝ := fun index =>
    Finset.univ.sup' Finset.univ_nonempty
      (fun pair : Sources index × Sources index =>
        |dist pair.1 pair.2 - dist (projections index pair.1) (projections index pair.2)|)
  have errorsNonnegative (index : ℕ) : 0 ≤ errors index := by
    let point := Classical.choice (inferInstance : Nonempty (Sources index))
    exact (abs_nonneg (dist point point - dist (projections index point) (projections index point))).trans
      (Finset.le_sup' (f := fun pair : Sources index × Sources index =>
        |dist pair.1 pair.2 - dist (projections index pair.1) (projections index pair.2)|)
        (Finset.mem_univ (point,point)))
  have errorsBound (index : ℕ) (first last : Sources index) :
      |dist first last - dist (projections index first) (projections index last)| ≤ errors index :=
    Finset.le_sup' (f := fun pair : Sources index × Sources index =>
      |dist pair.1 pair.2 - dist (projections index pair.1) (projections index pair.2)|)
      (Finset.mem_univ (first,last))
  have errorsVanish : Tendsto errors atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [distortionVanish tolerance positive] with index small
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (errorsNonnegative index)]
    exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun pair _ => small pair.1 pair.2)
  let radii : ℕ → ℝ := fun index => errors index + (index+1 : ℝ)⁻¹
  have radiiPositive (index : ℕ) : 0 < radii index := by
    have nonnegative := errorsNonnegative index
    dsimp only [radii]
    positivity
  have radiiVanish : Tendsto radii atTop (𝓝 0) := by
    have inverseVanish : Tendsto (fun index : ℕ => (index+1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using errorsVanish.add inverseVanish
  let Extensions := fun index => Sources index ⊕ Target
  let extensionMetrics : ∀ index, MetricSpace (Extensions index) := fun index =>
    glueMetricApprox (id : Sources index → Sources index) (projections index) (radii index) (radiiPositive index)
      (fun first last => (errorsBound index first last).trans (by
        have nonnegative := errorsNonnegative index
        have inverseNonnegative : 0 ≤ (index+1 : ℝ)⁻¹ := by positivity
        dsimp only [radii]
        linarith))
  letI : ∀ index, MetricSpace (Extensions index) := extensionMetrics
  let targetEmbedding := fun index => (@Sum.inr (Sources index) Target)
  have targetIsometry (index : ℕ) : Isometry (targetEmbedding index) :=
    Isometry.of_dist_eq (fun _ _ => rfl)
  have sourceIsometry (index : ℕ) : Isometry (@Sum.inl (Sources index) Target) :=
    Isometry.of_dist_eq (fun _ _ => rfl)
  have matched (index : ℕ) (point : Sources index) :
      dist (Sum.inl point : Extensions index) (Sum.inr (projections index point)) = radii index :=
    glueDist_glued_points (id : Sources index → Sources index) (projections index) (radii index) point
  letI : ∀ index, CompactSpace (Extensions index) := fun index => by
    have compact := (isCompact_range (sourceIsometry index).continuous).union
      (isCompact_range (targetIsometry index).continuous)
    have cover : Set.range (@Sum.inl (Sources index) Target) ∪ Set.range (@Sum.inr (Sources index) Target) = Set.univ := by
      ext point
      cases point <;> simp
    rw [cover] at compact
    exact isCompact_univ_iff.mp compact
  have extensionClose (index : ℕ) (point : Extensions index) :
      ∃ target, dist point (targetEmbedding index target) ≤ radii index := by
    cases point with
    | inl point => exact ⟨projections index point, (matched index point).le⟩
    | inr point => exact ⟨point, (dist_self _).le.trans (radiiPositive index).le⟩
  let Ambient := CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry
  letI : CompactSpace Ambient := commonTargetMetricAmbient_compact_completion20261011
    Extensions targetEmbedding targetIsometry radii radiiVanish extensionClose
  let target := commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry
  let sources := fun index => commonExtensionAmbientEmbeddingCompletion20261011
    Extensions targetEmbedding targetIsometry index ∘ (@Sum.inl (Sources index) Target)
  refine ⟨Ambient, inferInstance, inferInstance, inferInstance, target,
    commonTargetAmbientEmbedding_isometry_completion20261011 Extensions targetEmbedding targetIsometry,
    sources, fun index => (commonExtensionAmbientEmbedding_isometry_completion20261011
      Extensions targetEmbedding targetIsometry index).comp (sourceIsometry index), ?_⟩
  intro tolerance positive
  filter_upwards [radiiVanish.eventually (gt_mem_nhds positive)] with index small
  intro point
  change dist (commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index (Sum.inl point))
    (commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry (projections index point)) < tolerance
  rw [commonExtensionAmbientEmbedding_target_distance_completion20261011]
  exact (matched index point).trans_lt small

end
end IGSIII34.Topology
