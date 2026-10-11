import IGSIII34.ResistanceLimit.ActualFiniteAnnealedProfileConvergence
import IGSIII34.Diffusion.DistanceProfileUniformApproximation
import IGSIII34.Diffusion.CountableDistanceProfileCadlagWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (classicalRule : rule.Classical)
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
  (scale : ℝ) (scalePositive : 0 < scale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))


variable {Ambient : Type*} [MetricSpace Ambient]
  (target : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence → Ambient)
  (targetIsometry : Isometry target)
  (sources : ∀ depth, ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    scale scalePositive depth → Ambient)
  (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
    dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths
      nonnegative positive childConvergence depth vertex)) < tolerance)

include crossing targetIsometry placementClose in
/-- The actual finite distance profiles approximate distance to actual born
marks in the SAME original metric ambient. No metric recoding is used in
this spatial estimate. -/
theorem actualFiniteAnnealedDistanceProfile_same_ambient_uniform
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (label : ActualAnnealedBirthLabels rule) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ vertex,
      |actualFiniteAnnealedDistanceProfile rule scale scalePositive depth
          (markedGenerationConfiguration rule marks depth [] true) vertex label -
        dist (sources depth (actualAnnealedFiniteVertexEquiv rule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex))
          (target (actualChemicalLabelPoint rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive
            lengths nonnegative positive childConvergence label))| < tolerance := by
  filter_upwards [actualFiniteAnnealedDistanceProfile_uniform rule classicalRule marks crossing coherent
    scale scalePositive lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
    radiusBounds label (tolerance / 2) (by positivity), placementClose (tolerance / 2) (by positivity)] with depth raw close
  intro vertex
  let point := actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence depth
      (actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex)
  let born := actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence label
  have rawNear := raw vertex
  have placedNear := close (actualAnnealedFiniteVertexEquiv rule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex)
  have changed := abs_dist_sub_le (target point)
    (sources depth (actualAnnealedFiniteVertexEquiv rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex)) (target born)
  rw [targetIsometry.dist_eq, dist_comm (target point)] at changed
  have triangle := abs_sub_le (actualFiniteAnnealedDistanceProfile rule scale scalePositive depth
    (markedGenerationConfiguration rule marks depth [] true) vertex label) (dist point born)
    (dist (sources depth (actualAnnealedFiniteVertexEquiv rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth vertex)) (target born))
  exact triangle.trans_lt (by linarith)


include crossing targetIsometry placementClose in
/-- The genuine finite chemical full-path laws transport to the fixed
compact profile, using weak convergence in the SAME actual ambient and
proved actual uniform chemical distances. This retains every path time. -/
theorem actualFiniteAnnealed_same_ambient_profile_whole_weak
    [CompactSpace Ambient]
    (sourceIsometry : ∀ depth, Isometry (sources depth))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (finiteLaws : ∀ depth, ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011
      (ActualFiniteCluster rule (configurationAtDepth rule depth
        (markedGenerationConfiguration rule marks depth [] true)) scale scalePositive depth)))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 Ambient))
    (projectedWeak : Tendsto (fun depth => (finiteLaws depth).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (sources depth ∘ actualAnnealedFiniteVertexEquiv rule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth)
        ((sourceIsometry depth).continuous.comp
          (actualAnnealedFiniteVertexEquiv rule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth).continuous)).measurable.aemeasurable)
      atTop (𝓝 law)) :
    Tendsto (fun depth => (finiteLaws depth).map
      (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (actualFiniteAnnealedCompactProfile rule scale scalePositive depth
          (markedGenerationConfiguration rule marks depth [] true))
        (distanceProfilePoint_continuous _)).measurable.aemeasurable) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011
        (distanceProfilePoint (target ∘ actualChemicalLabelPoint rule classicalRule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive
          lengths nonnegative positive childConvergence))
        (distanceProfilePoint_continuous _)).measurable.aemeasurable)) := by
  let births := target ∘ actualChemicalLabelPoint rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive
    lengths nonnegative positive childConvergence
  let originals := fun depth => skorokhodCadlagContinuousCarrierMapCompletion20261011
    (actualFiniteAnnealedCompactProfile rule scale scalePositive depth
      (markedGenerationConfiguration rule marks depth [] true)) (distanceProfilePoint_continuous _)
  let projections := fun depth => skorokhodCadlagContinuousCarrierMapCompletion20261011
    (sources depth ∘ actualAnnealedFiniteVertexEquiv rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth)
    ((sourceIsometry depth).continuous.comp
      (actualAnnealedFiniteVertexEquiv rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth).continuous)
  have originalMeasurable depth : Measurable (originals depth) :=
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 _ _).measurable
  have projectionMeasurable depth : Measurable (projections depth) :=
    (skorokhodCadlagContinuousCarrierMap_continuous_completion20261011 _ _).measurable
  have weak := countableDistanceProfile_whole_cadlag_weak
    (fun depth => SkorokhodCadlagPathCompletion20261011
      (ActualFiniteCluster rule (configurationAtDepth rule depth
        (markedGenerationConfiguration rule marks depth [] true)) scale scalePositive depth))
    (fun depth => (finiteLaws depth : Measure (SkorokhodCadlagPathCompletion20261011
      (ActualFiniteCluster rule (configurationAtDepth rule depth
        (markedGenerationConfiguration rule marks depth [] true)) scale scalePositive depth)))) births originals projections
    (fun depth => (originalMeasurable depth).aemeasurable)
    (fun depth => (projectionMeasurable depth).aemeasurable) law projectedWeak
    (fun label tolerance coordinatePositive => by
      filter_upwards [actualFiniteAnnealedDistanceProfile_same_ambient_uniform rule classicalRule marks crossing coherent
        scale scalePositive lengths nonnegative positive childConvergence target targetIsometry sources placementClose
        eta coefficient start etaNonnegative etaBelowOne radiusBounds label tolerance coordinatePositive] with depth near
      intro path time
      change |Real.exp (-actualFiniteAnnealedDistanceProfile rule scale scalePositive depth
          (markedGenerationConfiguration rule marks depth [] true) (path.val time) label) -
        Real.exp (-dist (sources depth (actualAnnealedFiniteVertexEquiv rule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth (path.val time)))
          (births label))| < tolerance
      exact (exp_neg_distance_difference_le dist_nonneg dist_nonneg).trans_lt (near (path.val time)))
  exact weak.1

end
end IGSIII34.ResistanceLimit
