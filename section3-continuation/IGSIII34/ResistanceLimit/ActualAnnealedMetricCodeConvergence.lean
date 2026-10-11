import IGSIII34.ResistanceLimit.ActualAnnealedGeometryCode
import IGSIII.Geometry.ActualClusterGromovHausdorff

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.Spectral MeasureTheory Filter GromovHausdorff
open scoped _root_.Topology
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

variable (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
  (radiusBounds : ∀ address opened depth, start ≤ address.length →
    (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
      coefficient * eta ^ address.length)

include crossing eta coefficient start etaNonnegative etaBelowOne radiusBounds in
/-- Every genuine finite born-distance coordinate converges to its SAME
actual chemical completion coordinate. Nonretained labels are source labels. -/
theorem actualFiniteAnnealedDistance_coordinate_tendsto
    (first last : ActualAnnealedBirthLabels rule) :
    Tendsto (fun depth => dist
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) first)
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) last)) atTop
      (𝓝 (dist
        (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence first)
        (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence last))) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  filter_upwards [actualFiniteAnnealedDistanceProfile_uniform rule classicalRule marks crossing coherent scale scalePositive
    lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne radiusBounds last tolerance tolerancePositive,
    eventually_ge_atTop first.1] with depth near bound
  have estimate := near (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) first)
  rw [actualFiniteAnnealedBirthProjection_chemical rule classicalRule marks coherent scale scalePositive lengths nonnegative positive childConvergence depth first bound] at estimate
  simpa only [Real.dist_eq, actualFiniteAnnealedDistanceProfile] using estimate

include crossing eta coefficient start etaNonnegative etaBelowOne radiusBounds in
/-- The full countable original distance matrix converges in its product
 topology. This is a coordinate conclusion, not a replacement for GHP. -/
theorem actualFiniteAnnealedDistance_matrix_tendsto :
    Tendsto (fun depth => fun pair : ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule => dist
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) pair.1)
      (actualFiniteAnnealedBirthProjection rule scale scalePositive depth (markedGenerationConfiguration rule marks depth [] true) pair.2)) atTop
      (𝓝 (fun pair : ActualAnnealedBirthLabels rule × ActualAnnealedBirthLabels rule => dist
        (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence pair.1)
        (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
          coherent scale scalePositive lengths nonnegative positive childConvergence pair.2))) := by
  apply tendsto_pi_nhds.mpr
  intro pair
  exact actualFiniteAnnealedDistance_coordinate_tendsto rule classicalRule marks crossing coherent scale scalePositive
    lengths nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne radiusBounds pair.1 pair.2

theorem actualFiniteAnnealedGH_coordinate_tendsto (coefficientNonnegative : 0 ≤ coefficient) :
    letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
      marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    Tendsto (fun depth => toGHSpace (ActualFiniteCluster rule
      (configurationAtDepth rule depth (markedGenerationConfiguration rule marks depth [] true)) scale scalePositive depth)) atTop
      (𝓝 (toGHSpace (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence))) := by
  letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
    marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  have convergence := actualFiniteCluster_ghDist_tendsto_zero_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
    marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  have actual : Tendsto (fun depth => toGHSpace (ActualFiniteCluster rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth)) atTop
      (𝓝 (toGHSpace (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive lengths nonnegative positive childConvergence))) :=
    tendsto_iff_dist_tendsto_zero.mpr convergence
  apply actual.congr'
  apply Eventually.of_forall
  intro depth
  apply toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr
  exact ⟨(actualAnnealedFiniteVertexEquiv rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth).symm⟩

end
end IGSIII34.ResistanceLimit

