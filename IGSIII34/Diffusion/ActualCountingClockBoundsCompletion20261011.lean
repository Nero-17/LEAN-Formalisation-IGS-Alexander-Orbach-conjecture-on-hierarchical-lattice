import IGSIII34.ResistanceLimit.ActualStationaryCompletion
import IGSIII34.Diffusion.CountingClockDensityCompletion20261011
import IGSIII34.Diffusion.ActualDegreeRewards
import IGSIII34.Diffusion.ActualPaperClockWalkCompletion20261011
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII.Geometry IGSIII.Chemical.Substitution
open MeasureTheory Filter
open scoped _root_.Topology

theorem ae_actual_edge_vertex_ratio_bounded_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (scale : ℝ) (scalePositive : 0 < scale), ∃ bound : ℝ, 0 < bound ∧ ∀ depth,
        (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth))) /
          (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth) : ℝ) ≤ bound := by
  obtain ⟨left, coefficient, mass, leftPositive, coefficientPositive, limits⟩ :=
    actual_joint_edge_vertex_limits classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [limits, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks properties crossing
  intro scale scalePositive
  have vertexCard (depth : ℕ) :
      (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth) : ℝ) =
        markedComponentVertexMass rule marks depth [] + 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact actualFiniteCluster_card rule marks crossing scale scalePositive depth
  let ratio := fun depth => (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth))) /
    (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) scale scalePositive depth) : ℝ)
  have identity (depth : ℕ) : ratio depth =
      (2 * (((rule.generation depth).network.liveCount .connected .connected (markedGenerationConfiguration rule marks depth [] true) : ℝ) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)) /
      ((markedComponentVertexMass rule marks depth [] + 2) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth) := by
    dsimp only [ratio]
    rw [vertexCard, clusterEdge_card]
    change (2 * ((rule.generation depth).network.liveCount .connected .connected (markedGenerationConfiguration rule marks depth [] true) : ℝ)) / _ = _
    field_simp [pow_ne_zero depth radiusPositive.ne']
  have denominatorPositive := mul_pos radiusPositive (mul_pos coefficientPositive properties.1)
  have convergence := (properties.2.1.const_mul 2).div properties.2.2 denominatorPositive.ne'
  have ratioConvergence : Tendsto ratio atTop
      (𝓝 ((2 * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * (mass marks * left .connected))) /
        (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * (coefficient * mass marks)))) :=
    convergence.congr' (Eventually.of_forall fun depth => (identity depth).symm)
  obtain ⟨bound, boundPositive, bounded⟩ := (Metric.isBounded_range_of_tendsto ratio ratioConvergence).exists_pos_norm_le
  refine ⟨bound, boundPositive, ?_⟩
  intro depth
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using bounded (ratio depth) ⟨depth, rfl⟩)

end
end IGSIII34.Diffusion


