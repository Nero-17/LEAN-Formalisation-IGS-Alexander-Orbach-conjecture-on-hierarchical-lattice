import IGSIII34.Diffusion.ActualNaturalClocks
import IGSIII34.ResistanceLimit.ActualStationaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII.Geometry IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped _root_.Topology

theorem paper_deterministic_clock_ratio_completion
    (count : ℕ → ℝ) (growth resistance factor limit : ℝ)
    (growthPositive : 0 < growth) (resistanceNonzero : resistance ≠ 0)
    (factorPositive : 0 < factor) (limitPositive : 0 < limit)
    (convergence : Tendsto (fun depth => count depth / growth ^ depth) atTop (𝓝 (growth * limit))) :
    Tendsto (fun depth => (growth * resistance) ^ (depth+1) /
      (factor * count depth * resistance ^ (depth+1))) atTop (𝓝 (1 / (factor * limit))) := by
  have original := deterministic_clock_ratio count growth resistance factor (growth*limit)
    growthPositive resistanceNonzero factorPositive (mul_pos growthPositive limitPositive) convergence
  have multiplied := original.const_mul growth
  have identity (depth : ℕ) : growth * ((growth*resistance)^depth / (factor*count depth*resistance^depth)) =
      (growth*resistance)^(depth+1) / (factor*count depth*resistance^(depth+1)) := by
    rw [pow_succ, pow_succ]
    field_simp [resistanceNonzero]
  have limitIdentity : growth * (1 / (factor*(growth*limit))) = 1/(factor*limit) := by
    field_simp [growthPositive.ne', factorPositive.ne', limitPositive.ne']
  simpa only [identity, limitIdentity] using multiplied

theorem ae_actual_paper_deterministic_clock_limits_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (resistance : ℝ) (resistancePositive : 0 < resistance) :
    ∃ (edgeCoefficient vertexCoefficient : ℝ)
      (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < edgeCoefficient ∧ 0 < vertexCoefficient ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < mass marks ∧ ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ (depth+1)) /
            (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)) * resistance ^ (depth+1)))
          atTop (𝓝 (1 / (2 * (edgeCoefficient * mass marks)))) ∧
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ (depth+1)) /
            ((Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) : ℝ) * resistance ^ (depth+1)))
          atTop (𝓝 (1 / (vertexCoefficient * mass marks))) := by
  obtain ⟨left, coefficient, mass, leftPositive, coefficientPositive, limits⟩ :=
    actual_joint_edge_vertex_limits classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨left .connected, coefficient, mass, leftPositive, coefficientPositive, ?_⟩
  filter_upwards [limits, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks properties crossing
  refine ⟨properties.1, ?_⟩
  intro chemicalScale chemicalScalePositive
  have vertexCard (depth : ℕ) :
      (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) : ℝ) =
        markedComponentVertexMass rule marks depth [] + 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact actualFiniteCluster_card rule marks crossing chemicalScale chemicalScalePositive depth
  constructor
  · simpa only [clusterEdge_card, stationaryConfiguration, mul_assoc, mul_left_comm, mul_comm] using
      paper_deterministic_clock_ratio_completion
        (fun depth => ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ))
        _ resistance 2 (mass marks * left .connected) radiusPositive resistancePositive.ne'
        (by norm_num) (mul_pos properties.1 leftPositive) properties.2.1
  · simpa only [vertexCard, one_mul] using paper_deterministic_clock_ratio_completion
      (fun depth => markedComponentVertexMass rule marks depth [] + 2)
      _ resistance 1 (coefficient * mass marks) radiusPositive resistancePositive.ne'
      zero_lt_one (mul_pos coefficientPositive properties.1) properties.2.2

end
end IGSIII34.Diffusion
