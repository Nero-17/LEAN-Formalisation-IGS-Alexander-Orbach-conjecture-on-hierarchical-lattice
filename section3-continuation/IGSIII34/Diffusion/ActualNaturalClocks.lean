import IGSIII34.Diffusion.ActualDegreeRewards
import IGSIII34.Diffusion.NaturalTimeChange
import IGSIII.Mass.ComponentMassGrowth

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter Matrix
open scoped Topology

/-- On the actual common innovation sample the deterministic-clock ratios
converge to positive reciprocals of the same random Perron mass. This is the
clock conclusion of the manuscript, separately from process convergence. -/
theorem actual_deterministic_clock_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (resistance : ℝ) (resistancePositive : 0 < resistance) :
    ∃ (edgeCoefficient vertexCoefficient : ℝ)
      (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < edgeCoefficient ∧ 0 < vertexCoefficient ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < mass marks ∧
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ depth) /
            (2 * (rule.generation depth).network.liveCount .connected .connected
              (markedGenerationConfiguration rule marks depth [] true) * resistance ^ depth))
          atTop (𝓝 (1 / (2 * (edgeCoefficient * mass marks)))) ∧
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ depth) /
            ((markedComponentVertexMass rule marks depth [] + 2) * resistance ^ depth))
          atTop (𝓝 (1 / (vertexCoefficient * mass marks))) := by
  obtain ⟨left, coefficient, mass, leftPositive, coefficientPositive, limits⟩ :=
    actual_joint_edge_vertex_limits classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨(spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * left .connected,
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * coefficient, mass,
    mul_pos radiusPositive leftPositive, mul_pos radiusPositive coefficientPositive, ?_⟩
  filter_upwards [limits] with marks properties
  refine ⟨properties.1, ?_, ?_⟩
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      degree_deterministic_clock_ratio
        (fun depth => ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ))
        _ resistance _ radiusPositive resistancePositive.ne'
        (mul_pos radiusPositive (mul_pos properties.1 leftPositive)) properties.2.1
  · simpa only [mul_assoc] using counting_deterministic_clock_ratio
      (fun depth => markedComponentVertexMass rule marks depth [] + 2)
      _ resistance _ radiusPositive resistancePositive.ne'
      (mul_pos radiusPositive (mul_pos coefficientPositive properties.1)) properties.2.2

end
end IGSIII34.Diffusion
