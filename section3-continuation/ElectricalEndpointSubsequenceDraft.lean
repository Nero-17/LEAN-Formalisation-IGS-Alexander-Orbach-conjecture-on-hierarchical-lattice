import IGSIII34.Percolation.ElectricalOrbitInverse
import IGSIII34.Probability.ElectricalComparisonCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

theorem exists_electrical_endpoint_comparison_subsequence
    (rule : Rule) (classical : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ))
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      Tendsto (fun depth => electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth)) atTop (𝓝 endpoint) ∧
      Tendsto (fun depth =>
        (∫ marks, max (electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth) marks-endpoint marks) 0 *
          max 1 ((endpoint marks)⁻¹^2) ∂independentInnovationLaw rule p positive belowOne fixedPoint) /
        (∫ marks, min (endpoint marks) (endpoint marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0) ∧
      Tendsto (fun depth =>
        (∫ marks, max (endpoint marks-electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth) marks) 0 *
          max 1 ((electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth) marks)⁻¹^2)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) /
        (∫ marks, min (electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth) marks)
          (electricalOrbitLp rule p positive belowOne fixedPoint growth (subsequence depth) marks)⁻¹
          ∂independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0) := by
  obtain ⟨subsequence, increasing, convergence⟩ := membership.tendsto_subseq
  obtain ⟨orbitBound, orbitMoments⟩ := electricalOrbit_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive lowerMeans 4
  obtain ⟨omegaBound, omegaMoments⟩ := electricalOmega_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive lowerMeans 4
  have endpointPositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth growthPositive lowerMeans endpoint membership
  have orbitPositive (depth : ℕ) : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 < electricalOrbitLp rule p positive belowOne fixedPoint growth depth marks := by
    filter_upwards [electricalOrbitLp_above_normalizedPhysicalResistance rule classical p positive belowOne fixedPoint
        growth growthPositive lowerMeans depth,
      normalizedPhysicalResistance_positive_ae rule classical p positive belowOne fixedPoint depth]
      with marks comparison physicalPositive
    have physicalPositiveReal : (0 : ℝ) < (normalizedPhysicalResistance rule p positive belowOne fixedPoint depth marks : ℝ) := by exact_mod_cast physicalPositive
    exact physicalPositiveReal.trans_le comparison
  obtain ⟨forward, backward⟩ := electrical_comparison_coefficients_tendsto_zero
    (independentInnovationLaw rule p positive belowOne fixedPoint) _ endpoint convergence
    (fun depth => orbitPositive (subsequence depth)) endpointPositive
    (fun depth => (orbitMoments (subsequence depth)).1) (omegaMoments endpoint membership).1
    orbitBound (fun depth => (orbitMoments (subsequence depth)).2)
  exact ⟨subsequence, increasing, convergence, forward, backward⟩

end
end IGSIII34.Percolation


