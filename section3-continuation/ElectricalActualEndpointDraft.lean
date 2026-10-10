import IGSIII34.Percolation.ElectricalOmegaEndpoint
import IGSIII34.Percolation.ElectricalEndogenousExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem electricalOmega_fixed_ray_scalar_atLeastOne
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ))
    (fixed : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (meanOne : (∫ marks, fixed marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (amplitude : ℝ) (endpoint : amplitude • fixed ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    1 ≤ amplitude := by
  have meanLower := electricalOmega_mean_atLeastOne rule classical p positive belowOne fixedPoint growth growthPositive
    lowerMeans (amplitude • fixed) endpoint
  have meanEquality : (∫ marks, (amplitude • fixed) marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = amplitude := by
    rw [integral_congr_ae (Lp.coeFn_smul amplitude fixed)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, meanOne, mul_one]
  rwa [meanEquality] at meanLower

theorem exists_actual_electrical_fixed_ray_endpoint
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability p ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule p positive belowOne fixedPoint : Measure _) ∧
      (∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth) ∧
      ∃ fixed : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth fixed = fixed ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < fixed marks) ∧
        (∫ marks, fixed marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        ∃ amplitude : ℝ, 1 ≤ amplitude ∧
          amplitude • fixed ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth ∧
          (∀ value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth, value ≤ amplitude • fixed) ∧
          ∀ competitor : ℝ, (∀ value ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth,
            value ≤ competitor • fixed) → amplitude ≤ competitor := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, lower, upper, lowerPositive, upperPositive, comparison⟩ :=
      exists_actual_positive_endogenous_electrical_fixed rule classical p positive belowOne fixedPoint pathLength distanceBound
  have growthAboveOne := (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classical.scale).trans_le growthLower
  have growthPositive := zero_lt_one.trans growthAboveOne
  obtain ⟨amplitude, amplitudePositive, endpoint, dominates, least⟩ := electricalOmega_has_fixed_ray_upper_endpoint
    rule classical p positive belowOne fixedPoint constant growth growthAboveOne growthBounds fixed fixedIdentity fixedPositive
    lower upper lowerPositive (fun value membership => (comparison value membership).1)
    (fun value membership => (comparison value membership).2)
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, growthBounds,
    fixed, fixedIdentity, fixedPositive, meanOne, amplitude,
    electricalOmega_fixed_ray_scalar_atLeastOne rule classical p positive belowOne fixedPoint growth growthPositive
      (fun depth => (growthBounds depth).1) fixed meanOne amplitude endpoint,
    endpoint, dominates, least⟩

end
end IGSIII34.Percolation
