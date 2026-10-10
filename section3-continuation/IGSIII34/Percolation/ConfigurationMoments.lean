import IGSIII34.Percolation.ConnectedResistance
import IGSIII34.Percolation.PhysicalInverse
import IGSIII34.Percolation.MarkedIntegral
import IGSIII34.Resistance.FiniteElectricalVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped BigOperators

theorem finiteMean_conditional_unitResistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ) :
    finiteMean (network.conditionalCellWeight parameter true)
      (unitConfigurationResistance network) = conditionalMeanResistance network parameter := by
  unfold finiteMean conditionalMeanResistance Universality.FiniteNetwork.expectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases crossing : network.crosses configuration = true
  · simp only [Universality.FiniteNetwork.conditionalCellWeight, crossing, ↓reduceIte]
    change _ * unitConfigurationResistance network configuration = _ * configurationResistance network configuration / _
    change (bernoulliWeight parameter configuration / network.reliability parameter) *
      unitConfigurationResistance network configuration =
      bernoulliWeight parameter configuration * unitConfigurationResistance network configuration / network.reliability parameter
    ring
  · simp [Universality.FiniteNetwork.conditionalCellWeight, crossing]

theorem positiveNormalizedResistance_mean_one {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ)
    (meanPositive : 0 < conditionalMeanResistance network parameter) :
    finiteMean (network.conditionalCellWeight parameter true)
      (positiveNormalizedResistance network parameter) = 1 := by
  rw [show finiteMean (network.conditionalCellWeight parameter true) (positiveNormalizedResistance network parameter) =
    finiteMean (network.conditionalCellWeight parameter true) (normalizedConfigurationResistance network parameter) from
      positiveNormalizedResistance_observable network parameter id]
  unfold normalizedConfigurationResistance
  simp_rw [div_eq_mul_inv]
  rw [finiteMean_mul_const, finiteMean_conditional_unitResistance, mul_inv_cancel₀ meanPositive.ne']

theorem generation_conditionalMeanResistance_positive (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    0 < conditionalMeanResistance (rule.generation depth).network parameter := by
  exact (pow_pos (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
    parameter positive belowOne fixedPoint classical.scale)) _).trans_le
    (generation_conditionalMeanResistance_lower_bound rule positive belowOne.le fixedPoint depth)

theorem generation_normalizedResistance_observable (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) (response : ℝ → ℝ) :
    finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
      (fun configuration => response (positiveNormalizedResistance (rule.generation depth).network parameter configuration)) =
      ∫ marks, response (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint (depth + 1) marks : ℝ)
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
  rw [positiveNormalizedResistance_observable]
  change (∑ configuration, (rule.generation depth).network.conditionalCellWeight parameter true configuration *
    response (normalizedConfigurationResistance (rule.generation depth).network parameter configuration)) = _
  rw [← marked_observable_integral rule parameter positive belowOne fixedPoint depth [] true
    (fun configuration => response (normalizedConfigurationResistance (rule.generation depth).network parameter configuration))]
  apply integral_congr_ae
  filter_upwards [independentInnovationLaw_crosses rule parameter positive belowOne fixedPoint] with marks crossing
  apply congrArg response
  unfold normalizedConfigurationResistance
  rw [markedGeneration_resistance_eq_iteration rule marks crossing]
  rw [normalizedPhysicalResistance_eq_div_actual_mean rule classical parameter positive belowOne fixedPoint]
  rw [electricalIteration_mean_eq_conditionalMeanResistance]

theorem generation_normalizedResistance_uniform_inverse_moment (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)⁻¹) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedPhysicalResistance_uniform_inverse_moment
    rule classical parameter positive belowOne fixedPoint 1
  refine ⟨max 1 bound, le_max_left _ _, fun depth => ?_⟩
  rw [generation_normalizedResistance_observable rule classical parameter positive belowOne fixedPoint depth
    (fun value => value⁻¹)]
  have boundAtDepth : (∫ marks,
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint (depth+1) marks : ℝ)⁻¹
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) ≤ bound := by
    simpa only [pow_one] using (momentBound (depth + 1)).2
  exact boundAtDepth.trans (le_max_right _ _)

end
end IGSIII34.Percolation
