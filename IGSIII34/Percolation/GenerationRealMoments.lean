import IGSIII34.Percolation.ConfigurationMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators

theorem generation_normalizedResistance_uniform_real_moment
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (exponent : ℝ) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)^exponent) ≤ bound := by
  obtain ⟨bound, momentBound⟩ := normalizedPhysicalResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint exponent
  refine ⟨max 1 bound, le_max_left _ _, fun depth => ?_⟩
  rw [generation_normalizedResistance_observable rule classical parameter positive belowOne fixedPoint depth (fun value => value^exponent)]
  exact (momentBound (depth+1)).2.trans (le_max_right _ _)

theorem generation_normalizedResistance_uniform_second_moment
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)^2) ≤ bound := by
  simpa only [Real.rpow_two] using generation_normalizedResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint 2

theorem generation_normalizedResistance_uniform_real_inverse_moment
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (exponent : ℝ) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)⁻¹^exponent) ≤ bound := by
  simpa only [Real.rpow_neg_eq_inv_rpow] using generation_normalizedResistance_uniform_real_moment rule classical parameter positive belowOne fixedPoint (-exponent)

end
end IGSIII34.Percolation
