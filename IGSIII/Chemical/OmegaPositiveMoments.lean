import IGSIII.Chemical.SmallBall.ChemicalOmegaMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Chemical.SmallBall
open scoped BigOperators ENNReal

theorem exists_uniform_chemicalOmega_positive_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) (power : ℕ) :
    ∃ bound : ℝ, ∀ point ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      (∫⁻ marks, ENNReal.ofReal (point marks) ^ power
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal bound := by
  obtain ⟨bound, finiteValid⟩ := exists_uniform_growth_scaled_positive_moment
    rule classical p positive belowOne fixedPoint constant growth constantPositive growthPositive meanBounds power
  refine ⟨max 1 bound, fun point membership => ?_⟩
  apply chemicalOmega_lintegral_continuous_response_le rule classical p positive belowOne fixedPoint growth growthPositive.le
    (fun value => ENNReal.ofReal value ^ power)
    ((ENNReal.continuous_pow power).comp ENNReal.continuous_ofReal)
    (ENNReal.ofReal (max 1 bound)) _ _ point membership
  · simpa only [ENNReal.ofReal_one, one_pow] using ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) bound)
  · intro depth
    have equality : (∑ configuration,
        ENNReal.ofReal ((rule.generation depth).network.conditionalCellWeight p true configuration) *
          ENNReal.ofReal (growthScaledDistance rule growth depth configuration) ^ power) =
        ENNReal.ofReal (∑ configuration,
          (rule.generation depth).network.conditionalCellWeight p true configuration *
            growthScaledDistance rule growth depth configuration ^ power) := by
      simp only [← ENNReal.ofReal_pow (growthScaledDistance_nonnegative rule growth growthPositive.le depth _)]
      exact finite_ofReal_weighted_sum _ _
        ((rule.generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
        (fun configuration => pow_nonneg (growthScaledDistance_nonnegative rule growth growthPositive.le depth configuration) power)
    rw [equality]
    exact ENNReal.ofReal_le_ofReal ((finiteValid depth).trans (le_max_right _ _))

end IGSIII.Chemical.Substitution
