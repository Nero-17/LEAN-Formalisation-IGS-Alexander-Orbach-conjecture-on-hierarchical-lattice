import IGSIII.Geometry.BoxDimensionCriticalEquality

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open IGSIII.Probability Matrix MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- The dimension conclusion holds for the same scalar witness used in any
actual measured convergence theorem, without selecting a second chemical
field or a second metric completion. -/
theorem actual_critical_box_dimension_of_mean_bounds_and_positive_field
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (probabilityPositive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth amplitude : ℝ) (growthGreaterThanOne : 1 < growth) (amplitudePositive : 0 < amplitude)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p probabilityPositive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p probabilityPositive belowOne fixedPoint, 0 < value marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p probabilityPositive belowOne fixedPoint,
      ∀ coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true),
      ∀ lengthNonnegative : ∀ coarse edge,
        0 ≤ chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks coarse edge,
      ∀ lengthPositive : ∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
        0 < chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks coarse edge,
      ∀ childConvergence : ∀ coarse edge, Tendsto (fun fine =>
        (((rule.generation fine).network.openGraph
          (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
            (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
          growth ^ (coarse + fine + 2)) atTop
            (𝓝 (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks coarse edge)),
      lowerBoxDimension (ActualChemicalSpace rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growthGreaterThanOne)
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
        lengthNonnegative lengthPositive childConvergence) =
          ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) ∧
      upperBoxDimension (ActualChemicalSpace rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growthGreaterThanOne)
        (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
        lengthNonnegative lengthPositive childConvergence) =
          ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) := by
  filter_upwards [actual_critical_upper_box_dimension_of_mean_bounds rule classicalRule p probabilityPositive belowOne fixedPoint
      constant growth growthGreaterThanOne meanBounds,
    actual_critical_lower_box_dimension_of_positive_field rule classicalRule p probabilityPositive belowOne fixedPoint
      growth amplitude growthGreaterThanOne amplitudePositive value valuePositive] with marks upper lower
  intro coherent lengthNonnegative lengthPositive childConvergence
  have actualUpper := upper coherent
    (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence
  have actualLower := lower coherent lengthNonnegative lengthPositive childConvergence
  have order := lowerBoxDimension_le_upperBoxDimension (ActualChemicalSpace rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growthGreaterThanOne)
    (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence)
  exact ⟨le_antisymm (order.trans actualUpper) actualLower,
    le_antisymm actualUpper (actualLower.trans order)⟩

end
end IGSIII.Geometry
