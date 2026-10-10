import IGSIII.Geometry.BoxDimensionGoodCells
import IGSIII.Geometry.BoxDimensionGeometricLower

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open IGSIII.Probability Matrix MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- The lower box dimension is obtained from actual conditional independent
successful connected cylinders and actual separated skeleton points. -/
theorem actual_critical_lower_box_dimension_of_positive_field
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (probability_positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (growth amplitude : ℝ) (growth_large : 1 < growth) (amplitude_positive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p probability_positive below_one fixed_point))
    (value_positive : ∀ᵐ marks ∂independentInnovationLaw rule p probability_positive below_one fixed_point, 0 < value marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p probability_positive below_one fixed_point,
      ∀ (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
        (length_nonnegative : ∀ coarse edge,
          0 ≤ chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)
        (length_positive : ∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
          0 < chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)
        (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
          (((rule.generation fine).network.openGraph
            (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
              (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
            growth ^ (coarse + fine + 2)) atTop
              (𝓝 (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge))),
      ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        Real.log growth : ℝ) : EReal) ≤
          lowerBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth (zero_lt_one.trans growth_large)
            (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
            length_nonnegative length_positive child_convergence) := by
  have growth_positive := zero_lt_one.trans growth_large
  have population_large : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p probability_positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p probability_positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  obtain ⟨threshold, threshold_positive, population⟩ := exists_positive_field_good_cylinder_population
    rule classicalRule p probability_positive below_one fixed_point value (Lp.stronglyMeasurable value).measurable value_positive
  filter_upwards [population] with marks population
  obtain ⟨coefficient, coefficient_positive, count_bound⟩ := population
  intro coherent length_nonnegative length_positive child_convergence
  apply lowerBoxDimension_ge_of_eventual_geometric_packings
    (⟨amplitude * threshold / (2 * growth ^ 2), by positivity⟩ : ℝ≥0)
    (show 0 < amplitude * threshold / (2 * growth ^ 2) by positivity)
    growth ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    growth_large population_large
    (fun depth => (goodConnectedCylinderIndices rule (positiveFieldGoodEvent rule value threshold) depth marks).card)
    ?_ coefficient coefficient_positive count_bound
  intro depth
  have contraction_identity : (⟨growth⁻¹, inv_nonneg.mpr growth_positive.le⟩ : ℝ≥0) = growth.toNNReal⁻¹ := by
    apply NNReal.eq
    simp only [NNReal.coe_inv, Real.coe_toNNReal growth growth_positive.le]
    rfl
  simpa only [contraction_identity] using actual_good_cylinders_le_geometric_coveringNumber
    rule classicalRule p probability_positive below_one fixed_point growth amplitude growth_positive amplitude_positive
    value marks coherent length_nonnegative length_positive child_convergence threshold threshold_positive depth

end
end IGSIII.Geometry

