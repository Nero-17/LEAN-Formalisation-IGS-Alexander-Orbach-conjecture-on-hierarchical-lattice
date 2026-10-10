import IGSIII.Geometry.BoxDimensionCriticalUpper
import IGSIII.Geometry.BoxDimensionCriticalLower

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open IGSIII.Probability Matrix MeasureTheory Filter
open scoped Topology NNReal ENNReal

theorem lowerBoxDimension_le_upperBoxDimension (Space : Type*) [PseudoMetricSpace Space] :
    lowerBoxDimension Space ≤ upperBoxDimension Space := liminf_le_limsup

/-- The actual critical chemical completion has box dimension log rho / log
lambda. The field, its positive block lengths and their microscopic convergence
are all obtained from the actual classical critical model. -/
theorem exists_actual_critical_box_dimension
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (probability_positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ growth : ℝ, ∃ growth_positive : 0 < growth,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∃ amplitude : ℝ, 1 ≤ amplitude ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p probability_positive below_one fixed_point),
        (∀ᵐ marks ∂independentInnovationLaw rule p probability_positive below_one fixed_point, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p probability_positive below_one fixed_point) = 1 ∧
        ∀ᵐ marks ∂independentInnovationLaw rule p probability_positive below_one fixed_point,
          ∃ coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true),
          ∃ length_nonnegative : ∀ coarse edge,
            0 ≤ chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge,
          ∃ length_positive : ∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
            0 < chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge,
          ∃ child_convergence : ∀ coarse edge, Tendsto (fun fine =>
            (((rule.generation fine).network.openGraph
              (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
                (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
              growth ^ (coarse + fine + 2)) atTop
                (𝓝 (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)),
          lowerBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
            (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
            length_nonnegative length_positive child_convergence) =
              ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) ∧
          upperBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
            (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
            length_nonnegative length_positive child_convergence) =
              ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) := by
  obtain ⟨constant, growth, _, _, growth_lower, growth_upper, mean_bounds, value, _, value_positive, value_mean,
    amplitude, amplitude_at_least_one, field_limits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p probability_positive below_one fixed_point
  have growth_large : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growth_lower
  have growth_positive := zero_lt_one.trans growth_large
  have amplitude_positive := zero_lt_one.trans_le amplitude_at_least_one
  refine ⟨growth, growth_positive, growth_lower, growth_upper, amplitude, amplitude_at_least_one,
    value, value_positive, value_mean, ?_⟩
  filter_upwards [field_limits, independentInnovationLaw_crosses rule p probability_positive below_one fixed_point,
    marked_generations_coherent_ae rule p probability_positive below_one fixed_point,
    actual_critical_upper_box_dimension_of_mean_bounds rule classicalRule p probability_positive below_one fixed_point
      constant growth growth_large mean_bounds,
    actual_critical_lower_box_dimension_of_positive_field rule classicalRule p probability_positive below_one fixed_point
      growth amplitude growth_large amplitude_positive value value_positive] with marks fields crossing coherent upper lower
  obtain ⟨length_nonnegative, length_positive, child_convergence⟩ := actual_block_lengths_of_terminal_field
    rule p probability_positive below_one fixed_point growth amplitude growth_positive amplitude_positive value marks crossing
      (fun address => (fields address).1) (fun address => (fields address).2.2)
  have actual_upper := upper (coherent [] true)
    (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
    length_nonnegative length_positive child_convergence
  have actual_lower := lower (coherent [] true) length_nonnegative length_positive child_convergence
  have order := lowerBoxDimension_le_upperBoxDimension (ActualChemicalSpace rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) (coherent [] true) growth growth_positive
    (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
    length_nonnegative length_positive child_convergence)
  exact ⟨coherent [] true, length_nonnegative, length_positive, child_convergence,
    le_antisymm (order.trans actual_upper) actual_lower,
    le_antisymm actual_upper (actual_lower.trans order)⟩

end
end IGSIII.Geometry
