import IGSIII34.Percolation.ConfigurationMoments
import IGSIII34.Percolation.NormalizedBlock
import IGSIII34.Percolation.IIDJensen
import IGSIII.Chemical.SmallBall.Growth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators NNReal ENNReal

theorem generation_conditionalMeanResistance_product
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (constant : ℝ)
    (inverseBound : ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight parameter true)
        (fun configuration => (positiveNormalizedResistance (rule.generation depth).network parameter configuration)⁻¹) ≤ constant)
    (coarse fine : ℕ) :
    conditionalMeanResistance (rule.generation coarse).network parameter *
        conditionalMeanResistance (rule.generation fine).network parameter / constant ≤
      conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter ∧
    conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter ≤
      conditionalMeanResistance (rule.generation coarse).network parameter *
        conditionalMeanResistance (rule.generation fine).network parameter := by
  have meanPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint fine
  have innerNormalized := (rule.generation fine).network.sum_conditionalCellWeight parameter
    (by rwa [rule.generation_fixed_point parameter fixedPoint])
    (by rwa [rule.generation_fixed_point parameter fixedPoint]) true
  have innerNonnegative := (rule.generation fine).network.conditionalCellWeight_nonneg positive.le belowOne.le true
  have outerNonnegative := (rule.generation coarse).network.conditionalCellWeight_nonneg positive.le belowOne.le true
  have pointwise (configuration : Configuration (rule.generation coarse).edges) :
      unitConfigurationResistance (rule.generation coarse).network configuration / constant ≤
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            electricalCell (rule.generation coarse).network configuration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))) ∧
      finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            electricalCell (rule.generation coarse).network configuration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))) ≤
        unitConfigurationResistance (rule.generation coarse).network configuration := by
    by_cases crossing : (rule.generation coarse).network.crosses configuration = true
    · exact finite_iid_electricalCell_mean_sandwich _ configuration crossing _ innerNonnegative innerNormalized
        _ (positiveNormalizedResistance_positive _ parameter meanPositive)
        (positiveNormalizedResistance_mean_one _ parameter meanPositive) constant (inverseBound fine)
    · simp only [electricalCell_eq_zero_of_not_crosses _ _ crossing,
        show unitConfigurationResistance (rule.generation coarse).network configuration = 0 from
          electricalCell_eq_zero_of_not_crosses _ _ crossing _, finiteMean, mul_zero, Finset.sum_const_zero,
        zero_div, le_refl, and_self]
  have lower := finiteMean_mono _ outerNonnegative (fun configuration => (pointwise configuration).1)
  have upper := finiteMean_mono _ outerNonnegative (fun configuration => (pointwise configuration).2)
  have decomposition := normalized_generation_block_resistance_observable rule parameter positive belowOne fixedPoint
    coarse fine meanPositive id
  change finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
    (fun configuration => unitConfigurationResistance (rule.generation (coarse+fine+1)).network configuration /
      conditionalMeanResistance (rule.generation fine).network parameter) = _ at decomposition
  simp only [id_eq] at decomposition
  simp_rw [div_eq_mul_inv] at decomposition lower
  rw [finiteMean_mul_const, finiteMean_conditional_unitResistance] at decomposition lower
  rw [← decomposition] at lower upper
  rw [finiteMean_conditional_unitResistance] at upper
  constructor
  · calc
      _ = (conditionalMeanResistance (rule.generation coarse).network parameter * constant⁻¹) *
          conditionalMeanResistance (rule.generation fine).network parameter := by ring
      _ ≤ (conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter *
          (conditionalMeanResistance (rule.generation fine).network parameter)⁻¹) *
          conditionalMeanResistance (rule.generation fine).network parameter :=
        mul_le_mul_of_nonneg_right lower meanPositive.le
      _ = _ := by rw [mul_assoc, inv_mul_cancel₀ meanPositive.ne', mul_one]
  · exact (div_le_iff₀ meanPositive).mp (by simpa only [div_eq_mul_inv] using upper)

theorem electricalOrbitScale_succ_eq_generation_mean
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (electricalOrbitScale rule parameter positive belowOne fixedPoint (depth+1) : ℝ) =
      conditionalMeanResistance (rule.generation depth).network parameter := by
  rw [electricalOrbitScale_eq_actual_mean rule classical parameter positive belowOne fixedPoint,
    electricalIteration_mean_eq_conditionalMeanResistance]

theorem electricalOrbitScale_lower_bound
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    deriv rule.network.reliability parameter ^ depth ≤
      (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) := by
  cases depth with
  | zero => simp [electricalOrbitScale]
  | succ depth =>
    rw [electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint]
    exact generation_conditionalMeanResistance_lower_bound rule positive belowOne.le fixedPoint depth

theorem electricalOrbitScale_upper_path_bound
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration)
    (depth : ℕ) :
    (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) ≤
      (∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : MeasureTheory.Measure _)) ^ depth := by
  have pathMeanNonnegative : 0 ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : MeasureTheory.Measure _) :=
    MeasureTheory.integral_nonneg (fun _ => Nat.cast_nonneg _)
  induction depth with
  | zero => simp [electricalOrbitScale]
  | succ depth previous =>
    have meanNonnegative := (zero_lt_one.trans
      (rule.network.interior_fixed_point_strictly_unstable parameter positive belowOne fixedPoint classical.scale)).le.trans
        (normalizedElectricalOrbit_outputMean_bounds rule classical parameter positive belowOne fixedPoint depth).1
    obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_moment rule classical parameter positive belowOne fixedPoint 2
    have inputIntegrable := integrable_coe_of_secondMoment_bound _ bound (momentBound depth)
    have outputBound := electricalOutputMean_le_expected_path_length rule parameter positive belowOne fixedPoint _
      inputIntegrable (normalizedElectricalOrbit_mean_one rule classical parameter positive belowOne fixedPoint depth)
      pathLength distanceBound
    change ((Real.toNNReal _ * electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ≥0) : ℝ) ≤ _
    rw [NNReal.coe_mul, Real.coe_toNNReal _ meanNonnegative, pow_succ]
    simpa only [mul_comm] using mul_le_mul outputBound previous
      (electricalOrbitScale rule parameter positive belowOne fixedPoint depth).property pathMeanNonnegative

theorem electricalOrbitScale_quasi_multiplicative
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 ∧ ∀ first second,
      constant * (electricalOrbitScale rule parameter positive belowOne fixedPoint first : ℝ) *
          (electricalOrbitScale rule parameter positive belowOne fixedPoint second : ℝ) ≤
        (electricalOrbitScale rule parameter positive belowOne fixedPoint (first+second) : ℝ) ∧
      (electricalOrbitScale rule parameter positive belowOne fixedPoint (first+second) : ℝ) ≤
        (electricalOrbitScale rule parameter positive belowOne fixedPoint first : ℝ) *
          (electricalOrbitScale rule parameter positive belowOne fixedPoint second : ℝ) := by
  obtain ⟨bound, boundAtLeastOne, inverseBound⟩ := generation_normalizedResistance_uniform_inverse_moment
    rule classical parameter positive belowOne fixedPoint
  have boundPositive := zero_lt_one.trans_le boundAtLeastOne
  have inverseAtMostOne : bound⁻¹ ≤ 1 := inv_le_one_of_one_le₀ boundAtLeastOne
  refine ⟨bound⁻¹, inv_pos.mpr boundPositive, inverseAtMostOne, fun first second => ?_⟩
  cases first with
  | zero =>
    simp only [electricalOrbitScale, NNReal.coe_one, Nat.zero_add, mul_one, one_mul]
    exact ⟨mul_le_of_le_one_left (electricalOrbitScale rule parameter positive belowOne fixedPoint second).property
      inverseAtMostOne, le_rfl⟩
  | succ first =>
    cases second with
    | zero =>
      simp only [electricalOrbitScale, NNReal.coe_one, mul_one]
      exact ⟨mul_le_of_le_one_left (Real.toNNReal _ * electricalOrbitScale rule parameter positive belowOne fixedPoint first).property
        inverseAtMostOne, le_rfl⟩
    | succ second =>
      have comparison := generation_conditionalMeanResistance_product rule classical parameter positive belowOne fixedPoint
        bound inverseBound first second
      have index : first+1+(second+1) = (first+second+1)+1 := by omega
      rw [index, electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint,
        electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint,
        electricalOrbitScale_succ_eq_generation_mean rule classical parameter positive belowOne fixedPoint]
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using comparison

theorem exists_actual_electrical_growth
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      deriv rule.network.reliability parameter ≤ growth ∧
      growth ≤ ∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : MeasureTheory.Measure _) ∧
      ∀ depth, growth^depth ≤ (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth^depth := by
  obtain ⟨constant, constantPositive, constantAtMostOne, products⟩ := electricalOrbitScale_quasi_multiplicative
    rule classical parameter positive belowOne fixedPoint
  obtain ⟨growth, lower, upper, bounds⟩ := IGSIII.Chemical.SmallBall.quasi_multiplicative_growth_between
    (means := fun depth => (electricalOrbitScale rule parameter positive belowOne fixedPoint depth : ℝ)) rfl
    (rule.network.interior_fixed_point_strictly_unstable parameter positive belowOne fixedPoint classical.scale).le
    (electricalOrbitScale_lower_bound rule classical parameter positive belowOne fixedPoint)
    (electricalOrbitScale_upper_path_bound rule classical parameter positive belowOne fixedPoint pathLength distanceBound)
    constantPositive constantAtMostOne (fun first second => (products first second).2)
    (fun first second => (products first second).1)
  exact ⟨constant, growth, constantPositive, constantAtMostOne, lower, upper, bounds⟩

end
end IGSIII34.Percolation
