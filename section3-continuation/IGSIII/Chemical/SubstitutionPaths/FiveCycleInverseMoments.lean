import IGSIII.Chemical.SubstitutionPaths.FiveCycleBranchLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII.Chemical.FiveCycle

open Universality Universality.FiniteNetwork Substitution IGSIII.Probability
open IGSIII.Chemical.SmallBall
open scoped BigOperators

private theorem finiteMean_const_mul {Outcome : Type*} [Fintype Outcome]
    (weight response : Outcome → ℝ) (constant : ℝ) :
    finiteMean weight (fun outcome => constant * response outcome) = constant * finiteMean weight response := by
  simp only [finiteMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

private theorem finiteMean_indicator_scale {Outcome : Type*} [Fintype Outcome]
    (weight : Outcome → ℝ) (condition : Outcome → Bool) (constant : ℝ) :
    finiteMean weight (fun outcome => if condition outcome then constant else 0) =
      constant * finiteMean weight (fun outcome => if condition outcome then 1 else 0) := by
  simp only [finiteMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  cases condition outcome <;> simp [mul_comm]

theorem connected_child_inverse_cube_bound {Outcome : Type*} [Fintype Outcome]
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p)
    (weight value : Outcome → ℝ) (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (weightNormalized : ∑ outcome, weight outcome = 1) (valuePositive : ∀ outcome, 0 < value outcome) :
    finiteMean (network.conditionalCellWeight p true) (fun coarse =>
      finiteMean (tupleWeight (fun _ : Fin 5 => weight))
        (fun cells => ((edgePathFamily network coarse).shortest (fun edge => value (cells edge)))⁻¹ ^ 3)) ≤
      (p / 8 + p ^ 2 / 27) * finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) := by
  classical
  have productNonnegative := tupleWeight_nonnegative (fun _ : Fin 5 => weight) (fun _ => weightNonnegative)
  have localMean (edge : Fin 5) :
      finiteMean (tupleWeight (fun _ : Fin 5 => weight)) (fun cells => (value (cells edge))⁻¹ ^ 3) =
        finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) :=
    finiteMean_tuple_local _ (fun _ => weightNormalized) edge (fun outcome => (value outcome)⁻¹ ^ 3)
  simp only [inv_pow] at localMean
  have innerMean (coarse : Configuration 5) :
      finiteMean (tupleWeight (fun _ : Fin 5 => weight)) (fun cells =>
        (if coarse 0 && coarse 1 then (1 / 16 : ℝ) * ((value (cells 0))⁻¹ ^ 3 + (value (cells 1))⁻¹ ^ 3) else 0) +
        (if coarse 2 && coarse 3 && coarse 4 then
          (1 / 81 : ℝ) * ((value (cells 2))⁻¹ ^ 3 + (value (cells 3))⁻¹ ^ 3 + (value (cells 4))⁻¹ ^ 3) else 0)) =
        (if coarse 0 && coarse 1 then finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 8 else 0) +
        (if coarse 2 && coarse 3 && coarse 4 then finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 27 else 0) := by
    rw [finiteMean_add]
    by_cases short : (coarse 0 && coarse 1) = true <;>
      by_cases long : (coarse 2 && coarse 3 && coarse 4) = true <;>
      simp [short, long, finiteMean_const_mul, finiteMean_add,
        finiteMean_const _ (tupleWeight_normalized _ (fun _ => weightNormalized)), add_zero, zero_add]
    all_goals
      simp only [localMean 0, localMean 1, localMean 2, localMean 3, localMean 4]
      ring
  calc
    _ ≤ finiteMean (network.conditionalCellWeight p true) (fun coarse =>
        (if coarse 0 && coarse 1 then finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 8 else 0) +
        (if coarse 2 && coarse 3 && coarse 4 then finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 27 else 0)) := by
      apply Finset.sum_le_sum
      intro coarse _
      by_cases crossing : network.crosses coarse = true
      · apply mul_le_mul_of_nonneg_left _ (network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
        dsimp only
        rw [← innerMean coarse]
        apply Finset.sum_le_sum
        intro cells _
        exact mul_le_mul_of_nonneg_left
          (actual_path_inverse_cube_bound coarse crossing _ (fun edge => valuePositive (cells edge)))
          (productNonnegative cells)
      · simp [conditionalCellWeight, crossing]
    _ = _ := by
      rw [finiteMean_add,
        finiteMean_indicator_scale (network.conditionalCellWeight p true)
          (fun coarse : Configuration 5 => coarse 0 && coarse 1)
          (finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 8),
        finiteMean_indicator_scale (network.conditionalCellWeight p true)
          (fun coarse : Configuration 5 => coarse 2 && coarse 3 && coarse 4)
          (finiteMean weight (fun outcome => (value outcome)⁻¹ ^ 3) / 27)]
      change _ * (∑ configuration, network.conditionalCellWeight p true configuration *
          (if configuration 0 && configuration 1 then 1 else 0)) +
        _ * (∑ configuration, network.conditionalCellWeight p true configuration *
          (if configuration 2 && configuration 3 && configuration 4 then 1 else 0)) = _
      rw [short_branch_probability p positive fixedPoint, long_branch_probability p positive fixedPoint]
      ring

noncomputable def inverseThirdMoment {vertices edges : ℕ}
    (cell : FiniteNetwork vertices edges) (p : ℝ) : ℝ :=
  finiteMean (cell.conditionalCellWeight p true) (fun configuration =>
    (((cell.openGraph configuration).dist cell.source cell.target : ℝ)⁻¹) ^ 3)

theorem actual_inverse_third_moment_recursion (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : network.reliability p = p) (depth : ℕ) :
    inverseThirdMoment (rule.generation (depth + 1)).network p ≤
      (p / 8 + p ^ 2 / 27) * inverseThirdMoment (rule.generation depth).network p := by
  let mean := conditionedDistanceMean (rule.generation depth).network p
  have meanPositive : 0 < mean :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  let response : ℝ → ℝ := fun distance => (mean * distance)⁻¹ ^ 3
  let value : Configuration (rule.generation depth).edges → ℝ :=
    fun configuration => mean * positiveNormalizedDistance (rule.generation depth).network p configuration
  have valuePositive : ∀ configuration, 0 < value configuration := fun configuration =>
    mul_pos meanPositive (positiveNormalizedDistance_positive _ p meanPositive configuration)
  have normalization (distance : ℝ) :
      mean * (distance / conditionedDistanceMean (rule.generation depth).network p) = distance := by
    change mean * (distance / mean) = distance
    field_simp
  have generationLaw := generation_distance_over_childMean_observable rule rule_classical.simple
    p positive lessOne fixedPoint depth response
  have rootNetwork : rule.network = network := rfl
  rw [rootNetwork] at generationLaw
  simp only [response, normalization] at generationLaw
  have childMoment : finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
      (fun configuration => (value configuration)⁻¹ ^ 3) = inverseThirdMoment (rule.generation depth).network p := by
    have equality := positiveNormalizedDistance_observable (rule.generation depth).network p response
    simpa only [finiteMean, response, value, normalizedDistance, normalization, inverseThirdMoment] using equality
  calc
    _ = finiteMean (network.conditionalCellWeight p true) (fun coarse =>
        finiteMean (tupleWeight (fun _ : Fin 5 => (rule.generation depth).network.conditionalCellWeight p true))
          (fun cells => ((edgePathFamily network coarse).shortest (fun edge => value (cells edge)))⁻¹ ^ 3)) := by
      calc
        _ = finiteMean (network.conditionalCellWeight p true) (fun coarse =>
            finiteMean (tupleWeight (fun edge => (rule.generation depth).network.conditionalCellWeight p (coarse edge)))
              (fun cells => response ((edgePathFamily network coarse).shortest
                (fun edge => normalizedDistance (rule.generation depth).network p (cells edge))))) := by
          simpa only [inverseThirdMoment, finiteMean, tupleWeight, response, rule] using generationLaw
        _ = _ := by
          apply Finset.sum_congr rfl
          intro coarse _
          congr 1
          have equality := actual_child_shortest_connected_product network (rule.generation depth).network
            rule_classical.simple p (by rwa [rule.generation_fixed_point p fixedPoint])
              (by rwa [rule.generation_fixed_point p fixedPoint]) coarse response
          refine equality.trans ?_
          apply Finset.sum_congr rfl
          intro cells _
          congr 1
          dsimp only [response, value]
          rw [PathFamily.shortest_scale _ _ meanPositive.le]
    _ ≤ (p / 8 + p ^ 2 / 27) *
        finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
          (fun configuration => (value configuration)⁻¹ ^ 3) :=
      connected_child_inverse_cube_bound p positive lessOne fixedPoint _ value
        (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg
          positive.le lessOne.le true configuration)
        ((rule.generation depth).network.sum_conditionalCellWeight p
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]) true) valuePositive
    _ = _ := by rw [childMoment]

theorem actual_inverse_third_moment_lower {vertices edges : ℕ}
    (cell : FiniteNetwork vertices edges) (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (reliabilityPositive : 0 < cell.reliability p) (reliabilityLessOne : cell.reliability p < 1) :
    (conditionedDistanceMean cell p)⁻¹ ^ 3 ≤ inverseThirdMoment cell p := by
  let mean := conditionedDistanceMean cell p
  have meanPositive : 0 < mean := lt_of_lt_of_le zero_lt_one
    (conditionedDistanceMean_atLeastOne cell positive.le lessOne.le reliabilityPositive reliabilityLessOne)
  let value := fun configuration => mean * positiveNormalizedDistance cell p configuration
  have normalization (distance : ℝ) : mean * (distance / conditionedDistanceMean cell p) = distance := by
    change mean * (distance / mean) = distance
    field_simp
  have completionMean : finiteMean (cell.conditionalCellWeight p true) (positiveNormalizedDistance cell p) =
      finiteMean (cell.conditionalCellWeight p true) (normalizedDistance cell p) :=
    positiveNormalizedDistance_observable cell p id
  have meanEquality : finiteMean (cell.conditionalCellWeight p true) value = mean := by
    rw [show value = fun configuration => mean * positiveNormalizedDistance cell p configuration from rfl,
      finiteMean_const_mul, completionMean]
    change mean * (∑ configuration, cell.conditionalCellWeight p true configuration * normalizedDistance cell p configuration) = mean
    rw [normalizedDistance_mean_one cell p meanPositive, mul_one]
  have momentEquality : finiteMean (cell.conditionalCellWeight p true) (fun configuration => (value configuration)⁻¹ ^ 3) =
      inverseThirdMoment cell p := by
    have equality := positiveNormalizedDistance_observable cell p (fun distance => (mean * distance)⁻¹ ^ 3)
    simpa only [finiteMean, value, normalizedDistance, normalization, inverseThirdMoment] using equality
  have comparison := inverse_cube_weighted_mean (cell.conditionalCellWeight p true) value
    (cell.conditionalCellWeight_nonneg positive.le lessOne.le true)
    (cell.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true)
    (fun configuration => mul_pos meanPositive (positiveNormalizedDistance_positive cell p meanPositive configuration))
  change (finiteMean (cell.conditionalCellWeight p true) value)⁻¹ ^ 3 ≤
    finiteMean (cell.conditionalCellWeight p true) (fun configuration => (value configuration)⁻¹ ^ 3) at comparison
  rw [meanEquality, momentEquality] at comparison
  exact comparison

end IGSIII.Chemical.FiveCycle
