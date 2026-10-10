import IGSIII.Chemical.SmallBall.FiniteDepthMoments
import IGSIII.Chemical.SmallBall.FactorialAsymptotics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork Substitution
open scoped BigOperators

noncomputable section

theorem generation_normalizedDistanceMoment_product_law (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth power : ℕ) :
    (conditionedDistanceMean (rule.generation (depth + 1)).network p /
        conditionedDistanceMean (rule.generation depth).network p) ^ power *
        normalizedDistanceMoment (rule.generation (depth + 1)).network p power =
      ∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            (edgePathFamily rule.network coarse).shortest
              (fun edge => normalizedDistance (rule.generation depth).network p (cells edge)) ^ power := by
  have parentMeanPositive : 0 < conditionedDistanceMean (rule.generation (depth + 1)).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have law := generation_distance_over_childMean_observable rule simple p positive lessOne fixedPoint depth
    (fun distance => distance ^ power)
  have summand (fine : Configuration (rule.generation (depth + 1)).edges) :
      (rule.generation (depth + 1)).network.conditionalCellWeight p true fine *
          (((((rule.generation (depth + 1)).network.openGraph fine).dist
            (rule.generation (depth + 1)).network.source
            (rule.generation (depth + 1)).network.target : ℝ) /
              conditionedDistanceMean (rule.generation depth).network p) ^ power) =
        (conditionedDistanceMean (rule.generation (depth + 1)).network p /
          conditionedDistanceMean (rule.generation depth).network p) ^ power *
          ((rule.generation (depth + 1)).network.conditionalCellWeight p true fine *
            normalizedDistance (rule.generation (depth + 1)).network p fine ^ power) := by
    have rescaling :
        ((((rule.generation (depth + 1)).network.openGraph fine).dist
            (rule.generation (depth + 1)).network.source
            (rule.generation (depth + 1)).network.target : ℝ) /
              conditionedDistanceMean (rule.generation depth).network p) =
          (conditionedDistanceMean (rule.generation (depth + 1)).network p /
            conditionedDistanceMean (rule.generation depth).network p) *
              normalizedDistance (rule.generation (depth + 1)).network p fine := by
      dsimp [normalizedDistance]
      field_simp
    rw [rescaling, mul_pow]
    ring
  simp_rw [summand] at law
  rw [← Finset.mul_sum] at law
  exact law

theorem generation_factorial_moment_preserved (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (derivativePositive : 0 < deriv rule.network.reliability p) (depth power : ℕ)
    {constant : ℝ} (constantNonnegative : 0 ≤ constant)
    (compositionBound : (((longestTerminalPath rule.network + power - 1).choose power : ℕ) : ℝ) ≤
      deriv rule.network.reliability p ^ power)
    (childMoments : ∀ order, order ≤ power →
      normalizedDistanceMoment (rule.generation depth).network p order ≤
        constant ^ order * (order.factorial : ℝ)) :
    normalizedDistanceMoment (rule.generation (depth + 1)).network p power ≤
      constant ^ power * (power.factorial : ℝ) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have parentMomentNonnegative := normalizedDistanceMoment_nonnegative
    (rule.generation (depth + 1)).network positive.le lessOne.le
    (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))) power
  have comparison := selected_path_factorial_moment_bound (rule.network.conditionalCellWeight p true)
    (edgePathFamily rule.network) (selectedTerminalPath rule.network) (selectedTerminalPath_mem rule.network)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight p (coarse edge) cell)
    (fun _ _ cell => normalizedDistance (rule.generation depth).network p cell)
    (fun coarse => rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight_nonneg
      positive.le lessOne.le (coarse edge) cell)
    (fun _ _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
    (fun coarse edge => (rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (coarse edge)) power
    (fun coarse edge membership order orderBound => by
      rw [edgePathFamily_used_edge rule.network simple coarse
        (selectedTerminalPath_mem rule.network coarse) membership]
      exact childMoments order orderBound)
  rw [← generation_normalizedDistanceMoment_product_law rule simple p positive lessOne fixedPoint depth power] at comparison
  have selectedCompositionBound :
      (∑ coarse, rule.network.conditionalCellWeight p true coarse *
        (((selectedTerminalPath rule.network coarse).card + power - 1).choose power : ℝ)) ≤
          deriv rule.network.reliability p ^ power := by
    calc
      _ ≤ ∑ coarse, rule.network.conditionalCellWeight p true coarse *
          deriv rule.network.reliability p ^ power := Finset.sum_le_sum
        (fun coarse _ => mul_le_mul_of_nonneg_left
          ((by exact_mod_cast Nat.choose_le_choose power (Nat.sub_le_sub_right
            (Nat.add_le_add_right (selectedTerminalPath_card_le_longest rule.network simple coarse) power) 1) :
              (((selectedTerminalPath rule.network coarse).card + power - 1).choose power : ℝ) ≤
                ((longestTerminalPath rule.network + power - 1).choose power : ℝ)).trans compositionBound)
          (rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse))
      _ = _ := by
        rw [← Finset.sum_mul, rule.network.sum_conditionalCellWeight p
          (by rwa [fixedPoint]) (by rwa [fixedPoint]) true, one_mul]
  have ratioBound := (generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint depth).1
  have productBound : deriv rule.network.reliability p ^ power *
      normalizedDistanceMoment (rule.generation (depth + 1)).network p power ≤
        deriv rule.network.reliability p ^ power * (constant ^ power * (power.factorial : ℝ)) :=
    ((mul_le_mul_of_nonneg_right (pow_le_pow_left₀ derivativePositive.le ratioBound power)
      parentMomentNonnegative).trans comparison).trans
      (mul_le_mul_of_nonneg_right selectedCompositionBound
        (mul_nonneg (pow_nonneg constantNonnegative power) (Nat.cast_nonneg _)))
  exact (mul_le_mul_iff_of_pos_left (pow_pos derivativePositive power)).mp productBound

theorem exists_uniform_generation_factorial_moments (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    ∃ constant : ℝ, 1 ≤ constant ∧ ∀ depth power,
      normalizedDistanceMoment (rule.generation depth).network p power ≤
        constant ^ power * (power.factorial : ℝ) := by
  have derivativeGreaterOne := rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint scale
  obtain ⟨threshold, thresholdValid⟩ := eventually_weak_compositions_le_geometric
    (longestTerminalPath rule.network) derivativeGreaterOne
  apply exists_uniform_factorial_majorant
    (moment := fun depth power => normalizedDistanceMoment (rule.generation depth).network p power)
  · intro depth
    simp only [normalizedDistanceMoment, pow_zero, mul_one]
    exact (rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) true
  · exact exists_uniform_generation_positive_moment rule simple p positive lessOne fixedPoint scale
  · exact exists_finite_factorial_bound
      ((rule.generation 0).network.conditionalCellWeight p true)
      (normalizedDistance (rule.generation 0).network p)
      (fun configuration => (rule.generation 0).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      (fun configuration => normalizedDistance_nonnegative _
        (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration)
      ((rule.generation 0).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) true)
  · refine ⟨threshold, fun power powerLarge depth constant constantAtLeastOne childMoments => ?_⟩
    exact generation_factorial_moment_preserved rule simple p positive lessOne fixedPoint
      (lt_trans zero_lt_one derivativeGreaterOne) depth power (zero_le_one.trans constantAtLeastOne)
      (thresholdValid power powerLarge) childMoments

def normalizedDistanceExponentialMoment {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p parameter : ℝ) : ℝ :=
  ∑ configuration, network.conditionalCellWeight p true configuration *
    Real.exp (parameter * normalizedDistance network p configuration)

theorem normalizedDistanceExponentialMoment_nonnegative {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (parameter : ℝ) : 0 ≤ normalizedDistanceExponentialMoment network p parameter :=
  Finset.sum_nonneg (fun configuration _ => mul_nonneg
    (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration) (Real.exp_nonneg _))

theorem normalizedDistanceExponentialMoment_atLeastOne {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p parameter : ℝ}
    (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) (parameterNonnegative : 0 ≤ parameter) :
    1 ≤ normalizedDistanceExponentialMoment network p parameter := by
  rw [← network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true]
  apply Finset.sum_le_sum
  intro configuration _
  apply le_mul_of_one_le_right (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
  exact Real.one_le_exp (mul_nonneg parameterNonnegative (normalizedDistance_nonnegative _
    (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ nonnegative atMostOne
      reliabilityPositive reliabilityLessOne)) configuration))

theorem generation_normalized_exponential_moment_step (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    {parameter : ℝ} (parameterNonnegative : 0 ≤ parameter) :
    normalizedDistanceExponentialMoment (rule.generation (depth + 1)).network p
        (deriv rule.network.reliability p * parameter) ≤
      normalizedDistanceExponentialMoment (rule.generation depth).network p parameter ^
        longestTerminalPath rule.network := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have parentMeanPositive : 0 < conditionedDistanceMean (rule.generation (depth + 1)).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  rw [normalizedDistanceExponentialMoment, generation_normalized_distance_observable rule simple p positive lessOne fixedPoint
    depth (fun distance => Real.exp ((deriv rule.network.reliability p * parameter) * distance))]
  apply selected_path_normalized_exponential_moment_bound
    (rule.network.conditionalCellWeight p true)
    (edgePathFamily rule.network) (selectedTerminalPath rule.network) (selectedTerminalPath_mem rule.network)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight p (coarse edge) cell)
    (fun _ _ cell => normalizedDistance (rule.generation depth).network p cell)
    (fun coarse => rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
    (rule.network.sum_conditionalCellWeight p (by rwa [fixedPoint]) (by rwa [fixedPoint]) true)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight_nonneg
      positive.le lessOne.le (coarse edge) cell)
    (fun _ _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
    (fun coarse edge => (rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (coarse edge))
    (div_pos parentMeanPositive childMeanPositive)
    (generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint depth).1
    parameterNonnegative
    (normalizedDistanceExponentialMoment_atLeastOne (rule.generation depth).network positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) parameterNonnegative)
    (selectedTerminalPath_card_le_longest rule.network simple)
  intro coarse edge membership
  rw [edgePathFamily_used_edge rule.network simple coarse
    (selectedTerminalPath_mem rule.network coarse) membership]
  exact le_rfl

theorem exists_uniform_generation_exponential_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) :
    ∃ bound : ℝ, ∀ depth,
      normalizedDistanceExponentialMoment (rule.generation depth).network p parameter ≤ bound := by
  obtain ⟨constant, constantAtLeastOne, factorialBounds⟩ :=
    exists_uniform_generation_factorial_moments rule simple p positive lessOne fixedPoint scale
  have constantPositive : 0 < constant := lt_of_lt_of_le zero_lt_one constantAtLeastOne
  have initialParameterPositive : 0 < 1 / (2 * constant) := by positivity
  have initialParameterSmall : constant * (1 / (2 * constant)) < 1 := by
    have comparison : constant / (2 * constant) < 1 :=
      (div_lt_one (by positivity : 0 < 2 * constant)).mpr (by linarith)
    simpa only [one_div, div_eq_mul_inv, one_mul] using comparison
  apply exists_uniform_exponential_bound_at_every_parameter
    (moment := fun depth argument => normalizedDistanceExponentialMoment (rule.generation depth).network p argument)
    (base := deriv rule.network.reliability p) (initialParameter := 1 / (2 * constant))
    (initialBound := (1 - constant * (1 / (2 * constant)))⁻¹)
    (length := longestTerminalPath rule.network)
    (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint scale)
    initialParameterPositive
    (fun depth => finite_exponential_moment_bound_of_factorial
      ((rule.generation depth).network.conditionalCellWeight p true)
      (normalizedDistance (rule.generation depth).network p) constantPositive.le initialParameterPositive.le
      initialParameterSmall (factorialBounds depth))
    (fun depth argument => normalizedDistanceExponentialMoment_nonnegative _ positive.le lessOne.le argument)
    (by
      intro depth first firstNonnegative second secondNonnegative comparison
      exact finite_exponential_moment_monotone
        ((rule.generation depth).network.conditionalCellWeight p true)
        (normalizedDistance (rule.generation depth).network p)
        (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg
          positive.le lessOne.le true configuration)
        (fun configuration => normalizedDistance_nonnegative _
          (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
            (by rwa [rule.generation_fixed_point p fixedPoint])
            (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration) comparison)
    (fun depth argument argumentNonnegative => generation_normalized_exponential_moment_step
      rule simple p positive lessOne fixedPoint depth argumentNonnegative)
    parameter parameterNonnegative

end
end IGSIII.Chemical.SmallBall
