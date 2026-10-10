import IGSIII.Chemical.SmallBall.FiniteDepthIndexing
import IGSIII.Chemical.SmallBall.PathCountMoments
import IGSIII.Chemical.SmallBall.Growth
import IGSIII.Chemical.SubstitutionPaths.BlockPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork Substitution
open scoped BigOperators

noncomputable section

def unitMinimizingTerminalPath {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Finset (Fin edges) :=
  ((edgePathFamily network configuration).exists_minimizer (fun _ => 1)).choose

theorem unitMinimizingTerminalPath_mem {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    unitMinimizingTerminalPath network configuration ∈ (edgePathFamily network configuration).paths :=
  ((edgePathFamily network configuration).exists_minimizer (fun _ => 1)).choose_spec.1

theorem unitMinimizingTerminalPath_card {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) :
    ((unitMinimizingTerminalPath network configuration).card : ℝ) =
      (network.openGraph configuration).dist network.source network.target := by
  have minimum := ((edgePathFamily network configuration).exists_minimizer (fun _ => 1)).choose_spec.2
  change (edgePathFamily network configuration).shortest (fun _ => 1) =
    PathFamily.pathCost (unitMinimizingTerminalPath network configuration) (fun _ => 1) at minimum
  rw [edgePathFamily_shortest_unit network simple configuration] at minimum
  simpa only [unitMinimizingTerminalPath, PathFamily.pathCost, Finset.sum_const, nsmul_eq_mul, mul_one] using minimum.symm

theorem generation_block_mean_over_childMean (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ) :
    conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p /
        conditionedDistanceMean (rule.generation fine).network p =
      ∑ outerConfiguration, (rule.generation coarse).network.conditionalCellWeight p true outerConfiguration *
        ∑ cells : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
          (∏ edge, (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge) (cells edge)) *
            (edgePathFamily (rule.generation coarse).network outerConfiguration).shortest
              (fun edge => normalizedDistance (rule.generation fine).network p (cells edge)) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation fine).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have law := generation_block_conditioned_distance_observable rule classical p positive lessOne fixedPoint coarse fine
    (fun distance => distance / conditionedDistanceMean (rule.generation fine).network p)
  simp only [← mul_div_assoc, ← Finset.sum_div] at law
  simp_rw [cellMinPlus_normalizedDistance _ _ (classical.generation coarse).simple p childMeanPositive]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact law

theorem generation_conditionedDistanceMean_upper_product (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ) :
    conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p ≤
      conditionedDistanceMean (rule.generation coarse).network p *
        conditionedDistanceMean (rule.generation fine).network p := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation fine).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have comparison := (selected_path_mean_bounds
    ((rule.generation coarse).network.conditionalCellWeight p true)
    (edgePathFamily (rule.generation coarse).network)
    (unitMinimizingTerminalPath (rule.generation coarse).network)
    (unitMinimizingTerminalPath_mem (rule.generation coarse).network)
    (fun outerConfiguration edge cell => (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge) cell)
    (fun _ _ cell => normalizedDistance (rule.generation fine).network p cell)
    (fun outerConfiguration => (rule.generation coarse).network.conditionalCellWeight_nonneg positive.le lessOne.le true outerConfiguration)
    (fun outerConfiguration edge cell => (rule.generation fine).network.conditionalCellWeight_nonneg
      positive.le lessOne.le (outerConfiguration edge) cell)
    (fun _ _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
    (fun outerConfiguration edge => (rule.generation fine).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (outerConfiguration edge))
    (fun outerConfiguration edge membership => by
      rw [edgePathFamily_used_edge _ (classical.generation coarse).simple outerConfiguration
        (unitMinimizingTerminalPath_mem _ outerConfiguration) membership]
      exact normalizedDistance_mean_one _ p childMeanPositive)).2
  simp_rw [unitMinimizingTerminalPath_card _ (classical.generation coarse).simple] at comparison
  rw [← generation_block_mean_over_childMean rule classical p positive lessOne fixedPoint coarse fine] at comparison
  exact (div_le_iff₀ childMeanPositive).mp comparison

theorem exists_generation_conditionedDistanceMean_lower_product (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 ∧ ∀ coarse fine,
      constant * conditionedDistanceMean (rule.generation coarse).network p *
          conditionedDistanceMean (rule.generation fine).network p ≤
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p := by
  have pathCountPositive : 0 < (((rule.edges + 3) ^ 4 : ℕ) : ℝ) := by positivity
  have laplacePositive : 0 < 1 / (8 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ)) := by positivity
  obtain ⟨parameter, parameterPositive, laplaceBound⟩ := exists_uniform_generation_laplace_decay
    rule classical.simple p positive lessOne fixedPoint classical.scale laplacePositive
  have speedPositive : 0 < Real.log 2 / parameter := div_pos (Real.log_pos (by norm_num)) parameterPositive
  have exponentialIdentity : Real.exp (parameter * (Real.log 2 / parameter)) = 2 := by
    have exponentIdentity : parameter * (Real.log 2 / parameter) = Real.log 2 := by field_simp
    rw [exponentIdentity, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have geometricIdentity : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (Real.exp (parameter * (Real.log 2 / parameter)) *
        (1 / (8 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ)))) = (1 / 4 : ℝ) := by
    rw [exponentialIdentity]
    field_simp
    norm_num
  refine ⟨min 1 ((Real.log 2 / parameter) / 2), by positivity, min_le_left _ _, fun coarse fine => ?_⟩
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation fine).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have rootBound (configuration : Configuration (rule.generation coarse).edges)
      (crossing : (rule.generation coarse).network.crosses configuration = true) :
      ((Real.log 2 / parameter) / 2) *
          (((rule.generation coarse).network.openGraph configuration).dist
            (rule.generation coarse).network.source (rule.generation coarse).network.target : ℝ) ≤
        ∑ cells : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
          (∏ edge, (rule.generation fine).network.conditionalCellWeight p (configuration edge) (cells edge)) *
            (edgePathFamily (rule.generation coarse).network configuration).shortest
              (fun edge => normalizedDistance (rule.generation fine).network p (cells edge)) := by
    rw [← edgePathFamily_shortest_unit _ (classical.generation coarse).simple configuration]
    apply finite_product_shortest_mean_lower
      (edgePathFamily (rule.generation coarse).network configuration)
      (fun path membership => by
        have lower := (edgePathFamily_card_bounds _ (classical.generation coarse).simple configuration crossing membership).1
        have scale := (classical.generation coarse).scale
        omega)
      (fun edge cell => (rule.generation fine).network.conditionalCellWeight p (configuration edge) cell)
      (fun _ cell => normalizedDistance (rule.generation fine).network p cell)
      (fun edge cell => (rule.generation fine).network.conditionalCellWeight_nonneg positive.le lessOne.le (configuration edge) cell)
      (fun edge => (rule.generation fine).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) (configuration edge))
      (fun _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
      parameterPositive.le laplacePositive.le speedPositive.le pathCountPositive.le
      (fun path membership edge edgeMembership => by
        rw [edgePathFamily_used_edge _ (classical.generation coarse).simple configuration membership edgeMembership]
        exact laplaceBound fine)
      (fun size => by exact_mod_cast actual_edgePathFamily_length_count rule classical coarse size configuration)
      (by rw [geometricIdentity]; norm_num)
      (by rw [geometricIdentity]; norm_num)
  have averaged : min 1 ((Real.log 2 / parameter) / 2) *
      conditionedDistanceMean (rule.generation coarse).network p ≤
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p /
          conditionedDistanceMean (rule.generation fine).network p := by
    rw [generation_block_mean_over_childMean rule classical p positive lessOne fixedPoint coarse fine,
      conditionedDistanceMean, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro configuration _
    by_cases crossing : (rule.generation coarse).network.crosses configuration = true
    · have comparison := (mul_le_mul_of_nonneg_right (min_le_right 1 ((Real.log 2 / parameter) / 2))
        (by positivity : 0 ≤ (((rule.generation coarse).network.openGraph configuration).dist
          (rule.generation coarse).network.source (rule.generation coarse).network.target : ℝ))).trans (rootBound configuration crossing)
      have weighted := mul_le_mul_of_nonneg_left comparison
        ((rule.generation coarse).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      simpa only [mul_assoc, mul_left_comm] using weighted
    · simp [conditionalCellWeight, crossing]
  exact (le_div_iff₀ childMeanPositive).mp averaged

theorem conditionedDistanceMean_graph_bounds {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) :
    (network.fullGraph.dist network.source network.target : ℝ) ≤ conditionedDistanceMean network p ∧
      conditionedDistanceMean network p ≤ longestTerminalPath network := by
  have pointwise (configuration : Configuration edges) (crossing : network.crosses configuration = true) :
      (network.fullGraph.dist network.source network.target : ℝ) ≤
          (network.openGraph configuration).dist network.source network.target ∧
        ((network.openGraph configuration).dist network.source network.target : ℝ) ≤ longestTerminalPath network := by
    rw [← edgePathFamily_shortest_unit network simple configuration]
    constructor
    · apply PathFamily.le_shortest
      intro path membership
      simpa only [PathFamily.pathCost, Finset.sum_const, nsmul_eq_mul, mul_one] using
        (show (network.fullGraph.dist network.source network.target : ℝ) ≤ (path.card : ℝ) from
          by exact_mod_cast (edgePathFamily_card_bounds network simple configuration crossing membership).1)
    · have selected := selectedTerminalPath_mem network configuration
      have comparison : (edgePathFamily network configuration).shortest (fun _ => 1) ≤
          (selectedTerminalPath network configuration).card := by
        simpa only [PathFamily.pathCost, Finset.sum_const, nsmul_eq_mul, mul_one] using
          (edgePathFamily network configuration).shortest_le_pathCost (fun _ => 1) selected
      exact comparison.trans
          (by exact_mod_cast selectedTerminalPath_card_le_longest network simple configuration)
  have averagedLower : (∑ configuration, network.conditionalCellWeight p true configuration *
      (network.fullGraph.dist network.source network.target : ℝ)) ≤ conditionedDistanceMean network p := by
    apply Finset.sum_le_sum
    intro configuration _
    by_cases crossing : network.crosses configuration = true
    · exact mul_le_mul_of_nonneg_left (pointwise configuration crossing).1
        (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
    · simp [conditionalCellWeight, crossing]
  have averagedUpper : conditionedDistanceMean network p ≤
      ∑ configuration, network.conditionalCellWeight p true configuration * (longestTerminalPath network : ℝ) := by
    apply Finset.sum_le_sum
    intro configuration _
    by_cases crossing : network.crosses configuration = true
    · exact mul_le_mul_of_nonneg_left (pointwise configuration crossing).2
        (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
    · simp [conditionalCellWeight, crossing]
  simp only [← Finset.sum_mul, network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true, one_mul]
    at averagedLower averagedUpper
  exact ⟨averagedLower, averagedUpper⟩

theorem manuscriptDistanceMean_power_bounds (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ (longestTerminalPath rule.network : ℝ) ^ depth := by
  cases depth with
  | zero => simp [manuscriptDistanceMean]
  | succ depth =>
      have lower := (conditionedDistanceMean_graph_bounds (rule.generation depth).network (classical.generation depth).simple
        positive.le lessOne.le (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint])).1
      rw [rule.generation_terminal_distance (classical.connected _) depth, Nat.cast_pow] at lower
      have initialUpper := (conditionedDistanceMean_graph_bounds rule.network classical.simple positive.le lessOne.le
        (by rwa [fixedPoint]) (by rwa [fixedPoint])).2
      have upper := (generation_conditionedDistanceMean_upper rule classical.simple p positive lessOne fixedPoint depth).trans
        (mul_le_mul_of_nonneg_right initialUpper (pow_nonneg (Nat.cast_nonneg _) depth))
      refine ⟨lower, ?_⟩
      simpa only [manuscriptDistanceMean, pow_succ, mul_comm] using upper

theorem manuscriptDistanceMean_upper_product (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (first second : ℕ) :
    manuscriptDistanceMean rule p (first + second) ≤ manuscriptDistanceMean rule p first * manuscriptDistanceMean rule p second := by
  cases first with
  | zero => simp [manuscriptDistanceMean]
  | succ first =>
      cases second with
      | zero => simp [manuscriptDistanceMean]
      | succ second =>
          change conditionedDistanceMean (rule.generation (first + 1 + second)).network p ≤
            conditionedDistanceMean (rule.generation first).network p *
              conditionedDistanceMean (rule.generation second).network p
          convert generation_conditionedDistanceMean_upper_product rule classical p positive lessOne fixedPoint first second using 1 <;>
            congr 3 <;> omega

theorem exists_manuscriptDistanceMean_lower_product (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 ∧ ∀ first second,
      constant * manuscriptDistanceMean rule p first * manuscriptDistanceMean rule p second ≤ manuscriptDistanceMean rule p (first + second) := by
  obtain ⟨constant, constantPositive, constantAtMostOne, valid⟩ :=
    exists_generation_conditionedDistanceMean_lower_product rule classical p positive lessOne fixedPoint
  have meansNonnegative (depth : ℕ) : 0 ≤ manuscriptDistanceMean rule p depth :=
    (pow_nonneg (Nat.cast_nonneg _) depth).trans (manuscriptDistanceMean_power_bounds rule classical p positive lessOne fixedPoint depth).1
  refine ⟨constant, constantPositive, constantAtMostOne, fun first second => ?_⟩
  cases first with
  | zero =>
      simpa only [Nat.zero_add, manuscriptDistanceMean, mul_one, one_mul] using
        mul_le_mul_of_nonneg_right constantAtMostOne (meansNonnegative second)
  | succ first =>
      cases second with
      | zero =>
          simpa only [Nat.add_zero, manuscriptDistanceMean, mul_one, one_mul] using
            mul_le_mul_of_nonneg_right constantAtMostOne (meansNonnegative (first + 1))
      | succ second =>
          change constant * conditionedDistanceMean (rule.generation first).network p *
            conditionedDistanceMean (rule.generation second).network p ≤
              conditionedDistanceMean (rule.generation (first + 1 + second)).network p
          convert valid first second using 1 <;> congr 3 <;> omega

theorem exists_actual_chemical_growth (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧ ∀ depth,
        growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
          manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth := by
  obtain ⟨constant, constantPositive, constantAtMostOne, lowerProduct⟩ :=
    exists_manuscriptDistanceMean_lower_product rule classical p positive lessOne fixedPoint
  obtain ⟨growth, growthLower, growthUpper, bounds⟩ := quasi_multiplicative_growth_between
    (means := manuscriptDistanceMean rule p) rfl
    (by exact_mod_cast classical.scale.le : (1 : ℝ) ≤ rule.network.fullGraph.dist rule.network.source rule.network.target)
    (fun depth => (manuscriptDistanceMean_power_bounds rule classical p positive lessOne fixedPoint depth).1)
    (fun depth => (manuscriptDistanceMean_power_bounds rule classical p positive lessOne fixedPoint depth).2)
    constantPositive constantAtMostOne
    (manuscriptDistanceMean_upper_product rule classical p positive lessOne fixedPoint) lowerProduct
  exact ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, bounds⟩

end
end IGSIII.Chemical.SmallBall
