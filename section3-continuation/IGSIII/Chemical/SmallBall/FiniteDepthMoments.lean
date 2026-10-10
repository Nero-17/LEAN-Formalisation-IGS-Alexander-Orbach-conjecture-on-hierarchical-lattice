import IGSIII.Chemical.SubstitutionPaths.ConditionalLaw
import IGSIII.Chemical.SubstitutionPaths.PivotalPaths
import IGSIII.Chemical.SmallBall.ExponentialMoments
import Universality.Percolation.StrictInstability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Moments of the actual finite-generation chemical distance.  The child
product laws below are the configuration laws proved in IGS II; only edges
belonging to a selected open terminal path use the connected child law. -/

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork Substitution
open scoped BigOperators

noncomputable section

def conditionedDistanceMean {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p : ℝ) : ℝ :=
  ∑ configuration, network.conditionalCellWeight p true configuration *
    ((network.openGraph configuration).dist network.source network.target : ℝ)

def normalizedDistance {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p : ℝ) (configuration : Configuration edges) : ℝ :=
  ((network.openGraph configuration).dist network.source network.target : ℝ) /
    conditionedDistanceMean network p

def normalizedDistanceMoment {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p : ℝ) (power : ℕ) : ℝ :=
  ∑ configuration, network.conditionalCellWeight p true configuration *
    normalizedDistance network p configuration ^ power

def selectedTerminalPath {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Finset (Fin edges) :=
  (edgePathFamily network configuration).nonempty.choose

theorem selectedTerminalPath_mem {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    selectedTerminalPath network configuration ∈ (edgePathFamily network configuration).paths :=
  (edgePathFamily network configuration).nonempty.choose_spec

theorem conditionedDistanceMean_atLeastOne {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) :
    1 ≤ conditionedDistanceMean network p := by
  classical
  rw [← network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true]
  apply Finset.sum_le_sum
  intro configuration _
  by_cases crossing : network.crosses configuration = true
  · have distancePositive := ((network.crosses_eq_true configuration).mp crossing).pos_dist_of_ne
      network.terminals_distinct
    have distanceAtLeastOne : (1 : ℝ) ≤
        (network.openGraph configuration).dist network.source network.target := by
      exact_mod_cast distancePositive
    exact le_mul_of_one_le_right
      (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration) distanceAtLeastOne
  · simp [conditionalCellWeight, crossing]

theorem normalizedDistance_nonnegative {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (meanNonnegative : 0 ≤ conditionedDistanceMean network p)
    (configuration : Configuration edges) : 0 ≤ normalizedDistance network p configuration :=
  div_nonneg (Nat.cast_nonneg _) meanNonnegative

theorem normalizedDistance_mean_one {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ)
    (meanPositive : 0 < conditionedDistanceMean network p) :
    (∑ configuration, network.conditionalCellWeight p true configuration *
      normalizedDistance network p configuration) = 1 := by
  simp only [normalizedDistance, ← mul_div_assoc, ← Finset.sum_div]
  exact div_self meanPositive.ne'

theorem normalizedDistanceMoment_nonnegative {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (meanNonnegative : 0 ≤ conditionedDistanceMean network p) (power : ℕ) :
    0 ≤ normalizedDistanceMoment network p power :=
  Finset.sum_nonneg (fun configuration _ => mul_nonneg
    (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
    (pow_nonneg (normalizedDistance_nonnegative network meanNonnegative configuration) power))

theorem normalizedDistanceMoment_atLeastOne {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1)
    {power : ℕ} (powerPositive : 1 ≤ power) :
    1 ≤ normalizedDistanceMoment network p power := by
  have meanPositive : 0 < conditionedDistanceMean network p :=
    lt_of_lt_of_le zero_lt_one
      (conditionedDistanceMean_atLeastOne network nonnegative atMostOne reliabilityPositive reliabilityLessOne)
  have comparison := (convexOn_rpow (by exact_mod_cast powerPositive : (1 : ℝ) ≤ power)).map_sum_le
    (t := Finset.univ) (w := network.conditionalCellWeight p true)
    (p := normalizedDistance network p)
    (fun configuration _ => network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
    (network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true)
    (fun configuration _ => normalizedDistance_nonnegative network meanPositive.le configuration)
  simpa only [smul_eq_mul, normalizedDistance_mean_one network p meanPositive,
    Real.one_rpow, Real.rpow_natCast, one_pow, normalizedDistanceMoment] using comparison

theorem cellMinPlus_normalizedDistance
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (meanPositive : 0 < conditionedDistanceMean inner p)
    (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) :
    (edgePathFamily outer coarse).shortest (fun edge => normalizedDistance inner p (cells edge)) =
      cellMinPlus outer inner coarse cells / conditionedDistanceMean inner p := by
  simp only [normalizedDistance, div_eq_mul_inv]
  simp_rw [mul_comm _ (conditionedDistanceMean inner p)⁻¹]
  rw [PathFamily.shortest_scale _ _ (inv_nonneg.mpr meanPositive.le),
    cellMinPlus_eq_edgePathFamily_shortest outer inner simple]

theorem generation_distance_over_childMean_observable (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (response : ℝ → ℝ) :
    (∑ fine, (rule.generation (depth + 1)).network.conditionalCellWeight p true fine *
      response (((rule.generation (depth + 1)).network.openGraph fine).dist
        (rule.generation (depth + 1)).network.source
        (rule.generation (depth + 1)).network.target /
          conditionedDistanceMean (rule.generation depth).network p)) =
      ∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response ((edgePathFamily rule.network coarse).shortest
              (fun edge => normalizedDistance (rule.generation depth).network p (cells edge))) := by
  have innerMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  simp_rw [cellMinPlus_normalizedDistance rule.network _ simple p innerMeanPositive]
  exact generation_conditioned_distance_observable rule simple p positive lessOne fixedPoint depth
    (fun distance => response (distance / conditionedDistanceMean (rule.generation depth).network p))

theorem generation_normalized_distance_observable (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (response : ℝ → ℝ) :
    (∑ fine, (rule.generation (depth + 1)).network.conditionalCellWeight p true fine *
      response (normalizedDistance (rule.generation (depth + 1)).network p fine)) =
      ∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response ((edgePathFamily rule.network coarse).shortest
              (fun edge => normalizedDistance (rule.generation depth).network p (cells edge)) /
                (conditionedDistanceMean (rule.generation (depth + 1)).network p /
                  conditionedDistanceMean (rule.generation depth).network p)) := by
  have innerMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have shortestIdentity (coarse : Configuration rule.edges)
      (cells : Fin rule.edges → Configuration (rule.generation depth).edges) :
      (edgePathFamily rule.network coarse).shortest
          (fun edge => normalizedDistance (rule.generation depth).network p (cells edge)) =
        cellMinPlus rule.network (rule.generation depth).network coarse cells /
          conditionedDistanceMean (rule.generation depth).network p := by
    simp only [normalizedDistance, div_eq_mul_inv]
    simp_rw [mul_comm _ (conditionedDistanceMean (rule.generation depth).network p)⁻¹]
    rw [PathFamily.shortest_scale _ _ (inv_nonneg.mpr innerMeanPositive.le),
      cellMinPlus_eq_edgePathFamily_shortest rule.network _ simple]
  have law := generation_conditioned_distance_observable rule simple p positive lessOne fixedPoint depth
    (fun distance => response (distance / conditionedDistanceMean (rule.generation (depth + 1)).network p))
  simp_rw [shortestIdentity, div_div_div_cancel_right₀ innerMeanPositive.ne']
  exact law

theorem selectedTerminalPath_card_le_longest {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) :
    (selectedTerminalPath network configuration).card ≤ longestTerminalPath network := by
  classical
  by_cases crossing : network.crosses configuration = true
  · exact (edgePathFamily_card_bounds network simple configuration crossing
      (selectedTerminalPath_mem network configuration)).2
  · have notReachable : ¬ (network.openGraph configuration).Reachable network.source network.target := by
      simpa only [← network.crosses_eq_true configuration] using crossing
    have membership := selectedTerminalPath_mem network configuration
    simp only [edgePathFamily, dif_neg notReachable, Finset.mem_singleton] at membership
    simp [membership]

theorem generation_conditionedDistanceMean_ratio_bounds (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    deriv rule.network.reliability p ≤
        conditionedDistanceMean (rule.generation (depth + 1)).network p /
          conditionedDistanceMean (rule.generation depth).network p ∧
      conditionedDistanceMean (rule.generation (depth + 1)).network p /
          conditionedDistanceMean (rule.generation depth).network p ≤
        ∑ coarse, rule.network.conditionalCellWeight p true coarse *
          ((selectedTerminalPath rule.network coarse).card : ℝ) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have law := generation_distance_over_childMean_observable rule simple p positive lessOne fixedPoint depth id
  simp only [id_eq, ← mul_div_assoc, ← Finset.sum_div] at law
  have comparison := selected_path_mean_bounds (rule.network.conditionalCellWeight p true)
    (edgePathFamily rule.network) (selectedTerminalPath rule.network) (selectedTerminalPath_mem rule.network)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight p (coarse edge) cell)
    (fun _ _ cell => normalizedDistance (rule.generation depth).network p cell)
    (fun coarse => rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight_nonneg
      positive.le lessOne.le (coarse edge) cell)
    (fun _ _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
    (fun coarse edge => (rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (coarse edge))
    (fun coarse edge membership => by
      rw [edgePathFamily_used_edge rule.network simple coarse
        (selectedTerminalPath_mem rule.network coarse) membership]
      exact normalizedDistance_mean_one _ p childMeanPositive)
  rw [conditioned_commonEdges_mean_eq_reliability_deriv rule.network simple p positive fixedPoint] at comparison
  rw [← law] at comparison
  exact comparison

theorem generation_conditionedDistanceMean_ratio_le_longest (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    conditionedDistanceMean (rule.generation (depth + 1)).network p /
        conditionedDistanceMean (rule.generation depth).network p ≤ longestTerminalPath rule.network := by
  calc
    _ ≤ ∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ((selectedTerminalPath rule.network coarse).card : ℝ) :=
      (generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint depth).2
    _ ≤ ∑ coarse, rule.network.conditionalCellWeight p true coarse * (longestTerminalPath rule.network : ℝ) :=
      Finset.sum_le_sum (fun coarse _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast selectedTerminalPath_card_le_longest rule.network simple coarse)
        (rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse))
    _ = _ := by
      rw [← Finset.sum_mul, rule.network.sum_conditionalCellWeight p
        (by rwa [fixedPoint]) (by rwa [fixedPoint]) true, one_mul]

theorem generation_normalizedDistanceMoment_step (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) :
    (conditionedDistanceMean (rule.generation (depth + 1)).network p /
        conditionedDistanceMean (rule.generation depth).network p) ^ power *
        normalizedDistanceMoment (rule.generation (depth + 1)).network p power ≤
      (∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ((selectedTerminalPath rule.network coarse).card : ℝ)) *
          normalizedDistanceMoment (rule.generation depth).network p power +
      (∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ((selectedTerminalPath rule.network coarse).card : ℝ) ^ power) *
          normalizedDistanceMoment (rule.generation depth).network p power ^
            (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
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
  have comparison := selected_path_moment_bound (rule.network.conditionalCellWeight p true)
    (edgePathFamily rule.network) (selectedTerminalPath rule.network) (selectedTerminalPath_mem rule.network)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight p (coarse edge) cell)
    (fun _ _ cell => normalizedDistance (rule.generation depth).network p cell)
    (fun coarse => rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
    (fun coarse edge cell => (rule.generation depth).network.conditionalCellWeight_nonneg
      positive.le lessOne.le (coarse edge) cell)
    (fun _ _ cell => normalizedDistance_nonnegative _ childMeanPositive.le cell)
    (fun coarse edge => (rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (coarse edge))
    (fun coarse edge membership => by
      rw [edgePathFamily_used_edge rule.network simple coarse
        (selectedTerminalPath_mem rule.network coarse) membership]
      exact normalizedDistance_mean_one _ p childMeanPositive)
    powerAtLeastTwo
    (normalizedDistanceMoment_atLeastOne (rule.generation depth).network (p := p) (power := power)
      positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) (by omega : 1 ≤ power))
    (fun coarse edge membership => by
      rw [edgePathFamily_used_edge rule.network simple coarse
        (selectedTerminalPath_mem rule.network coarse) membership]
      exact le_rfl)
  rw [← law] at comparison
  exact comparison

theorem generation_normalizedDistanceMoment_contraction (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (derivativePositive : 0 < deriv rule.network.reliability p) (depth : ℕ)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) :
    normalizedDistanceMoment (rule.generation (depth + 1)).network p power ≤
      ((longestTerminalPath rule.network : ℝ) / deriv rule.network.reliability p ^ power) *
          normalizedDistanceMoment (rule.generation depth).network p power +
      ((longestTerminalPath rule.network : ℝ) ^ power / deriv rule.network.reliability p ^ power) *
          normalizedDistanceMoment (rule.generation depth).network p power ^
            (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have childMomentNonnegative := normalizedDistanceMoment_nonnegative _ positive.le lessOne.le
    childMeanPositive.le power
  have parentMomentNonnegative := normalizedDistanceMoment_nonnegative
    (rule.generation (depth + 1)).network positive.le lessOne.le
    (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))) power
  have selectedBound (order : ℕ) :
      (∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ((selectedTerminalPath rule.network coarse).card : ℝ) ^ order) ≤
          (longestTerminalPath rule.network : ℝ) ^ order := by
    calc
      _ ≤ ∑ coarse, rule.network.conditionalCellWeight p true coarse *
          (longestTerminalPath rule.network : ℝ) ^ order := Finset.sum_le_sum
        (fun coarse _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _)
            (by exact_mod_cast selectedTerminalPath_card_le_longest rule.network simple coarse) order)
          (rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse))
      _ = _ := by
        rw [← Finset.sum_mul, rule.network.sum_conditionalCellWeight p
          (by rwa [fixedPoint]) (by rwa [fixedPoint]) true, one_mul]
  have pureBound := selectedBound 1
  simp only [pow_one] at pureBound
  have stepBound := generation_normalizedDistanceMoment_step rule simple p positive lessOne fixedPoint depth powerAtLeastTwo
  have lowerRatio := (generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint depth).1
  have productBound : deriv rule.network.reliability p ^ power *
      normalizedDistanceMoment (rule.generation (depth + 1)).network p power ≤
        (longestTerminalPath rule.network : ℝ) * normalizedDistanceMoment (rule.generation depth).network p power +
          (longestTerminalPath rule.network : ℝ) ^ power *
            normalizedDistanceMoment (rule.generation depth).network p power ^
              (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) := by
    calc
      _ ≤ _ := (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ derivativePositive.le lowerRatio power) parentMomentNonnegative).trans stepBound
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right pureBound childMomentNonnegative)
        (mul_le_mul_of_nonneg_right (selectedBound power) (Real.rpow_nonneg childMomentNonnegative _))
  have divided := (le_div_iff₀ (pow_pos derivativePositive power)).mpr
    (show normalizedDistanceMoment (rule.generation (depth + 1)).network p power *
      deriv rule.network.reliability p ^ power ≤ _ from
      (mul_comm _ _).trans_le productBound)
  simpa only [add_div, div_mul_eq_mul_div] using divided

theorem exists_uniform_generation_moment_of_contraction (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (derivativePositive : 0 < deriv rule.network.reliability p)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power)
    (pureContraction : (longestTerminalPath rule.network : ℝ) < deriv rule.network.reliability p ^ power) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ depth,
      normalizedDistanceMoment (rule.generation depth).network p power ≤ bound := by
  have denominatorPositive : 0 < (power : ℝ) - 1 := by
    have : (2 : ℝ) ≤ power := by exact_mod_cast powerAtLeastTwo
    linarith
  have exponentBelowOne : (((power - 2 : ℕ) : ℝ) / ((power : ℝ) - 1)) < 1 := by
    rw [div_lt_one denominatorPositive, Nat.cast_sub powerAtLeastTwo, Nat.cast_ofNat]
    linarith
  exact exists_uniform_bound_of_sublinear_recursion
    (div_nonneg (Nat.cast_nonneg _) (pow_nonneg derivativePositive.le power))
    ((div_lt_one (pow_pos derivativePositive power)).mpr pureContraction)
    (div_nonneg (pow_nonneg (Nat.cast_nonneg _) power) (pow_nonneg derivativePositive.le power))
    (div_nonneg (Nat.cast_nonneg _) denominatorPositive.le) exponentBelowOne
    (fun depth => normalizedDistanceMoment_nonnegative _ positive.le lessOne.le
      (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))) power)
    (fun depth => generation_normalizedDistanceMoment_contraction rule simple p positive lessOne fixedPoint
      derivativePositive depth powerAtLeastTwo)

theorem normalizedDistanceMoment_le_one_add_higher {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1)
    {order power : ℕ} (orderBound : order ≤ power) :
    normalizedDistanceMoment network p order ≤ 1 + normalizedDistanceMoment network p power := by
  have meanPositive : 0 < conditionedDistanceMean network p := lt_of_lt_of_le zero_lt_one
    (conditionedDistanceMean_atLeastOne network nonnegative atMostOne reliabilityPositive reliabilityLessOne)
  have pointwise (configuration : Configuration edges) :
      normalizedDistance network p configuration ^ order ≤
        1 + normalizedDistance network p configuration ^ power := by
    have valueNonnegative := normalizedDistance_nonnegative network meanPositive.le configuration
    by_cases atMostOneValue : normalizedDistance network p configuration ≤ 1
    · have comparison := pow_le_pow_left₀ valueNonnegative atMostOneValue order
      simpa only [one_pow] using comparison.trans
        (le_add_of_nonneg_right (pow_nonneg valueNonnegative power))
    · exact (pow_le_pow_right₀ (le_of_not_ge atMostOneValue) orderBound).trans
        (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ ∑ configuration, network.conditionalCellWeight p true configuration *
        (1 + normalizedDistance network p configuration ^ power) := Finset.sum_le_sum
      (fun configuration _ => mul_le_mul_of_nonneg_left (pointwise configuration)
        (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration))
    _ = _ := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib,
        network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true, normalizedDistanceMoment]

theorem exists_uniform_generation_positive_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) (order : ℕ) :
    ∃ bound : ℝ, ∀ depth, normalizedDistanceMoment (rule.generation depth).network p order ≤ bound := by
  have derivativeGreaterOne := rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint scale
  obtain ⟨power, powerLarge⟩ := pow_unbounded_of_one_lt (longestTerminalPath rule.network : ℝ) derivativeGreaterOne
  have pureContraction : (longestTerminalPath rule.network : ℝ) <
      deriv rule.network.reliability p ^ max 2 (max order power) :=
    powerLarge.trans_le (pow_le_pow_right₀ derivativeGreaterOne.le
      ((le_max_right order power).trans (le_max_right 2 _)))
  obtain ⟨bound, boundAtLeastOne, boundValid⟩ := exists_uniform_generation_moment_of_contraction
    rule simple p positive lessOne fixedPoint (lt_trans zero_lt_one derivativeGreaterOne)
    (le_max_left 2 _) pureContraction
  refine ⟨1 + bound, fun depth => ?_⟩
  exact (normalizedDistanceMoment_le_one_add_higher (rule.generation depth).network positive.le lessOne.le
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint])
    ((le_max_left order power).trans (le_max_right 2 _))).trans
      (by linarith [boundValid depth])

end
end IGSIII.Chemical.SmallBall
