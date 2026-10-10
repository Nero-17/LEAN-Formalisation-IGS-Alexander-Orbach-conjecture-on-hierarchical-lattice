import IGSIII.Chemical.SmallBall.FiniteDepthMoments
import IGSIII.Chemical.SmallBall.FiniteProbability
import IGSIII.Chemical.SubstitutionPaths.RetentionLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork Substitution
open scoped BigOperators

noncomputable section

def normalizedDistanceTail {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p threshold : ℝ) : ℝ :=
  ∑ configuration, network.conditionalCellWeight p true configuration *
    (if normalizedDistance network p configuration ≤ threshold then 1 else 0)

/-- A positive completion only on zero-weight noncrossing configurations. -/
def completedNormalizedDistance {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (p : ℝ) (configuration : Configuration edges) : ℝ :=
  if network.crosses configuration then normalizedDistance network p configuration else 1

theorem conditioned_completion_observable {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (p : ℝ) (response : ℝ → ℝ) :
    (∑ configuration, network.conditionalCellWeight p true configuration *
      response (completedNormalizedDistance network p configuration)) =
        ∑ configuration, network.conditionalCellWeight p true configuration *
          response (normalizedDistance network p configuration) := by
  apply Finset.sum_congr rfl
  intro configuration _
  cases crossing : network.crosses configuration <;>
    simp [completedNormalizedDistance, conditionalCellWeight, crossing]

theorem completedNormalizedDistance_lower {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) (configuration : Configuration edges) :
    1 / conditionedDistanceMean network p ≤ completedNormalizedDistance network p configuration := by
  have meanAtLeastOne := conditionedDistanceMean_atLeastOne network nonnegative atMostOne reliabilityPositive reliabilityLessOne
  have meanPositive := lt_of_lt_of_le zero_lt_one meanAtLeastOne
  by_cases crossing : network.crosses configuration = true
  · have distancePositive := ((network.crosses_eq_true configuration).mp crossing).pos_dist_of_ne network.terminals_distinct
    have distanceAtLeastOne : (1 : ℝ) ≤ (network.openGraph configuration).dist network.source network.target := by
      exact_mod_cast distancePositive
    simpa only [completedNormalizedDistance, crossing, if_true, normalizedDistance] using
      (div_le_div_iff_of_pos_right meanPositive).mpr distanceAtLeastOne
  · simp only [completedNormalizedDistance, Bool.not_eq_true] at crossing ⊢
    rw [crossing]
    simpa only [Bool.false_eq_true, if_false, div_one] using one_div_le_one_div_of_le zero_lt_one meanAtLeastOne

theorem completedNormalizedDistance_positive {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) (configuration : Configuration edges) :
    0 < completedNormalizedDistance network p configuration :=
  lt_of_lt_of_le (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one
    (conditionedDistanceMean_atLeastOne network nonnegative atMostOne reliabilityPositive reliabilityLessOne)))
    (completedNormalizedDistance_lower network nonnegative atMostOne reliabilityPositive reliabilityLessOne configuration)

theorem normalizedDistanceTail_nonnegative {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (threshold : ℝ) : 0 ≤ normalizedDistanceTail network p threshold :=
  Finset.sum_nonneg (fun configuration _ => mul_nonneg
    (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration) (by split <;> positivity))

theorem normalizedDistanceTail_atMostOne {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (reliabilityPositive : 0 < network.reliability p)
    (reliabilityLessOne : network.reliability p < 1) (threshold : ℝ) :
    normalizedDistanceTail network p threshold ≤ 1 := by
  rw [← network.sum_conditionalCellWeight p reliabilityPositive reliabilityLessOne true]
  apply Finset.sum_le_sum
  intro configuration _
  split
  · simp
  · simpa using network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration

theorem normalizedDistanceTail_monotone {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) {p : ℝ} (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1) :
    Monotone (normalizedDistanceTail network p) := by
  intro first second comparison
  apply Finset.sum_le_sum
  intro configuration _
  apply mul_le_mul_of_nonneg_left _ (network.conditionalCellWeight_nonneg nonnegative atMostOne true configuration)
  by_cases firstSmall : normalizedDistance network p configuration ≤ first
  · simp [firstSmall, firstSmall.trans comparison]
  · simp [firstSmall]; split <;> positivity

theorem generation_conditionedDistanceMean_upper (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) :
    conditionedDistanceMean (rule.generation depth).network p ≤
      conditionedDistanceMean rule.network p * (longestTerminalPath rule.network : ℝ) ^ depth := by
  induction depth with
  | zero => simp [Rule.generation]
  | succ depth inductionHypothesis =>
      have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
        lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]))
      have stepBound := (div_le_iff₀ childMeanPositive).mp
        (generation_conditionedDistanceMean_ratio_le_longest rule simple p positive lessOne fixedPoint depth)
      calc
        _ ≤ _ := stepBound
        _ ≤ (longestTerminalPath rule.network : ℝ) *
            (conditionedDistanceMean rule.network p * (longestTerminalPath rule.network : ℝ) ^ depth) :=
          mul_le_mul_of_nonneg_left inductionHypothesis (Nat.cast_nonneg _)
        _ = _ := by rw [pow_succ]; ring

theorem retained_edges_preserve_terminal_path {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration retained : Configuration edges)
    (crossing : network.crosses configuration = true) {path : Finset (Fin edges)}
    (membership : path ∈ (edgePathFamily network configuration).paths)
    (retention : ∀ edge ∈ path, retained edge = true) : network.crosses retained = true := by
  classical
  have reachable := (network.crosses_eq_true _).mp crossing
  simp only [edgePathFamily, dif_pos reachable] at membership
  obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
  obtain ⟨walk, _, rfl⟩ := (mem_graphPathFamily _ network.source network.target reachable bondPath).mp bondMembership
  apply (network.crosses_eq_true _).mpr
  refine ⟨walk.transfer (network.openGraph retained) ?_⟩
  intro bond bondMembership
  revert bondMembership
  refine Sym2.inductionOn bond (fun source target bondMembership => ?_)
  obtain ⟨distinct, edge, _, endpoints | endpoints⟩ := walk.adj_of_mem_edges bondMembership
  · refine ⟨distinct, edge, retention edge ?_, Or.inl endpoints⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [endpoints]
    exact List.mem_toFinset.mpr bondMembership
  · refine ⟨distinct, edge, retention edge ?_, Or.inr endpoints⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [endpoints, Sym2.eq_swap]
    exact List.mem_toFinset.mpr bondMembership

theorem small_shortest_crosses_retained_configuration {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (cost : Fin edges → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge) {threshold : ℝ}
    (small : (edgePathFamily network configuration).shortest cost ≤ threshold) :
    network.crosses (fun edge => configuration edge && decide (cost edge ≤ threshold)) = true := by
  classical
  obtain ⟨path, membership, edgeBound⟩ := (edgePathFamily network configuration).low_cost_path_has_low_cost_edges nonnegative small
  apply retained_edges_preserve_terminal_path network configuration _ crossing membership
  intro edge edgeMembership
  simp only [edgePathFamily_used_edge network simple configuration membership edgeMembership,
    Bool.true_and, decide_eq_true_eq]
  exact edgeBound edge edgeMembership

theorem generation_normalizedDistanceTail_step (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ)
    {threshold : ℝ} (thresholdNonnegative : 0 ≤ threshold) :
    normalizedDistanceTail (rule.generation (depth + 1)).network p threshold ≤
      thinningMap rule.network p
        (normalizedDistanceTail (rule.generation depth).network p
          ((longestTerminalPath rule.network : ℝ) * threshold)) := by
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have parentMeanPositive : 0 < conditionedDistanceMean (rule.generation (depth + 1)).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  rw [normalizedDistanceTail, generation_normalized_distance_observable rule simple p positive lessOne fixedPoint
    depth (fun distance => if distance ≤ threshold then 1 else 0)]
  calc
    _ ≤ ∑ coarse, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            (if rule.network.crosses (fun edge => coarse edge && decide
                (normalizedDistance (rule.generation depth).network p (cells edge) ≤
                  (longestTerminalPath rule.network : ℝ) * threshold)) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro coarse _
      by_cases crossing : rule.network.crosses coarse = true
      · apply mul_le_mul_of_nonneg_left _ (rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true coarse)
        apply Finset.sum_le_sum
        intro cells _
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun edge _ =>
          (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le (coarse edge) (cells edge)))
        by_cases small : (edgePathFamily rule.network coarse).shortest
            (fun edge => normalizedDistance (rule.generation depth).network p (cells edge)) /
              (conditionedDistanceMean (rule.generation (depth + 1)).network p /
                conditionedDistanceMean (rule.generation depth).network p) ≤ threshold
        · have smallCost := (div_le_iff₀ (div_pos parentMeanPositive childMeanPositive)).mp small
          have costBound := smallCost.trans (mul_le_mul_of_nonneg_left
            (generation_conditionedDistanceMean_ratio_le_longest rule simple p positive lessOne fixedPoint depth)
            thresholdNonnegative)
          have retainedCrossing := small_shortest_crosses_retained_configuration rule.network simple coarse crossing
            (fun edge => normalizedDistance (rule.generation depth).network p (cells edge))
            (fun edge => normalizedDistance_nonnegative _ childMeanPositive.le (cells edge))
            (threshold := (longestTerminalPath rule.network : ℝ) * threshold)
            (by simpa only [mul_comm] using costBound)
          simp only [small, if_true, retainedCrossing]
          exact le_rfl
        · simp only [small, if_false]; split <;> positivity
      · simp [conditionalCellWeight, crossing]
    _ = _ := by
      rw [actual_conditional_child_thinning rule.network (rule.generation depth).network p
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) fixedPoint
        (fun cell => decide (normalizedDistance (rule.generation depth).network p cell ≤
          (longestTerminalPath rule.network : ℝ) * threshold))]
      simp only [connectedRetentionProbability, normalizedDistanceTail, thinningMap, decide_eq_true_eq]

theorem longestTerminalPath_greaterOne (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    1 < (longestTerminalPath rule.network : ℝ) :=
  (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint scale).trans_le
    ((generation_conditionedDistanceMean_ratio_bounds rule simple p positive lessOne fixedPoint 0).1.trans
      (generation_conditionedDistanceMean_ratio_le_longest rule simple p positive lessOne fixedPoint 0))

theorem generation_normalizedDistanceTail_shallow_zero (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    {cutoff : ℝ} (cutoffSmall : cutoff < 1 / conditionedDistanceMean rule.network p)
    (depth level : ℕ) (shallow : depth < level) :
    normalizedDistanceTail (rule.generation depth).network p
      (cutoff / (longestTerminalPath rule.network : ℝ) ^ level) = 0 := by
  have initialMeanPositive : 0 < conditionedDistanceMean rule.network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [fixedPoint]) (by rwa [fixedPoint]))
  have longestGreaterOne := longestTerminalPath_greaterOne rule simple p positive lessOne fixedPoint scale
  have longestPositive := lt_trans zero_lt_one longestGreaterOne
  have childMeanPositive : 0 < conditionedDistanceMean (rule.generation depth).network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]))
  have lower (configuration : Configuration (rule.generation depth).edges) :
      (1 / conditionedDistanceMean rule.network p) / (longestTerminalPath rule.network : ℝ) ^ depth ≤
        completedNormalizedDistance (rule.generation depth).network p configuration := by
    have meanBound := generation_conditionedDistanceMean_upper rule simple p positive lessOne fixedPoint depth
    have reciprocalBound := one_div_le_one_div_of_le childMeanPositive meanBound
    have completedBound := completedNormalizedDistance_lower (rule.generation depth).network positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) configuration
    rw [div_div] at ⊢
    exact reciprocalBound.trans completedBound
  have strictLower (configuration : Configuration (rule.generation depth).edges) :
      cutoff / (longestTerminalPath rule.network : ℝ) ^ level <
        completedNormalizedDistance (rule.generation depth).network p configuration := by
    have powerComparison := pow_le_pow_right₀ longestGreaterOne.le shallow.le
    have reciprocalComparison := one_div_le_one_div_of_le (pow_pos longestPositive depth) powerComparison
    have cutoffComparison := (div_lt_div_iff_of_pos_right (pow_pos longestPositive level)).mpr cutoffSmall
    have scaleComparison := mul_le_mul_of_nonneg_left reciprocalComparison (one_div_nonneg.mpr initialMeanPositive.le)
    have scaleComparison' : (1 / conditionedDistanceMean rule.network p) /
        (longestTerminalPath rule.network : ℝ) ^ level ≤
          (1 / conditionedDistanceMean rule.network p) / (longestTerminalPath rule.network : ℝ) ^ depth := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using scaleComparison
    exact cutoffComparison.trans_le (scaleComparison'.trans (lower configuration))
  rw [normalizedDistanceTail, ← conditioned_completion_observable _ p
    (fun value => if value ≤ cutoff / (longestTerminalPath rule.network : ℝ) ^ level then 1 else 0)]
  apply Finset.sum_eq_zero
  intro configuration _
  simp [not_le_of_gt (strictLower configuration)]

theorem exists_uniform_generation_thinning_tail_bound (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    ∃ cutoff start : ℝ, 0 < cutoff ∧ 0 ≤ start ∧ start < 1 ∧ ∀ depth level,
      normalizedDistanceTail (rule.generation depth).network p
        (cutoff / (longestTerminalPath rule.network : ℝ) ^ level) ≤
          (thinningMap rule.network p)^[level] start := by
  obtain ⟨secondMomentBound, secondMomentValid⟩ :=
    exists_uniform_generation_positive_moment rule simple p positive lessOne fixedPoint scale 2
  have secondMomentPositive : 0 < max 1 secondMomentBound := zero_lt_one.trans_le (le_max_left _ _)
  have initial (depth : ℕ) : normalizedDistanceTail (rule.generation depth).network p (1 / 2 : ℝ) ≤
      1 - 1 / (4 * max 1 secondMomentBound) := by
    letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
    apply finite_smallBall_half_le_of_mean_one_second_moment_bound
      ((rule.generation depth).network.conditionalCellWeight p true)
      (normalizedDistance (rule.generation depth).network p)
      (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      ((rule.generation depth).network.sum_conditionalCellWeight p
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) true)
      (normalizedDistance_mean_one _ p (lt_of_lt_of_le zero_lt_one
        (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint])))) secondMomentPositive
    exact (secondMomentValid depth).trans (le_max_right _ _)
  have initialMeanPositive : 0 < conditionedDistanceMean rule.network p :=
    lt_of_lt_of_le zero_lt_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
      (by rwa [fixedPoint]) (by rwa [fixedPoint]))
  have cutoffPositive : 0 < min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)) := by positivity
  have cutoffSmall : min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)) <
      1 / conditionedDistanceMean rule.network p :=
    (min_le_right _ _).trans_lt (one_div_lt_one_div_of_lt initialMeanPositive (by linarith))
  have startNonnegative : 0 ≤ 1 - 1 / (4 * max 1 secondMomentBound) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * max 1 secondMomentBound)).mpr
    have := le_max_left 1 secondMomentBound
    nlinarith
  have startBelowOne : 1 - 1 / (4 * max 1 secondMomentBound) < 1 := sub_lt_self _ (by positivity)
  have longestGreaterOne := longestTerminalPath_greaterOne rule simple p positive lessOne fixedPoint scale
  have longestPositive := lt_trans zero_lt_one longestGreaterOne
  refine ⟨min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)),
    1 - 1 / (4 * max 1 secondMomentBound), cutoffPositive, startNonnegative, startBelowOne, ?_⟩
  have orbitBounds := iterate_bounds startNonnegative startBelowOne
    (thinningMap_zero rule.network p)
    (fun input nonnegative belowOne => thinningMap_nonnegative rule.network positive lessOne nonnegative belowOne.le)
    (fun input positiveInput belowOne => thinningMap_strict rule.network positive lessOne fixedPoint scale positiveInput belowOne)
  apply uniform_finite_depth_tail_le_iterate_on
    (thinningMap_monotoneOn rule.network positive lessOne)
    (fun level => ⟨(orbitBounds level).1, (orbitBounds level).2.trans startBelowOne.le⟩)
    (fun level => (orbitBounds level).1)
    (fun depth level => ⟨normalizedDistanceTail_nonnegative _ positive.le lessOne.le _,
      normalizedDistanceTail_atMostOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]) _⟩)
    (fun depth => by
      simpa only [pow_zero, div_one] using
        ((normalizedDistanceTail_monotone (rule.generation depth).network positive.le lessOne.le)
          (min_le_left (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)))).trans (initial depth))
    (fun depth level => by
      have scaledThreshold : (longestTerminalPath rule.network : ℝ) *
          (min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)) /
            (longestTerminalPath rule.network : ℝ) ^ (level + 1)) =
          min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)) /
            (longestTerminalPath rule.network : ℝ) ^ level := by
        rw [pow_succ]
        field_simp [longestPositive.ne']
      simpa only [scaledThreshold] using generation_normalizedDistanceTail_step rule simple p positive lessOne fixedPoint depth
        (threshold := min (1 / 2 : ℝ) (1 / (2 * conditionedDistanceMean rule.network p)) /
          (longestTerminalPath rule.network : ℝ) ^ (level + 1))
        (div_nonneg cutoffPositive.le (pow_nonneg longestPositive.le _)))
    (fun depth level shallow => generation_normalizedDistanceTail_shallow_zero rule simple p positive lessOne fixedPoint
      scale cutoffSmall depth level shallow)

theorem exists_uniform_generation_laplace_decay (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        Real.exp (-parameter * normalizedDistance (rule.generation depth).network p configuration)) ≤ target := by
  obtain ⟨cutoff, start, cutoffPositive, startNonnegative, startBelowOne, tailBound⟩ :=
    exists_uniform_generation_thinning_tail_bound rule simple p positive lessOne fixedPoint scale
  have summability := thinningMap_weighted_iterate_summable rule.network positive lessOne fixedPoint
    scale startNonnegative startBelowOne (growth := 1) zero_lt_one
  have convergence : Filter.Tendsto (fun level : ℕ => (thinningMap rule.network p)^[level] start)
      Filter.atTop (nhds 0) := by simpa only [one_pow, one_mul] using summability.tendsto_atTop_zero
  have errorPositive : 0 < min (target / 2) (1 / 2 : ℝ) := by positivity
  have errorBelowOne : min (target / 2) (1 / 2 : ℝ) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨level, small⟩ := (convergence.eventually (gt_mem_nhds errorPositive)).exists
  have longestPositive : 0 < (longestTerminalPath rule.network : ℝ) :=
    lt_trans zero_lt_one (longestTerminalPath_greaterOne rule simple p positive lessOne fixedPoint scale)
  have thresholdPositive : 0 < cutoff / (longestTerminalPath rule.network : ℝ) ^ level :=
    div_pos cutoffPositive (pow_pos longestPositive level)
  have parameterPositive : 0 < -Real.log (min (target / 2) (1 / 2 : ℝ)) /
      (cutoff / (longestTerminalPath rule.network : ℝ) ^ level) :=
    div_pos (neg_pos.mpr (Real.log_neg errorPositive errorBelowOne)) thresholdPositive
  refine ⟨-Real.log (min (target / 2) (1 / 2 : ℝ)) /
    (cutoff / (longestTerminalPath rule.network : ℝ) ^ level), parameterPositive, fun depth => ?_⟩
  letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
  have comparison := finite_laplace_le_smallBall
    ((rule.generation depth).network.conditionalCellWeight p true)
    (normalizedDistance (rule.generation depth).network p)
    (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    ((rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) true)
    (fun configuration => normalizedDistance_nonnegative _
      (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration)
    parameterPositive.le (cutoff / (longestTerminalPath rule.network : ℝ) ^ level)
  have exponentIdentity :
      -(-Real.log (min (target / 2) (1 / 2 : ℝ)) /
        (cutoff / (longestTerminalPath rule.network : ℝ) ^ level)) *
          (cutoff / (longestTerminalPath rule.network : ℝ) ^ level) =
            Real.log (min (target / 2) (1 / 2 : ℝ)) := by field_simp
  rw [exponentIdentity, Real.exp_log errorPositive] at comparison
  have probabilityBound := (tailBound depth level).trans small.le
  have halfBound := min_le_left (target / 2) (1 / 2 : ℝ)
  change normalizedDistanceTail (rule.generation depth).network p
    (cutoff / (longestTerminalPath rule.network : ℝ) ^ level) ≤ _ at probabilityBound
  dsimp [normalizedDistanceTail] at probabilityBound
  linarith

theorem exists_uniform_generation_inverse_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) (power : ℕ) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        (normalizedDistance (rule.generation depth).network p configuration)⁻¹ ^ power) ≤ bound := by
  obtain ⟨cutoff, start, cutoffPositive, startNonnegative, startBelowOne, tailBound⟩ :=
    exists_uniform_generation_thinning_tail_bound rule simple p positive lessOne fixedPoint scale
  refine ⟨cutoff⁻¹ ^ power * (1 + (longestTerminalPath rule.network : ℝ) ^ power *
    ∑' level : ℕ, ((longestTerminalPath rule.network : ℝ) ^ power) ^ level *
      (thinningMap rule.network p)^[level] start), fun depth => ?_⟩
  letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
  rw [← conditioned_completion_observable _ p (fun value => value⁻¹ ^ power)]
  apply finite_inverse_moment_le_of_thinning_tail_bound rule.network
    ((rule.generation depth).network.conditionalCellWeight p true)
    (completedNormalizedDistance (rule.generation depth).network p)
    (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    ((rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) true)
    (fun configuration => completedNormalizedDistance_positive _ positive.le lessOne.le
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) configuration) power
    positive lessOne fixedPoint scale startNonnegative startBelowOne
    (longestTerminalPath_greaterOne rule simple p positive lessOne fixedPoint scale) cutoffPositive
  intro level
  rw [conditioned_completion_observable _ p (fun value =>
    if value ≤ cutoff / (longestTerminalPath rule.network : ℝ) ^ level then 1 else 0)]
  exact tailBound depth level

theorem exists_uniform_generation_real_positive_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    {exponent : ℝ} (exponentNonnegative : 0 ≤ exponent) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        normalizedDistance (rule.generation depth).network p configuration ^ exponent) ≤ bound := by
  obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
  obtain ⟨bound, boundValid⟩ := exists_uniform_generation_positive_moment rule simple p positive lessOne fixedPoint scale power
  refine ⟨1 + bound, fun depth => ?_⟩
  letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
  have comparison := finite_rpow_le_one_add_power
    ((rule.generation depth).network.conditionalCellWeight p true)
    (normalizedDistance (rule.generation depth).network p)
    (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    ((rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) true)
    (fun configuration => normalizedDistance_nonnegative _
      (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration)
    exponentNonnegative exponentBound
  exact comparison.trans (by
    change 1 + normalizedDistanceMoment (rule.generation depth).network p power ≤ 1 + bound
    linarith [boundValid depth])

theorem exists_uniform_generation_real_inverse_moment (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target)
    {exponent : ℝ} (exponentNonnegative : 0 ≤ exponent) :
    ∃ bound : ℝ, ∀ depth,
      (∑ configuration, (rule.generation depth).network.conditionalCellWeight p true configuration *
        normalizedDistance (rule.generation depth).network p configuration ^ (-exponent)) ≤ bound := by
  obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
  obtain ⟨bound, boundValid⟩ := exists_uniform_generation_inverse_moment rule simple p positive lessOne fixedPoint scale power
  refine ⟨1 + bound, fun depth => ?_⟩
  letI : MeasurableSpace (Configuration (rule.generation depth).edges) := ⊤
  have comparison := finite_rpow_le_one_add_power
    ((rule.generation depth).network.conditionalCellWeight p true)
    (fun configuration => (normalizedDistance (rule.generation depth).network p configuration)⁻¹)
    (fun configuration => (rule.generation depth).network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
    ((rule.generation depth).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) true)
    (fun configuration => inv_nonneg.mpr (normalizedDistance_nonnegative _
      (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration))
    exponentNonnegative exponentBound
  simp only [Real.rpow_neg_eq_inv_rpow]
  exact comparison.trans (by linarith [boundValid depth])

end
end IGSIII.Chemical.SmallBall
