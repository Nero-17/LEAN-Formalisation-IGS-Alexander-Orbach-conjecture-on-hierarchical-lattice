import IGSIII4.SpectralDensity.StrictCellMoments

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability
open Filter Topology

theorem actual_normalized_variance_lt_eight {vertices edges : ℕ}
    (finiteNetwork : Universality.FiniteNetwork vertices edges) (probability : ℝ)
    (normalized : ∑ configuration, finiteNetwork.conditionalCellWeight probability true configuration = 1)
    (meanPositive : 0 < conditionalMeanResistance finiteNetwork probability)
    (secondBound : finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance finiteNetwork configuration ^ 2) <
        9 * conditionalMeanResistance finiteNetwork probability ^ 2) :
    finiteVariance (finiteNetwork.conditionalCellWeight probability true)
      (positiveNormalizedResistance finiteNetwork probability) < 8 := by
  rw [finiteVariance_eq_second_moment _ _ normalized,
    positiveNormalizedResistance_mean_one _ _ meanPositive,
    actual_normalized_second_moment]
  have bound : finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance finiteNetwork configuration ^ 2) /
        conditionalMeanResistance finiteNetwork probability ^ 2 < 9 :=
    (div_lt_iff₀ (sq_pos_of_pos meanPositive)).mpr secondBound
  norm_num only [one_pow] at *
  linarith

/-- Strict cell bounds propagate through the actual finite graph generations.
The third conclusion is the strict lower factor for every consecutive pair of means. -/
theorem actual_generation_strict_bounds_of_uniform_cell_moments
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (cellBounds : ∀ {Outcome : Type} [Fintype Outcome] [Nonempty Outcome]
      (weight response : Outcome → ℝ),
      (∀ outcome, 0 ≤ weight outcome) → (∑ outcome, weight outcome = 1) →
      (∀ outcome, 0 < response outcome) → finiteMean weight response = 1 →
      finiteVariance weight response ≤ 8 →
      lower < weightedCellMean blocks paths interior probability weight response ∧
      weightedCellSecondMoment blocks paths interior probability weight response <
        9 * weightedCellMean blocks paths interior probability weight response ^ 2) :
    ∀ depth : ℕ,
      finiteVariance (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
        (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability) < 8 ∧
      lower ^ (depth + 1) < conditionalMeanResistance
        ((rule blocks paths interior).generation depth).network probability ∧
      lower * conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability <
        conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability := by
  have normalized (depth : ℕ) :
      ∑ configuration, ((rule blocks paths interior).generation depth).network.conditionalCellWeight
        probability true configuration = 1 :=
    ((rule blocks paths interior).generation depth).network.sum_conditionalCellWeight probability
      (by rwa [(rule blocks paths interior).generation_fixed_point probability critical])
      (by rwa [(rule blocks paths interior).generation_fixed_point probability critical]) true
  have meanPositive (depth : ℕ) := generation_conditionalMeanResistance_positive
    (rule blocks paths interior) (classical blocks paths interior pathsPositive)
    probability positive belowOne critical depth
  have moments : ∀ depth : ℕ,
      finiteVariance (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
        (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability) < 8 ∧
      lower ^ (depth + 1) < conditionalMeanResistance
        ((rule blocks paths interior).generation depth).network probability := by
    intro depth
    induction depth with
    | zero =>
      have bounds := cellBounds (fun _ : Unit => (1 : ℝ)) (fun _ => (1 : ℝ))
        (by simp) (by simp) (by simp)
        (by simp [finiteMean]) (by simp [finiteVariance, finiteMean])
      rw [actual_unit_cell_mean, actual_unit_cell_second_moment] at bounds
      refine ⟨actual_normalized_variance_lt_eight _ probability (normalized 0) (meanPositive 0) bounds.2, ?_⟩
      simpa only [Nat.zero_add, pow_one, Rule.generation] using bounds.1
    | succ depth previous =>
      have bounds := cellBounds
        (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
        (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability)
        (((rule blocks paths interior).generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
        (normalized depth)
        (positiveNormalizedResistance_positive _ _ (meanPositive depth))
        (positiveNormalizedResistance_mean_one _ _ (meanPositive depth)) previous.1.le
      rw [actual_generation_weighted_cell_mean blocks paths interior pathsPositive probability positive belowOne critical depth,
        actual_generation_weighted_cell_second_moment blocks paths interior pathsPositive probability positive belowOne critical depth] at bounds
      have nextMeanLower := (lt_div_iff₀ (meanPositive depth)).mp bounds.1
      have secondBound : finiteMean
          (((rule blocks paths interior).generation (depth + 1)).network.conditionalCellWeight probability true)
          (fun configuration => unitConfigurationResistance
            ((rule blocks paths interior).generation (depth + 1)).network configuration ^ 2) <
          9 * conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 := by
        have scaled := bounds.2
        rw [div_pow] at scaled
        have multiplied := (div_lt_iff₀ (sq_pos_of_pos (meanPositive depth))).mp scaled
        have cancellation :
            (9 * (conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 /
              conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability ^ 2)) *
                conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability ^ 2 =
            9 * conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 := by
          field_simp [(meanPositive depth).ne']
        exact multiplied.trans_eq cancellation
      refine ⟨actual_normalized_variance_lt_eight _ probability (normalized (depth + 1)) (meanPositive (depth + 1)) secondBound, ?_⟩
      calc
        lower ^ (depth + 1 + 1) = lower * lower ^ (depth + 1) := by rw [pow_succ']
        _ ≤ lower * conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability :=
          mul_le_mul_of_nonneg_left previous.2.le lowerPositive.le
        _ < _ := nextMeanLower
  intro depth
  refine ⟨(moments depth).1, (moments depth).2, ?_⟩
  have bounds := cellBounds
    (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
    (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability)
    (((rule blocks paths interior).generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    (normalized depth)
    (positiveNormalizedResistance_positive _ _ (meanPositive depth))
    (positiveNormalizedResistance_mean_one _ _ (meanPositive depth)) (moments depth).1.le
  rw [actual_generation_weighted_cell_mean blocks paths interior pathsPositive probability
    positive belowOne critical depth] at bounds
  exact (lt_div_iff₀ (meanPositive depth)).mp bounds.1

/-- One cutoff depending only on the base gives variance strictly below eight
and the strict mean-growth factor at every recursive depth of the actual rule. -/
theorem generation_strict_moment_bounds_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      ∀ depth : ℕ,
        finiteVariance
          (((rule (blockCount base length) (pathCount length) (length - 2)).generation depth).network.conditionalCellWeight
            (appendixCriticalProbability base length) true)
          (positiveNormalizedResistance
            ((rule (blockCount base length) (pathCount length) (length - 2)).generation depth).network
            (appendixCriticalProbability base length)) < 8 ∧
        ((blockCount base length : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2))) ^ (depth + 1) <
          conditionalMeanResistance
            ((rule (blockCount base length) (pathCount length) (length - 2)).generation depth).network
            (appendixCriticalProbability base length) ∧
        (blockCount base length : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2)) *
          conditionalMeanResistance
            ((rule (blockCount base length) (pathCount length) (length - 2)).generation depth).network
            (appendixCriticalProbability base length) <
          conditionalMeanResistance
            ((rule (blockCount base length) (pathCount length) (length - 2)).generation (depth + 1)).network
            (appendixCriticalProbability base length) := by
  filter_upwards [finite_cell_strict_moment_bounds_eventually base baseAboveOne,
    eventually_ge_atTop (4 : ℕ)] with length cellBounds lengthLarge
  have lengthAtLeastTwo : 2 ≤ length := by omega
  obtain ⟨probabilityPositive, probabilityBelowOne, fixedPoint⟩ :=
    appendixCriticalProbability_spec base length lengthAtLeastTwo
  have pathsPositive : 0 < pathCount length := by
    apply Nat.ceil_pos.mpr
    have lengthRealPositive : 0 < (length : ℝ) := by positivity
    exact mul_pos lengthRealPositive (by positivity)
  have lowerPositive : 0 < (blockCount base length : ℝ) / (40 * ((⌈base⌉₊ : ℝ) + 2)) := by
    have blocksPositive : 0 < blockCount base length := Nat.ceil_pos.mpr (by positivity : 0 < base ^ length)
    positivity
  exact actual_generation_strict_bounds_of_uniform_cell_moments (blockCount base length)
    (pathCount length) (length - 2) pathsPositive (appendixCriticalProbability base length)
    probabilityPositive probabilityBelowOne fixedPoint _ lowerPositive cellBounds

end
end IGSIII4.SpectralDensity.ActualFamily
