import IGSIII4.SpectralDensity.ActualGenerationMoments20261012
import IGSIII4.SpectralDensity.NaturalGrowthTransfer20261012
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability
open scoped BigOperators

/-- This property is an explicit premise of the iteration adapter below.
It must be discharged by the actual cell-law estimates. -/
def FiniteCellMomentBounds (blocks paths interior : ℕ) (probability lower : ℝ) : Prop :=
  ∀ {Outcome : Type} [Fintype Outcome] [Nonempty Outcome]
    (weight response : Outcome → ℝ),
    (∀ outcome, 0 ≤ weight outcome) → (∑ outcome, weight outcome = 1) →
    (∀ outcome, 0 < response outcome) → finiteMean weight response = 1 →
    finiteVariance weight response ≤ 8 →
    lower ≤ weightedCellMean blocks paths interior probability weight response ∧
    weightedCellSecondMoment blocks paths interior probability weight response ≤
      9 * weightedCellMean blocks paths interior probability weight response ^ 2

theorem actual_unit_cell_observable (blocks paths interior : ℕ) (probability : ℝ)
    (observable : ℝ → ℝ) :
    weightedCellObservable blocks paths interior probability (fun _ : Unit => (1 : ℝ))
      (fun _ => (1 : ℝ)) observable =
    finiteMean ((network blocks paths interior).conditionalCellWeight probability true)
      (fun configuration => observable (unitConfigurationResistance
        (network blocks paths interior) configuration)) := by
  unfold weightedCellObservable
  apply congrArg (finiteMean _)
  funext configuration
  change finiteMean (productWeight (fun _ : Unit => (1 : ℝ)))
    (fun _ => observable (unitConfigurationResistance (network blocks paths interior) configuration)) = _
  exact finiteMean_const _ (sum_productWeight _ (by simp)) _

theorem actual_unit_cell_mean (blocks paths interior : ℕ) (probability : ℝ) :
    weightedCellMean blocks paths interior probability (fun _ : Unit => (1 : ℝ))
      (fun _ => (1 : ℝ)) = conditionalMeanResistance (network blocks paths interior) probability := by
  unfold weightedCellMean
  rw [actual_unit_cell_observable]
  exact finiteMean_conditional_unitResistance _ _

theorem actual_unit_cell_second_moment (blocks paths interior : ℕ) (probability : ℝ) :
    weightedCellSecondMoment blocks paths interior probability (fun _ : Unit => (1 : ℝ))
      (fun _ => (1 : ℝ)) =
    finiteMean ((network blocks paths interior).conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance (network blocks paths interior) configuration ^ 2) := by
  unfold weightedCellSecondMoment
  exact actual_unit_cell_observable _ _ _ _ (fun value => value ^ 2)

theorem actual_normalized_second_moment {vertices edges : ℕ}
    (finiteNetwork : Universality.FiniteNetwork vertices edges) (probability : ℝ) :
    finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => positiveNormalizedResistance finiteNetwork probability configuration ^ 2) =
    finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance finiteNetwork configuration ^ 2) /
        conditionalMeanResistance finiteNetwork probability ^ 2 := by
  rw [positiveNormalizedResistance_observable finiteNetwork probability (fun value => value ^ 2)]
  simp only [normalizedConfigurationResistance, div_eq_mul_inv, mul_pow, inv_pow]
  rw [finiteMean_mul_const]

theorem actual_normalized_variance_le_eight {vertices edges : ℕ}
    (finiteNetwork : Universality.FiniteNetwork vertices edges) (probability : ℝ)
    (normalized : ∑ configuration, finiteNetwork.conditionalCellWeight probability true configuration = 1)
    (meanPositive : 0 < conditionalMeanResistance finiteNetwork probability)
    (secondBound : finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance finiteNetwork configuration ^ 2) ≤
        9 * conditionalMeanResistance finiteNetwork probability ^ 2) :
    finiteVariance (finiteNetwork.conditionalCellWeight probability true)
      (positiveNormalizedResistance finiteNetwork probability) ≤ 8 := by
  rw [finiteVariance_eq_second_moment _ _ normalized,
    positiveNormalizedResistance_mean_one _ _ meanPositive,
    actual_normalized_second_moment]
  have bound : finiteMean (finiteNetwork.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance finiteNetwork configuration ^ 2) /
        conditionalMeanResistance finiteNetwork probability ^ 2 ≤ 9 :=
    (div_le_iff₀ (sq_pos_of_pos meanPositive)).mpr secondBound
  norm_num only [one_pow] at *
  linarith

theorem actual_generation_bounds_of_uniform_cell_moments
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (cellBounds : FiniteCellMomentBounds blocks paths interior probability lower) :
    ∀ depth : ℕ,
      finiteVariance (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
        (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability) ≤ 8 ∧
      lower ^ (depth + 1) ≤ conditionalMeanResistance
        ((rule blocks paths interior).generation depth).network probability := by
  have normalized (depth : ℕ) :
      ∑ configuration, ((rule blocks paths interior).generation depth).network.conditionalCellWeight
        probability true configuration = 1 :=
    ((rule blocks paths interior).generation depth).network.sum_conditionalCellWeight probability
      (by rwa [(rule blocks paths interior).generation_fixed_point probability critical])
      (by rwa [(rule blocks paths interior).generation_fixed_point probability critical]) true
  have meanPositive (depth : ℕ) := generation_conditionalMeanResistance_positive
    (rule blocks paths interior) (classical blocks paths interior pathsPositive)
    probability positive belowOne critical depth
  intro depth
  induction depth with
  | zero =>
    have bounds := cellBounds (fun _ : Unit => (1 : ℝ)) (fun _ => (1 : ℝ))
      (by simp) (by simp) (by simp)
      (by simp [finiteMean]) (by simp [finiteVariance, finiteMean])
    rw [actual_unit_cell_mean, actual_unit_cell_second_moment] at bounds
    refine ⟨actual_normalized_variance_le_eight _ probability (normalized 0) (meanPositive 0) bounds.2, ?_⟩
    simpa only [Nat.zero_add, pow_one, Rule.generation] using bounds.1
  | succ depth previous =>
    have bounds := cellBounds
      (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
      (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability)
      (((rule blocks paths interior).generation depth).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
      (normalized depth)
      (positiveNormalizedResistance_positive _ _ (meanPositive depth))
      (positiveNormalizedResistance_mean_one _ _ (meanPositive depth)) previous.1
    rw [actual_generation_weighted_cell_mean blocks paths interior pathsPositive probability positive belowOne critical depth,
      actual_generation_weighted_cell_second_moment blocks paths interior pathsPositive probability positive belowOne critical depth] at bounds
    have nextMeanLower := (le_div_iff₀ (meanPositive depth)).mp bounds.1
    have secondBound : finiteMean
        (((rule blocks paths interior).generation (depth + 1)).network.conditionalCellWeight probability true)
        (fun configuration => unitConfigurationResistance
          ((rule blocks paths interior).generation (depth + 1)).network configuration ^ 2) ≤
        9 * conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 := by
      have scaled := bounds.2
      rw [div_pow] at scaled
      have multiplied := (div_le_iff₀ (sq_pos_of_pos (meanPositive depth))).mp scaled
      have cancellation :
          (9 * (conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 /
            conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability ^ 2)) *
              conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability ^ 2 =
          9 * conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability ^ 2 := by
        field_simp [(meanPositive depth).ne']
      exact multiplied.trans_eq cancellation
    refine ⟨actual_normalized_variance_le_eight _ probability (normalized (depth + 1)) (meanPositive (depth + 1)) secondBound, ?_⟩
    calc
      lower ^ (depth + 1 + 1) = lower * lower ^ (depth + 1) := by rw [pow_succ']
      _ ≤ lower * conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability :=
        mul_le_mul_of_nonneg_left previous.2 lowerPositive.le
      _ ≤ _ := nextMeanLower

theorem actual_finite_scale_lower_of_uniform_cell_moments
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (cellBounds : FiniteCellMomentBounds blocks paths interior probability lower) (depth : ℕ) :
    lower ^ depth ≤ (electricalOrbitScale (rule blocks paths interior) probability positive belowOne critical depth : ℝ) := by
  cases depth with
  | zero => simp [electricalOrbitScale]
  | succ depth =>
    rw [electricalOrbitScale_succ_eq_generation_mean (rule blocks paths interior)
      (classical blocks paths interior pathsPositive) probability positive belowOne critical]
    exact (actual_generation_bounds_of_uniform_cell_moments blocks paths interior pathsPositive probability
      positive belowOne critical lower lowerPositive cellBounds depth).2

theorem actual_natural_growth_lower_of_uniform_cell_moments
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (natural : NaturalResistanceCompletion20261011 (rule blocks paths interior) probability positive belowOne critical)
    (lower : ℝ) (lowerPositive : 0 < lower)
    (cellBounds : FiniteCellMomentBounds blocks paths interior probability lower) :
    lower ≤ natural.growth :=
  actual_natural_growth_lower_of_finite_scale_bounds (rule blocks paths interior)
    (classical blocks paths interior pathsPositive) probability positive belowOne critical natural lower lowerPositive
    (actual_finite_scale_lower_of_uniform_cell_moments blocks paths interior pathsPositive probability
      positive belowOne critical lower lowerPositive cellBounds)

end
end IGSIII4.SpectralDensity.ActualFamily
