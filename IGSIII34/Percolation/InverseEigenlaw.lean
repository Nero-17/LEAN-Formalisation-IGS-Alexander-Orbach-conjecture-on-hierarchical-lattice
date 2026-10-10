import IGSIII34.Percolation.EigenlawTail
import IGSIII34.Probability.AEInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped NNReal ENNReal

theorem normalized_electrical_eigenlaw_inverse_moments (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1)
    (meanAboveOne : 1 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (eigenlaw : normalizedElectricalLaw rule parameter positive belowOne fixedPoint law = law)
    (almostPositive : ∀ᵐ value ∂(law : Measure ℝ≥0), 0 < value)
    (power : ℕ) :
    Integrable (fun value : ℝ≥0 => (value : ℝ)⁻¹ ^ power) (law : Measure ℝ≥0) := by
  let base := (rule.edges : ℝ) * electricalOutputMean rule parameter positive belowOne fixedPoint law
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classical.connected _)
  have edgesAtLeastOne : (1 : ℝ) ≤ rule.edges := by exact_mod_cast Nat.zero_lt_of_lt edge.isLt
  have meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law :=
    zero_lt_one.trans meanAboveOne
  have baseAboveOne : 1 < base := by
    dsimp [base]
    nlinarith
  have cutoffBelowOne := meanOneLaw_smallBall_below_one law meanOne (1 / 2) (by norm_num)
  have positiveReal : ∀ᵐ value : ℝ≥0 ∂(law : Measure ℝ≥0), 0 < (value : ℝ) := by
    filter_upwards [almostPositive] with value valuePositive
    exact_mod_cast valuePositive
  apply integrable_inv_pow_of_thinning_recursion_ae rule.network (law : Measure ℝ≥0) power
    NNReal.continuous_coe.measurable positiveReal positive belowOne fixedPoint classical.scale
    (measureReal_nonneg : 0 ≤ (law : Measure ℝ≥0).real {value | (value : ℝ) ≤ 1 / 2}) cutoffBelowOne
    baseAboveOne (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  intro depth
  have thresholdNonnegative : 0 ≤ (1 / 2 : ℝ) / base ^ (depth + 1) :=
    div_nonneg (by norm_num) (pow_pos (zero_lt_one.trans baseAboveOne) _).le
  have bound := normalized_electrical_eigenlaw_smallBall rule parameter positive belowOne fixedPoint law
    meanPositive eigenlaw ((1 / 2 : ℝ) / base ^ (depth + 1)) thresholdNonnegative
  have thresholdIdentity : base * ((1 / 2 : ℝ) / base ^ (depth + 1)) = (1 / 2 : ℝ) / base ^ depth := by
    rw [pow_succ]
    field_simp
  change (law : Measure ℝ≥0) {value | (value : ℝ) ≤ (1 / 2 : ℝ) / base ^ (depth + 1)} ≤
    ENNReal.ofReal (rule.network.reliability (parameter * ((law : Measure ℝ≥0)
      {value | (value : ℝ) ≤ base * ((1 / 2 : ℝ) / base ^ (depth + 1))}).toReal) / parameter) at bound
  rw [thresholdIdentity] at bound
  have mapNonnegative : 0 ≤ thinningMap rule.network parameter
      ((law : Measure ℝ≥0).real {value | (value : ℝ) ≤ (1 / 2 : ℝ) / base ^ depth}) :=
    thinningMap_nonnegative rule.network positive belowOne measureReal_nonneg measureReal_le_one
  have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
  change (law : Measure ℝ≥0).real {value | (value : ℝ) ≤ (1 / 2 : ℝ) / base ^ (depth + 1)} ≤
    (ENNReal.ofReal (thinningMap rule.network parameter
      ((law : Measure ℝ≥0).real {value | (value : ℝ) ≤ (1 / 2 : ℝ) / base ^ depth}))).toReal at realBound
  rwa [ENNReal.toReal_ofReal mapNonnegative] at realBound

end
end IGSIII34.Percolation
