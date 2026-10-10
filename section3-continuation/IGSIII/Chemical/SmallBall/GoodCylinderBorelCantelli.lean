import IGSIII.Chemical.SmallBall.ActualConnectedCylinderChernoff
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

theorem exp_neg_le_inverse_of_pos {value : ℝ} (positive : 0 < value) : Real.exp (-value) ≤ value⁻¹ := by
  rw [Real.exp_neg]
  apply (inv_le_inv₀ (Real.exp_pos _) positive).mpr
  exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp value)

theorem ae_good_count_grows_of_positive_population
    {Sample : Type*} [MeasurableSpace Sample] (μ : Measure Sample) [IsProbabilityMeasure μ]
    (population successes : ℕ → Sample → ℝ) (growth probability : ℝ)
    (growthLarge : 1 < growth) (probabilityPositive : 0 < probability)
    (populationLimit : ∀ᵐ sample ∂μ, ∃ limit : ℝ, 0 < limit ∧
      Tendsto (fun depth => population depth sample / growth ^ depth) atTop (𝓝 limit))
    (chernoff : ∀ depth : ℕ, ∀ threshold : ℝ,
      μ.real {sample | threshold ≤ population depth sample ∧ successes depth sample < probability / 2 * population depth sample} ≤
        Real.exp (-probability * ((1 / 2 : ℝ) - Real.exp (-1)) * threshold)) :
    ∀ᵐ sample ∂μ, ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ᶠ depth : ℕ in atTop,
      coefficient * growth ^ depth ≤ successes depth sample := by
  have growthPositive : 0 < growth := zero_lt_one.trans growthLarge
  have ratePositive : 0 < probability * ((1 / 2 : ℝ) - Real.exp (-1)) :=
    mul_pos probabilityPositive bernoulli_lower_tail_exponent_positive
  have ratioNonnegative : 0 ≤ growth⁻¹ := inv_nonneg.mpr growthPositive.le
  have ratioBelow : growth⁻¹ < 1 := inv_lt_one_of_one_lt₀ growthLarge
  have exceptions (index : ℕ) : ∀ᵐ sample ∂μ, ∀ᶠ depth : ℕ in atTop,
      ¬ (growth ^ depth / ((index : ℝ) + 1) ≤ population depth sample ∧
        successes depth sample < probability / 2 * population depth sample) := by
    have bounds (depth : ℕ) : μ.real {sample |
        growth ^ depth / ((index : ℝ) + 1) ≤ population depth sample ∧
        successes depth sample < probability / 2 * population depth sample} ≤
        (((index : ℝ) + 1) / (probability * ((1 / 2 : ℝ) - Real.exp (-1)))) * (growth⁻¹) ^ depth := by
      refine (chernoff depth _).trans ?_
      have positive : 0 < probability * ((1 / 2 : ℝ) - Real.exp (-1)) * (growth ^ depth / ((index : ℝ) + 1)) :=
        mul_pos ratePositive (div_pos (pow_pos growthPositive _) (by positivity))
      calc
        _ = Real.exp (-(probability * ((1 / 2 : ℝ) - Real.exp (-1)) *
            (growth ^ depth / ((index : ℝ) + 1)))) := by congr 1; ring
        _ ≤ (probability * ((1 / 2 : ℝ) - Real.exp (-1)) * (growth ^ depth / ((index : ℝ) + 1)))⁻¹ :=
          exp_neg_le_inverse_of_pos positive
        _ = _ := by rw [mul_inv_rev, inv_div, inv_pow]; ring
    have summable := (summable_geometric_of_lt_one ratioNonnegative ratioBelow).mul_left
      (((index : ℝ) + 1) / (probability * ((1 / 2 : ℝ) - Real.exp (-1))))
    have finiteEvents : (∑' depth : ℕ, μ {sample |
        growth ^ depth / ((index : ℝ) + 1) ≤ population depth sample ∧
        successes depth sample < probability / 2 * population depth sample}) ≠ ∞ := by
      apply ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
      apply ENNReal.tsum_le_tsum
      intro depth
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (bounds depth)
    exact ae_eventually_notMem finiteEvents
  filter_upwards [ae_all_iff.mpr exceptions, populationLimit] with sample outside populationConvergence
  obtain ⟨limit, limitPositive, convergence⟩ := populationConvergence
  obtain ⟨index, small⟩ := exists_nat_one_div_lt (half_pos limitPositive)
  refine ⟨probability / 2 / ((index : ℝ) + 1), by positivity, ?_⟩
  have populationLower : ∀ᶠ depth : ℕ in atTop,
      growth ^ depth / ((index : ℝ) + 1) ≤ population depth sample := by
    filter_upwards [convergence.eventually (lt_mem_nhds (half_lt_self limitPositive))] with depth lower
    have comparison : 1 / ((index : ℝ) + 1) ≤ population depth sample / growth ^ depth := small.le.trans lower.le
    have multiplied := (le_div_iff₀ (pow_pos growthPositive depth)).mp comparison
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using multiplied
  filter_upwards [outside index, populationLower] with depth notBad lower
  have successLower : probability / 2 * population depth sample ≤ successes depth sample :=
    le_of_not_gt (fun bad => notBad ⟨lower, bad⟩)
  refine (le_trans ?_ successLower)
  have multiplied := mul_le_mul_of_nonneg_left lower (half_pos probabilityPositive).le
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using multiplied

end
end IGSIII.Chemical.SmallBall