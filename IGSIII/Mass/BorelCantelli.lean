import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace IGSIII.Mass

open MeasureTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

/-- Summability of squared L² norms gives convergence of the whole sequence
almost everywhere, by Chebyshev's inequality and the first Borel--Cantelli lemma.
No independence assumption and no subsequence extraction are used. -/
theorem ae_tendsto_zero_of_summable_L2
    (error : ℕ → Ω → ℝ)
    (measurable : ∀ n, AEStronglyMeasurable (error n) probability)
    (summable : (∑' n, (eLpNorm (error n) 2 probability) ^ 2) ≠ ∞) :
    ∀ᵐ sample ∂probability, Tendsto (fun n => error n sample) atTop (𝓝 0) := by
  have eventually_small (k : ℕ) : ∀ᵐ sample ∂probability,
      ∀ᶠ n in atTop, ‖error n sample‖ₑ < (2 : ℝ≥0∞)⁻¹ ^ k := by
    have threshold_ne_zero : (2 : ℝ≥0∞)⁻¹ ^ k ≠ 0 := by simp
    have estimate (n : ℕ) :
        probability {sample | (2 : ℝ≥0∞)⁻¹ ^ k ≤ ‖error n sample‖ₑ} ≤
          (((2 : ℝ≥0∞)⁻¹ ^ k)⁻¹) ^ 2 * (eLpNorm (error n) 2 probability) ^ 2 := by
      simpa using meas_ge_le_mul_pow_eLpNorm_enorm probability (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (measurable n) threshold_ne_zero (by simp)
    have finite_sum : (∑' n, probability
        {sample | (2 : ℝ≥0∞)⁻¹ ^ k ≤ ‖error n sample‖ₑ}) ≠ ∞ := by
      apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum estimate)
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top (by simp) summable
    simpa only [Set.mem_setOf_eq, not_le] using ae_eventually_notMem finite_sum
  filter_upwards [ae_all_iff.mpr eventually_small] with sample small
  apply EMetric.tendsto_atTop.mpr
  intro epsilon positive
  obtain ⟨k, bound⟩ := ENNReal.exists_inv_two_pow_lt positive.ne'
  obtain ⟨N, tail⟩ := eventually_atTop.mp (small k)
  exact ⟨N, fun n hn => by simpa only [edist_zero_right] using (tail n hn).trans bound⟩

/-- A geometric L² bound is summable and therefore controls every sufficiently
large generation almost surely. -/
theorem ae_tendsto_zero_of_geometric_L2
    (error : ℕ → Ω → ℝ)
    (measurable : ∀ n, AEStronglyMeasurable (error n) probability)
    (bound rate : ℝ) (bound_nonnegative : 0 ≤ bound)
    (rate_nonnegative : 0 ≤ rate) (rate_lt_one : rate < 1)
    (estimate : ∀ n, eLpNorm (error n) 2 probability ≤ ENNReal.ofReal (bound * rate ^ n)) :
    ∀ᵐ sample ∂probability, Tendsto (fun n => error n sample) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_summable_L2 error measurable
  have estimate_sq (n : ℕ) : (eLpNorm (error n) 2 probability) ^ 2 ≤
      ENNReal.ofReal bound ^ 2 * (ENNReal.ofReal rate ^ 2) ^ n := by
    calc
      _ ≤ ENNReal.ofReal (bound * rate ^ n) ^ 2 := pow_le_pow_left' (estimate n) 2
      _ = _ := by
        rw [ENNReal.ofReal_mul bound_nonnegative, ENNReal.ofReal_pow rate_nonnegative, mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum estimate_sq)
  rw [ENNReal.tsum_mul_left]
  apply ENNReal.mul_ne_top (by finiteness)
  apply (tsum_geometric_lt_top.mpr _).ne
  have rate_bound : ENNReal.ofReal rate < 1 := by
    exact ENNReal.ofReal_lt_one.mpr rate_lt_one
  exact pow_lt_one₀ bot_le rate_bound (by decide : (2 : ℕ) ≠ 0)

end IGSIII.Mass
