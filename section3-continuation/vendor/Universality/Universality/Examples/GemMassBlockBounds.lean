import Universality.Examples.GemMassBlock
import Universality.Examples.TieGemCriticalBounds
namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 800000

/-- Rational interval arithmetic for the genuine two-dimensional mass block. -/
theorem gemMassBlockFormula_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (5128845 : ℝ) / 1000000 ≤ gemMassBlockFormula p 0 0 ∧
    gemMassBlockFormula p 0 0 ≤ (5128853 : ℝ) / 1000000 ∧
    (1262253 : ℝ) / 1000000 ≤ gemMassBlockFormula p 0 1 ∧
    gemMassBlockFormula p 0 1 ≤ (1262255 : ℝ) / 1000000 ∧
    (1703741 : ℝ) / 1000000 ≤ gemMassBlockFormula p 1 0 ∧
    gemMassBlockFormula p 1 0 ≤ (1703744 : ℝ) / 1000000 ∧
    gemMassBlockFormula p 1 1 = 2 := by
  obtain ⟨hlower, hupper⟩ := gem_critical_point_rational_bounds p hp hp' hfixed
  have hl2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8191725 / 10000000) hlower.le 2
  have hu2 := pow_le_pow_left₀ hp.le hupper.le 2
  have hl4 := pow_le_pow_left₀ (sq_nonneg ((8191725 : ℝ) / 10000000)) hl2 2
  have hu4 := pow_le_pow_left₀ (sq_nonneg p) hu2 2
  norm_num at hl2 hu2 hl4 hu4
  have hden : 0 < 1 + p ^ 2 - (p ^ 2) ^ 2 := by nlinarith
  have hplus : 0 < 1 + p := by linarith
  have hplus2 : 0 < 1 + p ^ 2 := by positivity
  have hcc0 : (2280227 : ℝ) / 1000000 ≤
      (1 + 4 * p ^ 2 - 2 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hcc1 : (1 + 4 * p ^ 2 - 2 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2) ≤
      (2280230 : ℝ) / 1000000 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hoff0 : (1262253 : ℝ) / 1000000 ≤
      (2 + 2 * p ^ 2 - 4 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hoff1 : (2 + 2 * p ^ 2 - 4 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2) ≤
      (1262255 : ℝ) / 1000000 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have ht0 : (4502994 : ℝ) / 10000000 ≤ p / (1 + p) := by
    apply (le_div_iff₀ hplus).mpr
    linarith
  have ht1 : p / (1 + p) ≤ (4502996 : ℝ) / 10000000 := by
    apply (div_le_iff₀ hplus).mpr
    linarith
  have hs0 : (4015714 : ℝ) / 10000000 ≤ p ^ 2 / (1 + p ^ 2) := by
    apply (le_div_iff₀ hplus2).mpr
    nlinarith
  have hs1 : p ^ 2 / (1 + p ^ 2) ≤ (4015718 : ℝ) / 10000000 := by
    apply (div_le_iff₀ hplus2).mpr
    nlinarith
  have hoffnonneg : 0 ≤ (2 + 2 * p ^ 2 - 4 * (p ^ 2) ^ 2) /
      (1 + p ^ 2 - (p ^ 2) ^ 2) := by linarith
  have hproduct0 := mul_le_mul hoff0 ht0 (by norm_num : (0 : ℝ) ≤ 4502994 / 10000000) hoffnonneg
  have hproduct1 := mul_le_mul hoff1 ht1 (div_nonneg hp.le hplus.le)
    (by norm_num : (0 : ℝ) ≤ 1262255 / 1000000)
  simp only [gemMassBlockFormula, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_div_assoc]
  refine ⟨?_, ?_, hoff0, hoff1, ?_, ?_, trivial⟩ <;>
    linarith only [hcc0, hcc1, hproduct0, hproduct1, hs0, hs1, ht0, ht1]

end
end Universality

