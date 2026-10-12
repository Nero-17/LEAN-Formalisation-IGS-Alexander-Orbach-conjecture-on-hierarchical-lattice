import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Scalar combination of the independently established short/long finite
moment bounds. The actual product-law and graph identities are separate inputs. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section

theorem mixture_mean_and_second_moment_bound
    (blocks constant polynomial probability longMean outputMean outputSecondMoment : ℝ)
    (blocksAboveOne : 1 ≤ blocks) (constantPositive : 0 < constant)
    (polynomialNonnegative : 0 ≤ polynomial)
    (probabilityNonnegative : 0 ≤ probability) (probabilityBelow : probability < 4 / 5)
    (longMeanLower : blocks / (8 * constant) ≤ longMean)
    (outputMeanLower : (1 - probability) * longMean ≤ outputMean)
    (outputSecondUpper : outputSecondMoment ≤ 20 * probability +
      (1 - probability) * (longMean ^ 2 + 16 + blocks * polynomial))
    (cutoff : 1600 * constant ^ 2 * (polynomial + 36) / blocks < 4) :
    blocks / (40 * constant) < outputMean ∧ outputSecondMoment < 9 * outputMean ^ 2 := by
  have blocksPositive : 0 < blocks := by linarith
  have longMeanPositive : 0 < longMean := (div_pos blocksPositive (by positivity)).trans_le longMeanLower
  have longMeanScaled : blocks ≤ 8 * constant * longMean :=
    by simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 8 * constant)).mp longMeanLower
  have probabilityComplementPositive : 0 < 1 - probability := by linarith
  have meanStrict : longMean / 5 < outputMean := by
    nlinarith [mul_pos (show 0 < 1 - probability - 1 / 5 by linarith) longMeanPositive]
  have outputMeanPositive : 0 < outputMean := (by positivity : 0 < longMean / 5).trans meanStrict
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < 40 * constant)).mpr
    nlinarith [mul_lt_mul_of_pos_left meanStrict (by positivity : 0 < 40 * constant)]
  · have cutoffScaled : 400 * constant ^ 2 * (polynomial + 36) < blocks := by
      have scaled := (div_lt_iff₀ blocksPositive).mp cutoff
      nlinarith
    have multipliedCutoff := mul_lt_mul_of_pos_right cutoffScaled blocksPositive
    have constantSquarePositive : 0 < constant ^ 2 := sq_pos_of_pos constantPositive
    have polynomialScaled :
        400 * constant ^ 2 * (blocks * polynomial + 36) < blocks ^ 2 := by
      have nonnegative := mul_nonneg constantSquarePositive.le (sub_nonneg.mpr blocksAboveOne)
      nlinarith [multipliedCutoff]
    have squareLower : blocks ^ 2 ≤ 64 * constant ^ 2 * longMean ^ 2 := by
      nlinarith [sq_nonneg (8 * constant * longMean - blocks)]
    have quadraticGap : blocks * polynomial + 36 < (4 / 25 : ℝ) * longMean ^ 2 := by
      apply (mul_lt_mul_iff_right₀ constantSquarePositive).mp
      nlinarith [polynomialScaled, squareLower]
    have coefficientGap : (4 / 25 : ℝ) ≤ 9 * (1 - probability) ^ 2 - (1 - probability) := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - probability - 1 / 5 by linarith)
        (show 0 ≤ 9 * (1 - probability) + 4 / 5 by linarith)]
    have coefficientScaled := mul_le_mul_of_nonneg_right coefficientGap (sq_nonneg longMean)
    have complementAtMostOne : 1 - probability ≤ 1 := by linarith
    have varianceScaled := mul_le_mul_of_nonneg_right complementAtMostOne
      (show 0 ≤ 16 + blocks * polynomial by positivity)
    have outputScaled : (1 - probability) ^ 2 * longMean ^ 2 ≤ outputMean ^ 2 := by
      have lowerNonnegative : 0 ≤ (1 - probability) * longMean := by positivity
      nlinarith [sq_nonneg (outputMean - (1 - probability) * longMean)]
    nlinarith [outputSecondUpper, quadraticGap, coefficientScaled, varianceScaled, outputScaled]

end
end IGSIII4.SpectralDensity
