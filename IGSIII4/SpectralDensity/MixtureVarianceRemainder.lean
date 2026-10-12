import IGSIII4.SpectralDensity.MixtureMomentAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section

theorem mixture_normalized_variance_remainder
    (blocks constant polynomial probability longMean outputMean outputSecondMoment : ℝ)
    (blocksAboveOne : 1 ≤ blocks) (constantPositive : 0 < constant)
    (polynomialNonnegative : 0 ≤ polynomial)
    (probabilityNonnegative : 0 ≤ probability) (probabilityBelow : probability < 4 / 5)
    (longMeanLower : blocks / (8 * constant) ≤ longMean)
    (outputMeanLower : (1 - probability) * longMean ≤ outputMean)
    (outputSecondUpper : outputSecondMoment ≤ 20 * probability +
      (1 - probability) * (longMean ^ 2 + 16 + blocks * polynomial)) :
    (outputSecondMoment - outputMean ^ 2) / outputMean ^ 2 <
      4 + 1600 * constant ^ 2 * (polynomial + 36) / blocks := by
  have blocksPositive : 0 < blocks := by linarith
  have longMeanPositive : 0 < longMean :=
    (div_pos blocksPositive (by positivity)).trans_le longMeanLower
  have complementPositive : 0 < 1 - probability := by linarith
  have meanPositive : 0 < outputMean :=
    (mul_pos complementPositive longMeanPositive).trans_le outputMeanLower
  have longMeanScaled : blocks ≤ 8 * constant * longMean := by
    simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < 8 * constant)).mp longMeanLower
  have squareLower : blocks ^ 2 ≤ 64 * constant ^ 2 * longMean ^ 2 := by
    nlinarith [sq_nonneg (8 * constant * longMean - blocks)]
  have outputSquare : (1 - probability) ^ 2 * longMean ^ 2 ≤ outputMean ^ 2 := by
    have lowerNonnegative : 0 ≤ (1 - probability) * longMean := by positivity
    nlinarith [sq_nonneg (outputMean - (1 - probability) * longMean)]
  have complementSquare : (1 / 25 : ℝ) ≤ (1 - probability) ^ 2 := by
    nlinarith [sq_nonneg (1 - probability - 1 / 5)]
  have meanSquareLower : longMean ^ 2 / 25 ≤ outputMean ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right complementSquare (sq_nonneg longMean)]
  have blocksSquareLower : blocks ^ 2 ≤ 1600 * constant ^ 2 * outputMean ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left meanSquareLower
      (show 0 ≤ 1600 * constant ^ 2 by positivity)]
  have residualLower : blocks * polynomial + 36 ≤
      (1600 * constant ^ 2 * (polynomial + 36) / blocks) * outputMean ^ 2 := by
    apply (mul_le_mul_iff_right₀ blocksPositive).mp
    change blocks * (blocks * polynomial + 36) ≤
      blocks * ((1600 * constant ^ 2 * (polynomial + 36) / blocks) * outputMean ^ 2)
    have scale := mul_le_mul_of_nonneg_right blocksSquareLower
      (show 0 ≤ polynomial + 36 by positivity)
    have identity : blocks * ((1600 * constant ^ 2 * (polynomial + 36) / blocks) *
        outputMean ^ 2) = 1600 * constant ^ 2 * outputMean ^ 2 * (polynomial + 36) := by
      field_simp
    rw [identity]
    nlinarith [mul_nonneg blocksPositive.le (sub_nonneg.mpr blocksAboveOne)]
  have coefficientStrict : (1 - probability) < 5 * (1 - probability) ^ 2 := by
    nlinarith [mul_pos complementPositive
      (show 0 < 5 * (1 - probability) - 1 by linarith)]
  have leadingStrict : (1 - probability) * longMean ^ 2 < 5 * outputMean ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right coefficientStrict (sq_pos_of_pos longMeanPositive)]
  have varianceUpper : (1 - probability) * (16 + blocks * polynomial) ≤
      16 + blocks * polynomial := by
    exact mul_le_of_le_one_left (by positivity) (by linarith)
  have rawUpper : outputSecondMoment <
      (5 + 1600 * constant ^ 2 * (polynomial + 36) / blocks) * outputMean ^ 2 := by
    nlinarith
  apply (div_lt_iff₀ (sq_pos_of_pos meanPositive)).mpr
  nlinarith

end
end IGSIII4.SpectralDensity
