import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Universality

theorem window_ratio_bounds (numerator denominator massScale volumeScale lower upper volume : ℝ)
    (hmass : 0 < massScale) (hvolumeScale : 0 < volumeScale)
    (hlower : 0 < lower) (hupper : 0 < upper) (hvolume : 0 < volume)
    (hnumeratorLower : lower * massScale ≤ numerator)
    (hnumeratorUpper : numerator ≤ upper * massScale)
    (hdenominatorLower : volumeScale ≤ denominator)
    (hdenominatorUpper : denominator ≤ volume ^ 2 * volumeScale) :
    lower / volume ^ 2 * (massScale / volumeScale) ≤ numerator / denominator ∧
      numerator / denominator ≤ upper * (massScale / volumeScale) := by
  have hdenominator : 0 < denominator := hvolumeScale.trans_le hdenominatorLower
  have hnumerator : 0 ≤ numerator := (mul_pos hlower hmass).le.trans hnumeratorLower
  constructor
  · calc
      _ = lower * massScale / (volume ^ 2 * volumeScale) := by ring
      _ ≤ numerator / (volume ^ 2 * volumeScale) :=
        div_le_div_of_nonneg_right hnumeratorLower (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hnumerator hdenominator hdenominatorUpper
  · calc
      _ ≤ upper * massScale / denominator :=
        div_le_div_of_nonneg_right hnumeratorUpper hdenominator.le
      _ ≤ upper * massScale / volumeScale :=
        div_le_div_of_nonneg_left (by positivity) hvolumeScale hdenominatorLower
      _ = _ := by ring

end Universality
