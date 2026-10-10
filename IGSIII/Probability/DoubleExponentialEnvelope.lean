import IGSIII.Probability.ExceptionalEnvelope
import IGSIII.Probability.WeightedDoubleExponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Set
open scoped ENNReal

theorem indicator_norms_summable_of_double_exponential
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (order : ℝ≥0∞) (orderPositive : order ≠ 0) (orderFinite : order ≠ ∞)
    (exceptions : ℕ → Set Sample) (measurable : ∀ depth, MeasurableSet (exceptions depth))
    (weightCoefficient growth coefficient ratio : ℝ) (weightCoefficientNonnegative : 0 ≤ weightCoefficient)
    (growthNonnegative : 0 ≤ growth)
    (coefficientNonnegative : 0 ≤ coefficient) (ratioNonnegative : 0 ≤ ratio) (ratioBelowOne : ratio < 1)
    (base : ℕ) (baseAtLeastTwo : 2 ≤ base)
    (probabilityBound : ∀ depth, measure (exceptions depth) ≤
      ENNReal.ofReal (coefficient * ratio ^ (base ^ depth))) :
    (∑' depth, eLpNorm ((exceptions depth).indicator (fun _ => weightCoefficient * growth ^ depth)) order measure) ≠ ∞ := by
  have reciprocalPositive : 0 < 1 / order.toReal :=
    one_div_pos.mpr (ENNReal.toReal_pos orderPositive orderFinite)
  have rootNonnegative := Real.rpow_nonneg ratioNonnegative (1 / order.toReal)
  have rootBelowOne := Real.rpow_lt_one ratioNonnegative ratioBelowOne reciprocalPositive
  have summable := (weighted_double_exponential_summable growth growthNonnegative
    baseAtLeastTwo rootNonnegative rootBelowOne).mul_left (weightCoefficient * coefficient ^ (1 / order.toReal))
  apply ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro depth
  rw [eLpNorm_indicator_const (measurable depth) orderPositive orderFinite,
    Real.enorm_of_nonneg (mul_nonneg weightCoefficientNonnegative (pow_nonneg growthNonnegative depth))]
  calc
    _ ≤ ENNReal.ofReal (weightCoefficient * growth ^ depth) *
        ENNReal.ofReal (coefficient * ratio ^ (base ^ depth)) ^ (1 / order.toReal) :=
      mul_le_mul_right (ENNReal.rpow_le_rpow (probabilityBound depth) reciprocalPositive.le) _
    _ = ENNReal.ofReal ((weightCoefficient * coefficient ^ (1 / order.toReal)) *
        (growth ^ depth * (ratio ^ (1 / order.toReal)) ^ (base ^ depth))) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg coefficientNonnegative (pow_nonneg ratioNonnegative _)) reciprocalPositive.le,
        ← ENNReal.ofReal_mul (mul_nonneg weightCoefficientNonnegative (pow_nonneg growthNonnegative depth)),
        Real.mul_rpow coefficientNonnegative (pow_nonneg ratioNonnegative _),
        ← Real.rpow_natCast_mul ratioNonnegative,
        mul_comm ((base ^ depth : ℕ) : ℝ) (1 / order.toReal),
        Real.rpow_mul_natCast ratioNonnegative]
      congr 1
      ring

end IGSIII.Probability
