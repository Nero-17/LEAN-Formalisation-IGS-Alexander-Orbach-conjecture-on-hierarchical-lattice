import IGSIII4.SpectralDensity.Asymptotics
import Mathlib.Topology.Algebra.Order.Archimedean

/-! The limiting spectral dimension is continuous, strictly decreasing and
onto `(1,2)` on bases larger than one. Rational bases meet every open
subinterval of its range. -/

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open Filter Topology

theorem limitingDimension_continuousOn :
    ContinuousOn limitingDimension (Set.Ioi (1 : ℝ)) := by
  intro base baseAboveOne
  have basePositive : 0 < base := zero_lt_one.trans baseAboveOne
  have logarithmContinuous : ContinuousAt Real.log base := Real.continuousAt_log basePositive.ne'
  have denominatorPositive : 0 < 2 * Real.log base + Real.log (4 / 3 : ℝ) := by
    have := Real.log_pos baseAboveOne
    have : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
    positivity
  exact (((logarithmContinuous.add continuousAt_const).const_mul 2).div
    ((logarithmContinuous.const_mul 2).add continuousAt_const) denominatorPositive.ne').continuousWithinAt

theorem limitingDimension_strictAntiOn :
    StrictAntiOn limitingDimension (Set.Ioi (1 : ℝ)) := by
  intro first firstAboveOne second secondAboveOne firstBelowSecond
  have logarithmIncreasing := Real.log_lt_log (zero_lt_one.trans firstAboveOne) firstBelowSecond
  have fixedLogPositive : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have firstLogPositive := Real.log_pos firstAboveOne
  have secondLogPositive := Real.log_pos secondAboveOne
  have firstDenominatorPositive : 0 < 2 * Real.log first + Real.log (4 / 3 : ℝ) := by positivity
  have secondDenominatorPositive : 0 < 2 * Real.log second + Real.log (4 / 3 : ℝ) := by positivity
  change 2 * (Real.log second + Real.log (4 / 3 : ℝ)) /
      (2 * Real.log second + Real.log (4 / 3 : ℝ)) <
    2 * (Real.log first + Real.log (4 / 3 : ℝ)) /
      (2 * Real.log first + Real.log (4 / 3 : ℝ))
  apply (div_lt_div_iff₀ secondDenominatorPositive firstDenominatorPositive).mpr
  nlinarith [mul_pos fixedLogPositive (sub_pos.mpr logarithmIncreasing)]

theorem limitingDimension_image_Ioi :
    limitingDimension '' Set.Ioi (1 : ℝ) = Set.Ioo (1 : ℝ) 2 := by
  ext dimension
  constructor
  · rintro ⟨base, baseAboveOne, rfl⟩
    exact limitingDimension_mem_Ioo base baseAboveOne
  · intro dimensionInInterval
    obtain ⟨base, baseAboveOne, value⟩ := limitingDimension_surjective_Ioo dimension
      dimensionInInterval.1 dimensionInInterval.2
    exact ⟨base, baseAboveOne, value⟩

theorem rational_limitingDimension_mem_interval
    (lower upper : ℝ) (lowerAboveOne : 1 ≤ lower) (upperBelowTwo : upper ≤ 2)
    (nonemptyInterval : lower < upper) :
    ∃ base : ℚ, 1 < base ∧ limitingDimension (base : ℝ) ∈ Set.Ioo lower upper := by
  obtain ⟨first, firstAboveOne, firstValue⟩ := limitingDimension_surjective_Ioo
    ((lower + 2 * upper) / 3) (by linarith) (by linarith)
  obtain ⟨second, secondAboveOne, secondValue⟩ := limitingDimension_surjective_Ioo
    ((2 * lower + upper) / 3) (by linarith) (by linarith)
  have firstBelowSecond : first < second := by
    by_contra notBelow
    have order := limitingDimension_strictAntiOn.antitoneOn secondAboveOne firstAboveOne
      (le_of_not_gt notBelow)
    rw [firstValue, secondValue] at order
    linarith
  obtain ⟨base, firstBelowBase, baseBelowSecond⟩ := exists_rat_btwn firstBelowSecond
  have baseAboveOne : (1 : ℝ) < (base : ℝ) := firstAboveOne.trans firstBelowBase
  refine ⟨base, by exact_mod_cast baseAboveOne, ?_, ?_⟩
  · have order := limitingDimension_strictAntiOn baseAboveOne secondAboveOne baseBelowSecond
    rw [secondValue] at order
    linarith
  · have order := limitingDimension_strictAntiOn firstAboveOne baseAboveOne firstBelowBase
    rw [firstValue] at order
    linarith

end
end IGSIII4.SpectralDensity
