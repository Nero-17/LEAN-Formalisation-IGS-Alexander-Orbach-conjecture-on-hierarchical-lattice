import IGSIII34.Diffusion.ContinuousWalkConstruction
import IGSIII34.Diffusion.ExponentialMemoryless

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem holdingJumpIndex_eq_zero_iff (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    holdingJumpIndex holdingTimes time = 0 ↔ time < holdingTimes 0 := by
  constructor
  · intro equality
    have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
      nonexplosion time timeNonnegative
    simpa [equality, cumulativeHoldingTime] using interval.2
  · intro upper
    apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
    · simpa [cumulativeHoldingTime] using timeNonnegative
    · simpa [cumulativeHoldingTime] using upper

theorem holdingJumpIndex_ge_iff (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (count : ℕ) :
    count ≤ holdingJumpIndex holdingTimes time ↔ cumulativeHoldingTime holdingTimes count ≤ time := by
  have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le)
    nonexplosion time timeNonnegative
  constructor
  · intro bound
    exact (cumulativeHoldingTime_monotone holdingTimes (fun index => (positive index).le) bound).trans interval.1
  · intro bound
    by_contra failure
    have indexSmall : holdingJumpIndex holdingTimes time + 1 ≤ count := by omega
    exact (not_lt_of_ge bound) (interval.2.trans_le
      (cumulativeHoldingTime_monotone holdingTimes (fun index => (positive index).le) indexSmall))

/-- Exact initial no-jump probability of the explicit independent waiting-time law. -/
theorem exponentialHoldingTimeLaw_no_jump (time : ℝ) (timeNonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw.real {holdingTimes | holdingJumpIndex holdingTimes time = 0} =
      Real.exp (-time) := by
  calc
    _ = exponentialHoldingTimeLaw.real {holdingTimes | time < holdingTimes 0} := by
      apply measureReal_congr
      filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
        with holdingTimes positive nonexplosion
      exact propext (holdingJumpIndex_eq_zero_iff holdingTimes positive nonexplosion time timeNonnegative)
    _ = _ := exponentialHoldingTimeLaw_survival 0 time timeNonnegative

theorem exponentialHoldingTimeLaw_coordinate_cdf (index : ℕ) (time : ℝ)
    (timeNonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes index ≤ time} =
      1 - Real.exp (-time) := by
  have complement : {holdingTimes : ℕ → ℝ | holdingTimes index ≤ time} =
      {holdingTimes | time < holdingTimes index}ᶜ := by ext; simp
  rw [complement, measureReal_compl (measurableSet_lt measurable_const (measurable_pi_apply index)),
    probReal_univ, exponentialHoldingTimeLaw_survival index time timeNonnegative]

/-- Two jumps require two independent waiting times shorter than the observation time.
This gives a quadratic small-time bound without assuming a continuous-time Markov theorem. -/
theorem exponentialHoldingTimeLaw_two_jump_bound (time : ℝ) (timeNonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw.real {holdingTimes | 2 ≤ holdingJumpIndex holdingTimes time} ≤
      (1 - Real.exp (-time)) ^ 2 := by
  have bound : {holdingTimes : ℕ → ℝ | 2 ≤ holdingJumpIndex holdingTimes time} ≤ᵐ[
      exponentialHoldingTimeLaw]
      {holdingTimes | holdingTimes 0 ≤ time ∧ holdingTimes 1 ≤ time} := by
    filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion]
      with holdingTimes positive nonexplosion
    intro jumps
    have sumBound := (holdingJumpIndex_ge_iff holdingTimes positive nonexplosion time timeNonnegative 2).mp jumps
    simp only [cumulativeHoldingTime, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at sumBound
    constructor <;> linarith [positive 0, positive 1]
  have independent := exponentialHoldingTimeLaw_independent.indepFun (i := 0) (j := 1) (by decide)
  have intersection := independent.measure_inter_preimage_eq_mul (Set.Iic time) (Set.Iic time)
    measurableSet_Iic measurableSet_Iic
  have productProbability :
      exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 0 ≤ time ∧ holdingTimes 1 ≤ time} =
        (1 - Real.exp (-time)) ^ 2 := by
    change (exponentialHoldingTimeLaw
      ((fun holdingTimes : ℕ → ℝ => holdingTimes 0) ⁻¹' Set.Iic time ∩
        (fun holdingTimes : ℕ → ℝ => holdingTimes 1) ⁻¹' Set.Iic time)).toReal = _
    rw [intersection, ENNReal.toReal_mul]
    change exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 0 ≤ time} *
      exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 1 ≤ time} = _
    rw [exponentialHoldingTimeLaw_coordinate_cdf 0 time timeNonnegative,
      exponentialHoldingTimeLaw_coordinate_cdf 1 time timeNonnegative, pow_two]
  rw [← productProbability]
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae bound)

end
end IGSIII34.Diffusion
