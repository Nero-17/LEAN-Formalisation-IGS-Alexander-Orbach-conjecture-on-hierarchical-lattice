import IGSIII34.Diffusion.ExponentialHoldingTimes
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology

theorem unitExponential_survival (time : ℝ) (nonnegative : 0 ≤ time) :
    (expMeasure 1).real (Set.Ioi time) = Real.exp (-time) := by
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
    ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, if_pos nonnegative]
  simp only [one_mul]
  ring

/-- The conditional survival probability of an already elapsed
rate-one exponential waiting time is unchanged. This is a waiting-time
identity, not a continuous-time Markov theorem. -/
theorem unitExponential_memoryless (elapsed remaining : ℝ)
    (elapsedNonnegative : 0 ≤ elapsed) (remainingNonnegative : 0 ≤ remaining) :
    (expMeasure 1).real (Set.Ioi (elapsed + remaining)) /
      (expMeasure 1).real (Set.Ioi elapsed) = (expMeasure 1).real (Set.Ioi remaining) := by
  rw [unitExponential_survival _ (add_nonneg elapsedNonnegative remainingNonnegative),
    unitExponential_survival _ elapsedNonnegative, unitExponential_survival _ remainingNonnegative,
    neg_add, Real.exp_add]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

theorem exponentialHoldingTimeLaw_survival (index : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw.real {holdingTimes | time < holdingTimes index} = Real.exp (-time) := by
  have mapped := congrArg (fun measure : Measure ℝ => measure.real (Set.Ioi time))
    (exponentialHoldingTimeLaw_eval index)
  rw [measureReal_def, Measure.map_apply (measurable_pi_apply index) measurableSet_Ioi] at mapped
  exact mapped.trans (unitExponential_survival time nonnegative)

end
end IGSIII34.Diffusion
