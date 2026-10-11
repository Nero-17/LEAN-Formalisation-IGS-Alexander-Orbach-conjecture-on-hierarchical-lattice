import IGSIII34.Diffusion.ExponentialMemoryless

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology

/-- The complete residual-waiting distribution after deterministic elapsed
time is the original exponential distribution, multiplied by survival mass.
This identifies every measurable residual event, rather than only survival
probabilities. -/
theorem unitExponential_restricted_residual_law (elapsed : ℝ)
    (elapsedNonnegative : 0 ≤ elapsed) :
    ((expMeasure 1).restrict (Set.Ioi elapsed)).map (fun waiting => waiting - elapsed) =
      ENNReal.ofReal (Real.exp (-elapsed)) • expMeasure 1 := by
  apply Measure.ext_of_Iic
  intro remaining
  rw [Measure.map_apply (show Measurable (fun waiting : ℝ => waiting - elapsed) from by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage
      (show Measurable (fun waiting : ℝ => waiting - elapsed) from by fun_prop))]
  have interval : (fun waiting : ℝ => waiting - elapsed) ⁻¹' Set.Iic remaining ∩ Set.Ioi elapsed =
      Set.Ioc elapsed (elapsed + remaining) := by
    ext waiting
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]
    constructor <;> intro bounds <;> constructor <;> linarith
  rw [interval, Measure.smul_apply, smul_eq_mul]
  by_cases remainingNonnegative : 0 ≤ remaining
  · conv_lhs =>
      rw [← measure_cdf (expMeasure 1), StieltjesFunction.measure_Ioc,
        cdf_expMeasure_eq zero_lt_one, cdf_expMeasure_eq zero_lt_one,
        if_pos (add_nonneg elapsedNonnegative remainingNonnegative), if_pos elapsedNonnegative]
    rw [← ofReal_cdf, cdf_expMeasure_eq zero_lt_one, if_pos remainingNonnegative,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp only [one_mul]
    rw [neg_add, Real.exp_add]
    ring
  · have intervalEmpty : Set.Ioc elapsed (elapsed + remaining) = ∅ := by
      apply Set.Ioc_eq_empty_of_le
      linarith
    rw [intervalEmpty, measure_empty, ← ofReal_cdf, cdf_expMeasure_eq zero_lt_one,
      if_neg remainingNonnegative]
    simp

end
end IGSIII34.Diffusion


