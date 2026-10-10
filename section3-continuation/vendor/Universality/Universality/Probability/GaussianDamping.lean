import Universality.Probability.InverseCharacteristic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem inverseCharacteristic_gaussianDamping_tendsto (function : ℝ → ℂ)
    (hintegrable : Integrable function) (x : ℝ) :
    Tendsto (fun n : ℕ => inverseCharacteristic
      (fun t : ℝ => (Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2) : ℂ) * function t) x)
      atTop (𝓝 (inverseCharacteristic function x)) := by
  unfold inverseCharacteristic
  apply Tendsto.const_mul
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖function t‖)
  · intro n
    exact (show Continuous (fun t : ℝ => Complex.exp (-(t * x : ℝ) * Complex.I)) by fun_prop).aestronglyMeasurable.mul
      ((show Continuous (fun t : ℝ => (Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2) : ℂ)) by fun_prop).aestronglyMeasurable.mul
        hintegrable.aestronglyMeasurable)
  · exact hintegrable.norm
  · intro n
    exact Eventually.of_forall (fun t => by
      have hphase : ‖Complex.exp (-(t * x : ℝ) * Complex.I)‖ = 1 := by simp [Complex.norm_exp]
      have hgaussian : ‖(Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg t)
      rw [norm_mul, hphase, one_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hgaussian)
  · exact Eventually.of_forall (fun t => by
      have hreal : Tendsto (fun n : ℕ => Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2))
          atTop (𝓝 1) := by
        simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg.mul_const (t ^ 2))
      have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      simpa using (tendsto_const_nhds (x := Complex.exp (-(t * x : ℝ) * Complex.I))).mul
        (hcomplex.mul_const (function t)))

end
end Universality
