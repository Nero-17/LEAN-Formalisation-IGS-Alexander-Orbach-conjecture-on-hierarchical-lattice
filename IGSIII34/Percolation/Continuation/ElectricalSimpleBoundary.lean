import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import IGSIII34.Percolation.Continuation.ElectricalNormalizedEigenvalue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal ENNReal

def electricalSimpleBoundary (index : ℕ) : SimpleFunc ℝ≥0 ℝ :=
  (SimpleFunc.approxOn (fun value : ℝ≥0 => Real.log (value:ℝ))
    (Real.measurable_log.comp NNReal.continuous_coe.measurable) Set.univ 0 (Set.mem_univ 0) index).map Real.exp

theorem electricalSimpleBoundary_positive (index : ℕ) (value : ℝ≥0) :
    0 < electricalSimpleBoundary index value := Real.exp_pos _

theorem electricalSimpleBoundary_tendsto (value : ℝ≥0) (positive : 0 < value) :
    Tendsto (fun index => electricalSimpleBoundary index value) atTop (𝓝 (value:ℝ)) := by
  have convergence := SimpleFunc.tendsto_approxOn
    (Real.measurable_log.comp NNReal.continuous_coe.measurable) (Set.mem_univ (0:ℝ))
    (x := value) (by simp)
  have composed := Real.continuous_exp.continuousAt.tendsto.comp convergence
  have valuePositive : 0 < (value:ℝ) := by exact_mod_cast positive
  dsimp only [Function.comp_def] at composed
  rw [Real.exp_log valuePositive] at composed
  simpa only [electricalSimpleBoundary, SimpleFunc.map_apply, Function.comp_def,
    ] using composed

theorem electricalSimpleBoundary_rpow_bound (index : ℕ) (value : ℝ≥0) (positive : 0 < value) (exponent : ℝ) :
    ‖(electricalSimpleBoundary index value)^exponent‖ ≤
      (value:ℝ)^(2*|exponent|)+(value:ℝ)^(-2*|exponent|) := by
  let approximation := SimpleFunc.approxOn (fun value : ℝ≥0 => Real.log (value:ℝ))
    (Real.measurable_log.comp NNReal.continuous_coe.measurable) Set.univ 0 (Set.mem_univ 0) index value
  have logBound : |approximation| ≤ 2*|Real.log (value:ℝ)| := by
    have comparison := SimpleFunc.norm_approxOn_zero_le
      (Real.measurable_log.comp NNReal.continuous_coe.measurable) (Set.mem_univ (0:ℝ)) value index
    simpa only [approximation, Function.comp_def, Real.norm_eq_abs, two_mul] using comparison
  have exponentBound : approximation*exponent ≤ 2 * |exponent| * |Real.log (value:ℝ)| := by
    calc
      _ ≤ |approximation*exponent| := le_abs_self _
      _ = |approximation| * |exponent| := abs_mul _ _
      _ ≤ (2*|Real.log (value:ℝ)|) * |exponent| := mul_le_mul_of_nonneg_right logBound (abs_nonneg _)
      _ = _ := by ring
  have valuePositive : 0 < (value:ℝ) := by exact_mod_cast positive
  have exponentialBound : Real.exp (2 * |exponent| * |Real.log (value:ℝ)|) ≤
      (value:ℝ)^(2*|exponent|)+(value:ℝ)^(-2*|exponent|) := by
    rcases le_total 0 (Real.log (value:ℝ)) with nonnegative | nonpositive
    · rw [abs_of_nonneg nonnegative, Real.rpow_def_of_pos valuePositive,
        Real.rpow_def_of_pos valuePositive]
      have equality : 2 * |exponent| * Real.log (value:ℝ) = Real.log (value:ℝ)*(2*|exponent|) := by ring
      rw [equality]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos nonpositive, Real.rpow_def_of_pos valuePositive,
        Real.rpow_def_of_pos valuePositive]
      have equality : 2 * |exponent| * (-Real.log (value:ℝ)) = Real.log (value:ℝ)*(-2*|exponent|) := by ring
      rw [equality]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (electricalSimpleBoundary_positive index value) exponent),
    Real.rpow_def_of_pos (electricalSimpleBoundary_positive index value)]
  change Real.exp (Real.log (Real.exp approximation)*exponent) ≤ _
  rw [Real.log_exp]
  exact (Real.exp_le_exp.mpr exponentBound).trans exponentialBound

theorem electricalSimpleBoundary_real_moments_tendsto (law : ProbabilityMeasure ℝ≥0)
    (positive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (exponent : ℝ) :
    Tendsto (fun index => ∫ value, (electricalSimpleBoundary index value)^exponent ∂(law:Measure ℝ≥0))
      atTop (𝓝 (∫ value : ℝ≥0, (value:ℝ)^exponent ∂(law:Measure ℝ≥0))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun value : ℝ≥0 => (value:ℝ)^(2*|exponent|)+(value:ℝ)^(-2*|exponent|))
    (fun index => ((electricalSimpleBoundary index).measurable.pow_const exponent).aestronglyMeasurable)
    ((moments _).add (moments _))
    (fun index => positive.mono (fun value positive => electricalSimpleBoundary_rpow_bound index value positive exponent))
  filter_upwards [positive] with value positive
  exact (Real.continuousAt_rpow_const (value:ℝ) exponent (Or.inl (by exact_mod_cast positive.ne'))).tendsto.comp
    (electricalSimpleBoundary_tendsto value positive)

end
end IGSIII34.Percolation
