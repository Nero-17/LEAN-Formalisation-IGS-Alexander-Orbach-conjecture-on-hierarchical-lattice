import IGSIII34.Diffusion.ExponentialClockLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators _root_.Topology

private theorem unitExponential_weighted_square_completion20261011 :
    (fun value : ℝ => (exponentialPDF 1 value).toReal * value ^ 2) =
      (Set.Ioi (0 : ℝ)).indicator (fun value => Real.exp (-value) * value ^ 2) := by
  funext value
  by_cases positive : 0 < value
  · simp [exponentialPDF_eq, positive.le, ENNReal.toReal_ofReal,
      (Real.exp_pos _).le, Set.indicator, positive]
  · by_cases zero : value = 0
    · subst value; simp
    · have negative : value < 0 := lt_of_le_of_ne (le_of_not_gt positive) zero
      simp [exponentialPDF_of_neg negative, Set.indicator, positive]

theorem unitExponential_memLp_two_completion20261011 :
    MemLp (fun value : ℝ => value) 2 (expMeasure 1) := by
  apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
  change Integrable (fun value : ℝ => value ^ 2) (volume.withDensity (exponentialPDF 1))
  rw [integrable_withDensity_iff_integrable_smul' (f := exponentialPDF 1)
    ((measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Eventually.of_forall (fun value => by exact ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, unitExponential_weighted_square_completion20261011]
  have gamma : IntegrableOn (fun value : ℝ => Real.exp (-value) * value ^ 2) (Set.Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := 3) (by norm_num) using 1 <;> norm_num
  exact gamma.integrable_indicator measurableSet_Ioi

theorem unitExponential_integral_square_completion20261011 :
    (∫ value : ℝ, value ^ 2 ∂expMeasure 1) = 2 := by
  change (∫ value : ℝ, value ^ 2 ∂volume.withDensity (exponentialPDF 1)) = 2
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF 1)
    ((measurable_exponentialPDFReal 1).ennreal_ofReal)
    (Eventually.of_forall (fun value => by exact ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul, unitExponential_weighted_square_completion20261011]
  rw [integral_indicator measurableSet_Ioi]
  have gamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1)
    (by norm_num) (by norm_num)
  norm_num at gamma
  simpa [mul_comm] using gamma

theorem unitExponential_variance_completion20261011 :
    variance (fun value : ℝ => value) (expMeasure 1) = 1 := by
  rw [variance_eq_sub unitExponential_memLp_two_completion20261011]
  change (∫ value : ℝ, value ^ 2 ∂expMeasure 1) - (∫ value : ℝ, value ∂expMeasure 1) ^ 2 = 1
  rw [unitExponential_integral_square_completion20261011, unitExponential_integral_id]
  norm_num

theorem exponentialCoordinate_memLp_two_completion20261011 (index : ℕ) :
    MemLp (fun holding : ℕ → ℝ => holding index) 2 exponentialHoldingTimeLaw := by
  exact unitExponential_memLp_two_completion20261011.comp_measurePreserving
    ⟨measurable_pi_apply index, exponentialHoldingTimeLaw_eval index⟩

theorem exponentialCoordinate_integral_completion20261011 (index : ℕ) :
    (∫ holding : ℕ → ℝ, holding index ∂exponentialHoldingTimeLaw) = 1 := by
  calc
    _ = ∫ value : ℝ, value ∂exponentialHoldingTimeLaw.map (fun holding => holding index) :=
      (integral_map (measurable_pi_apply index).aemeasurable
        (show AEStronglyMeasurable (fun value : ℝ => value) _ from measurable_id.aestronglyMeasurable)).symm
    _ = 1 := by rw [exponentialHoldingTimeLaw_eval, unitExponential_integral_id]

theorem exponentialCoordinate_variance_completion20261011 (index : ℕ) :
    variance (fun holding : ℕ → ℝ => holding index) exponentialHoldingTimeLaw = 1 := by
  exact (MeasurePreserving.variance_fun_comp
    (show MeasurePreserving (fun holding : ℕ → ℝ => holding index) exponentialHoldingTimeLaw (expMeasure 1) from
      ⟨measurable_pi_apply index, exponentialHoldingTimeLaw_eval index⟩)
    measurable_id.aemeasurable).trans unitExponential_variance_completion20261011

def weightedExponentialNoiseCompletion20261011 (weights : ℕ → ℝ) (count : ℕ) (holding : ℕ → ℝ) : ℝ :=
  ∑ index ∈ Finset.range count, weights index * (holding index - 1)

theorem weightedExponentialNoise_memLp_two_completion20261011 (weights : ℕ → ℝ) (count : ℕ) :
    MemLp (weightedExponentialNoiseCompletion20261011 weights count) 2 exponentialHoldingTimeLaw := by
  apply memLp_finsetSum
  intro index _
  exact ((exponentialCoordinate_memLp_two_completion20261011 index).sub (memLp_const 1)).const_mul (weights index)

theorem weightedExponentialNoise_integral_completion20261011 (weights : ℕ → ℝ) (count : ℕ) :
    (∫ holding, weightedExponentialNoiseCompletion20261011 weights count holding ∂exponentialHoldingTimeLaw) = 0 := by
  unfold weightedExponentialNoiseCompletion20261011
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro index _
    rw [integral_const_mul, integral_sub
      ((exponentialCoordinate_memLp_two_completion20261011 index).integrable (by norm_num)) (integrable_const 1),
      exponentialCoordinate_integral_completion20261011]
    simp
  · intro index _
    exact (((exponentialCoordinate_memLp_two_completion20261011 index).sub (memLp_const 1)).const_mul
      (weights index)).integrable (by norm_num)

theorem weightedExponentialNoise_variance_completion20261011 (weights : ℕ → ℝ) (count : ℕ) :
    variance (weightedExponentialNoiseCompletion20261011 weights count) exponentialHoldingTimeLaw =
      ∑ index ∈ Finset.range count, weights index ^ 2 := by
  let increments := fun index (holding : ℕ → ℝ) => weights index * (holding index - 1)
  have independence : iIndepFun increments exponentialHoldingTimeLaw :=
    exponentialHoldingTimeLaw_independent.comp (fun index => fun value : ℝ => weights index * (value - 1))
      (fun _ => by fun_prop)
  have result := IndepFun.variance_sum
    (X := increments) (s := Finset.range count)
    (fun index _ => ((exponentialCoordinate_memLp_two_completion20261011 index).sub (memLp_const 1)).const_mul (weights index))
    (fun _ _ _ _ different => independence.indepFun different)
  have identity : weightedExponentialNoiseCompletion20261011 weights count = ∑ index ∈ Finset.range count, increments index := by
    funext holding
    simp only [weightedExponentialNoiseCompletion20261011, increments, Finset.sum_apply]
  rw [identity]
  calc
    _ = ∑ index ∈ Finset.range count, variance (increments index) exponentialHoldingTimeLaw := result
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      dsimp only [increments]
      rw [variance_const_mul, variance_sub_const (exponentialCoordinate_memLp_two_completion20261011 index).aestronglyMeasurable,
        exponentialCoordinate_variance_completion20261011, mul_one]

theorem weightedExponentialNoise_probability_bound_completion20261011
    (weights : ℕ → ℝ) (count : ℕ) (bound threshold : ℝ) (thresholdPositive : 0 < threshold)
    (bounded : ∀ index < count, |weights index| ≤ bound) :
    exponentialHoldingTimeLaw {holding | threshold ≤ |weightedExponentialNoiseCompletion20261011 weights count holding|} ≤
      ENNReal.ofReal ((count : ℝ) * bound ^ 2 / threshold ^ 2) := by
  have chebyshev := meas_ge_le_variance_div_sq
    (weightedExponentialNoise_memLp_two_completion20261011 weights count) thresholdPositive
  rw [weightedExponentialNoise_integral_completion20261011,
    weightedExponentialNoise_variance_completion20261011] at chebyshev
  simp only [sub_zero] at chebyshev
  apply chebyshev.trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (sq_nonneg threshold)
  calc
    _ ≤ ∑ _index ∈ Finset.range count, bound ^ 2 := by
      apply Finset.sum_le_sum
      intro index member
      have boundHere := bounded index (Finset.mem_range.mp member)
      have nonnegative : 0 ≤ bound := (abs_nonneg _).trans boundHere
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (weights index)) nonnegative).mpr boundHere
    _ = _ := by simp

end
end IGSIII34.Diffusion
