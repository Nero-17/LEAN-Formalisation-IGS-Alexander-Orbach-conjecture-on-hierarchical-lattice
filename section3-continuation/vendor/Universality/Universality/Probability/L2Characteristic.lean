import Universality.Probability.L2LimitOperations
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A coupling bounds characteristic functions uniformly on bounded frequency intervals. -/
theorem norm_characteristic_kernel_sub_le (t x y : ℝ) :
    ‖Complex.exp ((t * x : ℝ) * Complex.I) - Complex.exp ((t * y : ℝ) * Complex.I)‖ ≤
      |t| * |x - y| := by
  have heq : Complex.exp ((t * x : ℝ) * Complex.I) - Complex.exp ((t * y : ℝ) * Complex.I) =
      Complex.exp ((t * y : ℝ) * Complex.I) *
        (Complex.exp (Complex.I * ((t * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq (by rw [Real.norm_eq_abs, abs_mul])

/-- Characteristic functions represented on the original probability space. -/
def randomCharacteristic (μ : Measure Ω) (f : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp ((t * f x : ℝ) * Complex.I) ∂μ

theorem integrable_characteristic_kernel [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    Integrable (fun x => Complex.exp ((t * f x : ℝ) * Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono
  · exact (Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hf.const_mul t)).mul_const Complex.I))
  · filter_upwards [] with x
    simp only [Complex.norm_exp_ofReal_mul_I, norm_one, le_refl]

theorem randomCharacteristic_eq_charFun_map {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    randomCharacteristic μ f t = charFun (μ.map f) t := by
  rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
  simp only [randomCharacteristic, Complex.ofReal_mul]

theorem randomCharacteristic_sub_bound [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℝ) :
    ‖randomCharacteristic μ f t - randomCharacteristic μ g t‖ ≤
      |t| * (eLpNorm (f - g) 2 μ).toReal := by
  have hdiff := hf.sub hg
  have hint := hdiff.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hlone : (∫ x, ‖f x - g x‖ ∂μ) ≤ (eLpNorm (f - g) 2 μ).toReal := by
    change (∫ x, ‖(f - g) x‖ ∂μ) ≤ _
    rw [integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable]
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.toReal_mono hdiff.eLpNorm_lt_top.ne
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hdiff.aestronglyMeasurable)
  unfold randomCharacteristic
  rw [← integral_sub (integrable_characteristic_kernel hf.aestronglyMeasurable t)
    (integrable_characteristic_kernel hg.aestronglyMeasurable t)]
  calc
    _ ≤ ∫ x, |t| * ‖f x - g x‖ ∂μ :=
      norm_integral_le_of_norm_le (hint.norm.const_mul |t|)
        (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using
          norm_characteristic_kernel_sub_le t (f x) (g x)))
    _ = |t| * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hlone (abs_nonneg _)

/-- The L² estimate gives local uniform, rather than only pointwise, convergence. -/
theorem L2_characteristic_uniform [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (limit : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hlimit : MemLp limit 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - limit) 2 μ) atTop (𝓝 0))
    (bound : ℝ) :
    TendstoUniformlyOn (fun n => randomCharacteristic μ (f n))
      (randomCharacteristic μ limit) atTop {t : ℝ | |t| ≤ bound} := by
  have hreal : Tendsto (fun n => (eLpNorm (f n - limit) 2 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hconv
  have hscaled : Tendsto (fun n => max bound 0 * (eLpNorm (f n - limit) 2 μ).toReal)
      atTop (𝓝 0) := by simpa using hreal.const_mul (max bound 0)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hscaled.eventually (gt_mem_nhds hε)] with n hn
  intro t ht
  rw [dist_comm, dist_eq_norm]
  exact ((randomCharacteristic_sub_bound (hf n) hlimit t).trans
    (mul_le_mul_of_nonneg_right (ht.trans (le_max_left _ _)) ENNReal.toReal_nonneg)).trans_lt hn

end
end Universality


