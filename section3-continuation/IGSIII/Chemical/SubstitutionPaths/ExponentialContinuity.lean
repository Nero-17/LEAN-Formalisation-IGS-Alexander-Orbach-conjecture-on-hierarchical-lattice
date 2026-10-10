import IGSIII.Chemical.SubstitutionPaths.CommonPrefixL2
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section

open MeasureTheory Filter
open scoped Topology

theorem abs_exp_sub_exp_le (first second : ℝ) :
    |Real.exp first - Real.exp second| ≤ |first - second| * (Real.exp first + Real.exp second) := by
  have ordered_bound (first second : ℝ) (ordered : first ≤ second) :
      Real.exp second - Real.exp first ≤ (second - first) * Real.exp second := by
    have tangent := Real.add_one_le_exp (first - second)
    have multiplied := mul_le_mul_of_nonneg_right tangent (Real.exp_nonneg second)
    rw [← Real.exp_add] at multiplied
    have exponent : first - second + second = first := by ring
    rw [exponent] at multiplied
    nlinarith
  rcases le_total first second with ordered | ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr ordered)),
      abs_of_nonpos (sub_nonpos.mpr ordered)]
    have bound := ordered_bound first second ordered
    have additional := mul_nonneg (sub_nonneg.mpr ordered) (Real.exp_nonneg first)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr ordered)),
      abs_of_nonneg (sub_nonneg.mpr ordered)]
    have bound := ordered_bound second first ordered
    have additional := mul_nonneg (sub_nonneg.mpr ordered) (Real.exp_nonneg second)
    nlinarith

variable {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)

/-- The exponential integral is locally Lipschitz in L2 when its exponential
L2 norms are bounded. Cauchy--Schwarz supplies the quantitative constant. -/
theorem exponential_integral_difference_le_lp2 [IsFiniteMeasure measure]
    (first second : Lp ℝ 2 measure)
    (first_exp : MemLp (fun sample => Real.exp (first sample)) 2 measure)
    (second_exp : MemLp (fun sample => Real.exp (second sample)) 2 measure) :
    |(∫ sample, Real.exp (first sample) ∂measure) -
      (∫ sample, Real.exp (second sample) ∂measure)| ≤
      ‖first - second‖ *
        (‖first_exp.toLp (fun sample => Real.exp (first sample))‖ +
          ‖second_exp.toLp (fun sample => Real.exp (second sample))‖) := by
  let difference := (Lp.memLp (first - second)).norm.toLp (fun sample => ‖(first - second) sample‖)
  let exponentials := first_exp.toLp (fun sample => Real.exp (first sample)) +
    second_exp.toLp (fun sample => Real.exp (second sample))
  have difference_ae : difference =ᵐ[measure] (fun sample => |first sample - second sample|) := by
    filter_upwards [MemLp.coeFn_toLp (Lp.memLp (first - second)).norm,
      Lp.coeFn_sub first second] with sample first_equal second_equal
    calc
      difference sample = ‖(first - second) sample‖ := first_equal
      _ = |first sample - second sample| := by rw [second_equal]; rfl
  have exponentials_ae : exponentials =ᵐ[measure]
      (fun sample => Real.exp (first sample) + Real.exp (second sample)) := by
    filter_upwards [Lp.coeFn_add (first_exp.toLp _) (second_exp.toLp _),
      first_exp.coeFn_toLp, second_exp.coeFn_toLp] with sample sum_equal first_equal second_equal
    simp only [exponentials, sum_equal, Pi.add_apply, first_equal, second_equal]
  have product_integrable : Integrable (fun sample => difference sample * exponentials sample) measure := by
    simpa only [RCLike.inner_apply, conj_trivial] using L2.integrable_inner (𝕜 := ℝ) exponentials difference
  have norm_identity : ‖difference‖ = ‖first - second‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have cauchy := real_inner_le_norm difference exponentials
  rw [L2.inner_def] at cauchy
  simp only [RCLike.inner_apply, conj_trivial] at cauchy
  rw [← integral_sub (first_exp.integrable (by norm_num)) (second_exp.integrable (by norm_num))]
  calc
    _ ≤ ∫ sample, |Real.exp (first sample) - Real.exp (second sample)| ∂measure := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun sample => Real.exp (first sample) - Real.exp (second sample))
    _ ≤ ∫ sample, difference sample * exponentials sample ∂measure := by
      apply integral_mono_ae ((first_exp.integrable (by norm_num)).sub
        (second_exp.integrable (by norm_num))).norm product_integrable
      filter_upwards [difference_ae, exponentials_ae] with sample first_equal second_equal
      simpa only [Pi.sub_apply, Real.norm_eq_abs, first_equal, second_equal] using abs_exp_sub_exp_le (first sample) (second sample)
    _ ≤ ‖difference‖ * ‖exponentials‖ := by simpa only [mul_comm] using cauchy
    _ ≤ _ := by
      rw [norm_identity]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

theorem exponential_lp2_norm_sq (value : Lp ℝ 2 measure)
    (exponential : MemLp (fun sample => Real.exp (value sample)) 2 measure) :
    ‖exponential.toLp (fun sample => Real.exp (value sample))‖ ^ 2 =
      ∫ sample, Real.exp (2 * value sample) ∂measure := by
  rw [lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [exponential.coeFn_toLp] with sample equality
  rw [equality, ← Real.exp_nat_mul]
  congr 1

/-- Uniform second exponential moments and actual L2 convergence imply
convergence of the exponential integrals. -/
theorem exponential_integral_tendsto_of_lp2_tendsto [IsFiniteMeasure measure]
    (sequence : ℕ → Lp ℝ 2 measure) (limit : Lp ℝ 2 measure)
    (convergence : Tendsto sequence atTop (𝓝 limit))
    (sequence_exp : ∀ depth, MemLp (fun sample => Real.exp (sequence depth sample)) 2 measure)
    (limit_exp : MemLp (fun sample => Real.exp (limit sample)) 2 measure)
    (bound : ℝ) (moment_bound : ∀ depth,
      (∫ sample, Real.exp (2 * sequence depth sample) ∂measure) ≤ bound) :
    Tendsto (fun depth => ∫ sample, Real.exp (sequence depth sample) ∂measure) atTop
      (𝓝 (∫ sample, Real.exp (limit sample) ∂measure)) := by
  have norm_bound : ∀ depth,
      ‖(sequence_exp depth).toLp (fun sample => Real.exp (sequence depth sample))‖ ≤ Real.sqrt bound := by
    intro depth
    have square := (exponential_lp2_norm_sq measure (sequence depth) (sequence_exp depth)).trans_le (moment_bound depth)
    exact (Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) square)).mpr square
  have upper_convergence : Tendsto (fun depth => ‖sequence depth - limit‖ *
      (Real.sqrt bound + ‖limit_exp.toLp (fun sample => Real.exp (limit sample))‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_iff_norm_sub_tendsto_zero.mp convergence).mul_const
      (Real.sqrt bound + ‖limit_exp.toLp (fun sample => Real.exp (limit sample))‖)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ upper_convergence
  intro depth
  exact (exponential_integral_difference_le_lp2 measure (sequence depth) limit
    (sequence_exp depth) limit_exp).trans (mul_le_mul_of_nonneg_left
      (add_le_add (norm_bound depth) le_rfl) (norm_nonneg _))

end
end IGSIII.Chemical.Substitution
