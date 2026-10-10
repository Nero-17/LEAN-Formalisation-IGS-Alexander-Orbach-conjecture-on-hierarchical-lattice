import IGSIII.Chemical.SmallBall.OrbitExponentialMoments
import IGSIII.Chemical.SubstitutionPaths.ExponentialContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Filter Substitution
open scoped ENNReal Topology

noncomputable section

theorem signed_exponential_integrals_tendsto
    {Sample : Type*} [MeasurableSpace Sample] (μ : Measure Sample) [IsProbabilityMeasure μ]
    (sequence : ℕ → Lp ℝ 2 μ) (fixed : Lp ℝ 2 μ)
    (amplitude error parameter : ℝ) (amplitudePositive : 0 < amplitude)
    (errorPositive : 0 < error) (errorBelow : error < amplitude) (parameterPositive : 0 < parameter)
    (convergence : Tendsto sequence atTop (𝓝 (amplitude • fixed)))
    (sequenceNonnegative : ∀ depth, 0 ≤ sequence depth) (fixedNonnegative : 0 ≤ fixed)
    (sequenceBound endpointBound : ℝ)
    (sequenceMoments : ∀ depth, (∫⁻ sample, ENNReal.ofReal (Real.exp (2 * parameter * sequence depth sample)) ∂μ) ≤
      ENNReal.ofReal sequenceBound)
    (endpointMoment : (∫⁻ sample, ENNReal.ofReal (Real.exp (2 * parameter * amplitude * fixed sample)) ∂μ) ≤
      ENNReal.ofReal endpointBound) :
    (∀ depth, Integrable (fun sample => Real.exp (parameter *
      (sequence depth sample - (amplitude + error) * fixed sample))) μ ∧
      Integrable (fun sample => Real.exp (parameter * ((amplitude - error) * fixed sample - sequence depth sample))) μ) ∧
    Tendsto (fun depth => ∫ sample, Real.exp (parameter *
      (sequence depth sample - (amplitude + error) * fixed sample)) ∂μ) atTop
      (𝓝 (∫ sample, Real.exp (-parameter * error * fixed sample) ∂μ)) ∧
    Tendsto (fun depth => ∫ sample, Real.exp (parameter *
      ((amplitude - error) * fixed sample - sequence depth sample)) ∂μ) atTop
      (𝓝 (∫ sample, Real.exp (-parameter * error * fixed sample) ∂μ)) := by
  let upperSequence : ℕ → Lp ℝ 2 μ := fun depth => parameter • (sequence depth - (amplitude + error) • fixed)
  let lowerSequence : ℕ → Lp ℝ 2 μ := fun depth => parameter • ((amplitude - error) • fixed - sequence depth)
  let limit : Lp ℝ 2 μ := (-parameter * error) • fixed
  have upperEquality (depth : ℕ) : upperSequence depth =ᵐ[μ]
      fun sample => parameter * (sequence depth sample - (amplitude + error) * fixed sample) := by
    filter_upwards [Lp.coeFn_smul parameter (sequence depth - (amplitude + error) • fixed),
      Lp.coeFn_sub (sequence depth) ((amplitude + error) • fixed), Lp.coeFn_smul (amplitude + error) fixed]
      with sample scalarEquality subEquality fixedEquality
    simp only [upperSequence, scalarEquality, Pi.smul_apply, smul_eq_mul, subEquality, Pi.sub_apply, fixedEquality]
  have lowerEquality (depth : ℕ) : lowerSequence depth =ᵐ[μ]
      fun sample => parameter * ((amplitude - error) * fixed sample - sequence depth sample) := by
    filter_upwards [Lp.coeFn_smul parameter ((amplitude - error) • fixed - sequence depth),
      Lp.coeFn_sub ((amplitude - error) • fixed) (sequence depth), Lp.coeFn_smul (amplitude - error) fixed]
      with sample scalarEquality subEquality fixedEquality
    simp only [lowerSequence, scalarEquality, Pi.smul_apply, smul_eq_mul, subEquality, Pi.sub_apply, fixedEquality]
  have limitEquality : limit =ᵐ[μ] fun sample => -parameter * error * fixed sample := by
    filter_upwards [Lp.coeFn_smul (-parameter * error) fixed] with sample equality
    exact equality
  have upperConvergence : Tendsto upperSequence atTop (𝓝 limit) := by
    convert (convergence.sub_const ((amplitude + error) • fixed)).const_smul parameter using 1
    dsimp [limit]
    rw [← sub_smul, smul_smul]
    congr 1
    ring
  have lowerConvergence : Tendsto lowerSequence atTop (𝓝 limit) := by
    convert (tendsto_const_nhds.sub convergence).const_smul parameter using 1
    dsimp [limit]
    rw [← sub_smul, smul_smul]
    congr 1
    ring
  have upperMoments (depth : ℕ) : (∫⁻ sample, ENNReal.ofReal (Real.exp (2 * upperSequence depth sample)) ∂μ) ≤
      ENNReal.ofReal (max 1 sequenceBound) := by
    refine (lintegral_mono_ae ?_).trans ((sequenceMoments depth).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
    filter_upwards [upperEquality depth, (Lp.coeFn_nonneg fixed).mpr fixedNonnegative] with sample equality nonnegative
    change 0 ≤ fixed sample at nonnegative
    rw [equality]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ amplitude + error by linarith) nonnegative]
  have lowerMoments (depth : ℕ) : (∫⁻ sample, ENNReal.ofReal (Real.exp (2 * lowerSequence depth sample)) ∂μ) ≤
      ENNReal.ofReal (max 1 endpointBound) := by
    refine (lintegral_mono_ae ?_).trans (endpointMoment.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
    filter_upwards [lowerEquality depth, (Lp.coeFn_nonneg fixed).mpr fixedNonnegative,
      (Lp.coeFn_nonneg (sequence depth)).mpr (sequenceNonnegative depth)] with sample equality fixedPositive sequencePositive
    change 0 ≤ fixed sample at fixedPositive
    change 0 ≤ sequence depth sample at sequencePositive
    rw [equality]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg errorPositive.le fixedPositive]
  have upperMemLp (depth : ℕ) := exponential_memLp_two_of_lintegral_bound μ (upperSequence depth)
    ENNReal.ofReal_ne_top (upperMoments depth)
  have lowerMemLp (depth : ℕ) := exponential_memLp_two_of_lintegral_bound μ (lowerSequence depth)
    ENNReal.ofReal_ne_top (lowerMoments depth)
  have limitMemLp : MemLp (fun sample => Real.exp (limit sample)) 2 μ := by
    apply MemLp.of_bound (Lp.stronglyMeasurable limit).measurable.exp.aestronglyMeasurable 1
    filter_upwards [limitEquality, (Lp.coeFn_nonneg fixed).mpr fixedNonnegative] with sample equality nonnegative
    change 0 ≤ fixed sample at nonnegative
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), equality, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith : -parameter * error ≤ 0) nonnegative
  have upperRealMoments (depth : ℕ) : (∫ sample, Real.exp (2 * upperSequence depth sample) ∂μ) ≤ max 1 sequenceBound :=
    integral_le_of_lintegral_ofReal_le μ _
      ((Lp.stronglyMeasurable (upperSequence depth)).measurable.const_mul 2).exp.aestronglyMeasurable
      (Eventually.of_forall (fun _ => Real.exp_nonneg _)) (zero_le_one.trans (le_max_left _ _)) (upperMoments depth)
  have lowerRealMoments (depth : ℕ) : (∫ sample, Real.exp (2 * lowerSequence depth sample) ∂μ) ≤ max 1 endpointBound :=
    integral_le_of_lintegral_ofReal_le μ _
      ((Lp.stronglyMeasurable (lowerSequence depth)).measurable.const_mul 2).exp.aestronglyMeasurable
      (Eventually.of_forall (fun _ => Real.exp_nonneg _)) (zero_le_one.trans (le_max_left _ _)) (lowerMoments depth)
  have limitIntegral : (∫ sample, Real.exp (limit sample) ∂μ) = ∫ sample, Real.exp (-parameter * error * fixed sample) ∂μ :=
    integral_congr_ae (limitEquality.mono (fun _ equality => congrArg Real.exp equality))
  have upperIntegral (depth : ℕ) : (∫ sample, Real.exp (upperSequence depth sample) ∂μ) =
      ∫ sample, Real.exp (parameter * (sequence depth sample - (amplitude + error) * fixed sample)) ∂μ :=
    integral_congr_ae ((upperEquality depth).mono (fun _ equality => congrArg Real.exp equality))
  have lowerIntegral (depth : ℕ) : (∫ sample, Real.exp (lowerSequence depth sample) ∂μ) =
      ∫ sample, Real.exp (parameter * ((amplitude - error) * fixed sample - sequence depth sample)) ∂μ :=
    integral_congr_ae ((lowerEquality depth).mono (fun _ equality => congrArg Real.exp equality))
  refine ⟨fun depth => ⟨(upperMemLp depth).integrable (by norm_num) |>.congr
    ((upperEquality depth).mono (fun _ equality => congrArg Real.exp equality)),
    (lowerMemLp depth).integrable (by norm_num) |>.congr
    ((lowerEquality depth).mono (fun _ equality => congrArg Real.exp equality))⟩, ?_, ?_⟩
  · simpa only [upperIntegral, limitIntegral] using exponential_integral_tendsto_of_lp2_tendsto μ
      upperSequence limit upperConvergence upperMemLp limitMemLp (max 1 sequenceBound) upperRealMoments
  · simpa only [lowerIntegral, limitIntegral] using exponential_integral_tendsto_of_lp2_tendsto μ
      lowerSequence limit lowerConvergence lowerMemLp limitMemLp (max 1 endpointBound) lowerRealMoments

end
end IGSIII.Chemical.SmallBall