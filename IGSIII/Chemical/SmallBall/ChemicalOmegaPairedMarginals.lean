import IGSIII.Chemical.SmallBall.ChemicalOmegaMoments
import IGSIII.Chemical.SmallBall.MeasurePairedBarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Filter
open scoped ENNReal

noncomputable section

theorem integral_le_of_lintegral_ofReal_le {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (value : Sample → ℝ) (measurable : AEStronglyMeasurable value measure)
    (nonnegative : 0 ≤ᵐ[measure] value) {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (integralBound : (∫⁻ sample, ENNReal.ofReal (value sample) ∂measure) ≤ ENNReal.ofReal bound) :
    (∫ sample, value sample ∂measure) ≤ bound := by
  rw [integral_eq_lintegral_of_nonneg_ae nonnegative measurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top integralBound).trans_eq (ENNReal.toReal_ofReal boundNonnegative)

theorem exists_uniform_chemicalOmega_paired_exponential_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {ratio : ℝ} (ratioPositive : 0 < ratio) :
    ∃ scale : ℝ, 1 ≤ scale ∧
      ∀ first ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      ∀ second ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
        Integrable (fun marks => Real.exp (first marks - scale * second marks))
          (independentInnovationLaw rule p positive lessOne fixedPoint) ∧
        (∫ marks, Real.exp (first marks - scale * second marks)
          ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio := by
  obtain ⟨bound, exponentialValid⟩ := exists_uniform_chemicalOmega_exponential_moment
    rule classical p positive lessOne fixedPoint constant growth constantPositive growthPositive meanBounds 2 (by norm_num)
  have boundPositive : 0 < max 1 bound := zero_lt_one.trans_le (le_max_left _ _)
  have sqrtPositive : 0 < Real.sqrt (max 1 bound) := Real.sqrt_pos.mpr boundPositive
  have targetPositive : 0 < (ratio / Real.sqrt (max 1 bound)) ^ 2 := sq_pos_of_pos (div_pos ratioPositive sqrtPositive)
  obtain ⟨parameter, parameterPositive, laplaceValid⟩ := exists_uniform_chemicalOmega_laplace_decay
    rule classical p positive lessOne fixedPoint constant growth growthPositive meanBounds targetPositive
  refine ⟨max 1 (parameter / 2), le_max_left _ _, fun first firstMembership second secondMembership => ?_⟩
  have scalePositive : 0 < max 1 (parameter / 2) := zero_lt_one.trans_le (le_max_left _ _)
  have secondNonnegative : 0 ≤ᵐ[independentInnovationLaw rule p positive lessOne fixedPoint] second :=
    (chemicalOmega_ae_positive rule classical p positive lessOne fixedPoint constant growth growthPositive meanBounds second secondMembership).mono
      (fun _ bound => bound.le)
  have firstDoubleBound : (∫⁻ marks, ENNReal.ofReal (Real.exp (2 * first marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal (max 1 bound) :=
    (exponentialValid first firstMembership).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  have firstDoubleIntegrable : Integrable (fun marks => Real.exp (2 * first marks))
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    refine ⟨((Lp.stronglyMeasurable first).measurable.const_mul 2).exp.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun marks => Real.exp_nonneg (2 * first marks)))).mpr
      (lt_of_le_of_lt firstDoubleBound ENNReal.ofReal_lt_top)
  have firstMemLp : MemLp (fun marks => Real.exp (first marks)) 2
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    apply (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable first).measurable.exp.aestronglyMeasurable).mpr
    convert firstDoubleIntegrable using 1
    funext marks
    rw [← Real.exp_nat_mul]
    norm_num
  have secondMemLp : MemLp (fun marks => Real.exp (-max 1 (parameter / 2) * second marks)) 2
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    apply MemLp.of_bound ((Lp.stronglyMeasurable second).measurable.const_mul (-max 1 (parameter / 2))).exp.aestronglyMeasurable 1
    filter_upwards [secondNonnegative] with marks nonnegative
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr scalePositive.le) nonnegative
  have pairedIntegrable : Integrable (fun marks => Real.exp (first marks - max 1 (parameter / 2) * second marks))
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    convert firstMemLp.integrable_mul secondMemLp using 1
    funext marks
    simp only [Pi.mul_apply, ← Real.exp_add]
    congr 1
    ring
  refine ⟨pairedIntegrable, ?_⟩
  have firstRealBound : (∫ marks, Real.exp (2 * first marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ max 1 bound :=
    integral_le_of_lintegral_ofReal_le _ _ firstDoubleIntegrable.aestronglyMeasurable
      (Eventually.of_forall (fun marks => Real.exp_nonneg (2 * first marks))) boundPositive.le firstDoubleBound
  have coefficientBound : parameter ≤ 2 * max 1 (parameter / 2) := by linarith [le_max_right 1 (parameter / 2)]
  have secondDoubleBound : (∫⁻ marks, ENNReal.ofReal (Real.exp (-2 * max 1 (parameter / 2) * second marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ENNReal.ofReal ((ratio / Real.sqrt (max 1 bound)) ^ 2) := by
    refine (lintegral_mono_ae ?_).trans (laplaceValid second secondMembership)
    filter_upwards [secondNonnegative] with marks nonnegative
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right coefficientBound nonnegative]
  have secondRealBound : (∫ marks, Real.exp (-2 * max 1 (parameter / 2) * second marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ (ratio / Real.sqrt (max 1 bound)) ^ 2 :=
    integral_le_of_lintegral_ofReal_le _ _ ((Lp.stronglyMeasurable second).measurable.const_mul (-2 * max 1 (parameter / 2))).exp.aestronglyMeasurable
      (Eventually.of_forall (fun marks => Real.exp_nonneg (-2 * max 1 (parameter / 2) * second marks)))
      targetPositive.le secondDoubleBound
  have comparison := measure_paired_exponential_le (independentInnovationLaw rule p positive lessOne fixedPoint)
    first second 1 (max 1 (parameter / 2)) (by simpa only [one_mul] using firstMemLp)
    (by simpa only [neg_one_mul] using secondMemLp)
  simp only [one_mul, mul_one] at comparison
  have sqrtBound := mul_le_mul (Real.sqrt_le_sqrt firstRealBound) (Real.sqrt_le_sqrt secondRealBound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have identity : Real.sqrt (max 1 bound) * Real.sqrt ((ratio / Real.sqrt (max 1 bound)) ^ 2) = ratio := by
    rw [Real.sqrt_sq (div_nonneg ratioPositive.le sqrtPositive.le)]
    field_simp
  exact comparison.trans (sqrtBound.trans_eq identity)

end
end IGSIII.Chemical.SmallBall
