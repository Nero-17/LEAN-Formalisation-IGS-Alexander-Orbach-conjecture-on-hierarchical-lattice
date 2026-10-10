import IGSIII.Chemical.EndogenousMoments
import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

theorem chemicalOrbit_fixed_comparison_probability_bound
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueFixed : normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    {scale ratio : ℝ} (ratioNonnegative : 0 ≤ ratio)
    (pairedIntegrable : Integrable (fun marks => Real.exp
      (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - scale * value marks))
        (independentInnovationLaw rule p positive belowOne fixedPoint))
    (pairedBound : (∫ marks, Real.exp
      (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - scale * value marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) (depth : ℕ) :
    (independentInnovationLaw rule p positive belowOne fixedPoint).real
      {marks | scale * value marks < chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1) marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  have firstValue := normalizedChemicalTransferLp_iterate_value_ae rule p positive belowOne fixedPoint
    2 growth growthPositive.le (chemicalUnitLp rule p positive belowOne fixedPoint 2) (depth + 1)
  have secondValue := normalizedChemicalTransferLp_iterate_value_ae rule p positive belowOne fixedPoint
    2 growth growthPositive.le value (depth + 1)
  rw [Function.iterate_fixed valueFixed] at secondValue
  have eventEquality : {marks | scale * value marks <
      chemicalOrbit rule p positive belowOne fixedPoint growth (depth + 1) marks} =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      {marks | scale * ((chemicalTransfer rule)^[depth + 1] value) marks <
        ((chemicalTransfer rule)^[depth + 1] (chemicalUnitLp rule p positive belowOne fixedPoint 2)) marks} := by
    filter_upwards [firstValue, secondValue] with marks firstEquality secondEquality
    apply propext
    change (scale * value marks <
      ((normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth + 1]
        (chemicalUnitLp rule p positive belowOne fixedPoint 2)) marks) ↔
      (scale * ((chemicalTransfer rule)^[depth + 1] value) marks <
        ((chemicalTransfer rule)^[depth + 1] (chemicalUnitLp rule p positive belowOne fixedPoint 2)) marks)
    rw [firstEquality, secondEquality]
    simpa only [mul_left_comm scale ((growth⁻¹) ^ (depth + 1))] using
      (mul_lt_mul_iff_right₀ (pow_pos (inv_pos.mpr growthPositive) (depth + 1)) :
        ((growth⁻¹) ^ (depth + 1)) * (scale * ((chemicalTransfer rule)^[depth + 1] value) marks) <
          ((growth⁻¹) ^ (depth + 1)) *
            ((chemicalTransfer rule)^[depth + 1] (chemicalUnitLp rule p positive belowOne fixedPoint 2)) marks ↔ _)
  rw [measureReal_congr eventEquality]
  exact chemicalTransfer_iterate_paired_comparison_bound rule classical p positive belowOne fixedPoint
    _ _ ratioNonnegative pairedIntegrable pairedBound geometricBelowOne depth

theorem exists_unit_value_paired_barrier_of_omega_lower_bound
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value base : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (baseMember : base ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (lower : ℝ) (lowerPositive : 0 < lower) (lowerBound : lower • base ≤ value)
    {ratio : ℝ} (ratioPositive : 0 < ratio) :
    ∃ scale : ℝ, 0 < scale ∧
      Integrable (fun marks => Real.exp
        (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - scale * value marks))
          (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∫ marks, Real.exp
        (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - scale * value marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ratio := by
  obtain ⟨parameter, parameterPositive, laplaceBound⟩ := exists_uniform_chemicalOmega_laplace_decay
    rule classical p positive belowOne fixedPoint constant growth growthPositive meanBounds
    (div_pos ratioPositive (Real.exp_pos 1))
  have scalePositive := div_pos parameterPositive lowerPositive
  have lowerAe : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      lower * base marks ≤ value marks := by
    filter_upwards [(Lp.coeFn_le _ _).mpr lowerBound, Lp.coeFn_smul lower base]
      with marks inequality equality
    simpa only [equality, Pi.smul_apply, smul_eq_mul] using inequality
  have pairedIntegrable : Integrable (fun marks => Real.exp
      (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - (parameter / lower) * value marks))
        (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply (integrable_const (Real.exp 1)).mono'
      (((Lp.stronglyMeasurable (chemicalUnitLp rule p positive belowOne fixedPoint 2)).measurable.sub
        ((Lp.stronglyMeasurable value).measurable.const_mul (parameter / lower))).exp.aestronglyMeasurable)
    filter_upwards [chemicalUnitLp_ae rule p positive belowOne fixedPoint 2, valuePositive]
      with marks unitEquality positivity
    change ‖Real.exp (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks -
      (parameter / lower) * value marks)‖ ≤ Real.exp 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), unitEquality]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg scalePositive.le positivity.le
    linarith
  refine ⟨parameter / lower, scalePositive, pairedIntegrable, ?_⟩
  have pairedBound : (∫⁻ marks, ENNReal.ofReal (Real.exp
      (chemicalUnitLp rule p positive belowOne fixedPoint 2 marks - (parameter / lower) * value marks))
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal ratio := by
    calc
      _ ≤ ∫⁻ marks, ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-parameter * base marks))
          ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
        apply lintegral_mono_ae
        filter_upwards [chemicalUnitLp_ae rule p positive belowOne fixedPoint 2, lowerAe]
          with marks unitEquality inequality
        rw [unitEquality, ← ENNReal.ofReal_mul (Real.exp_nonneg 1), ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have scaled := mul_le_mul_of_nonneg_left inequality scalePositive.le
        have cancellation : (parameter / lower) * (lower * base marks) = parameter * base marks := by
          field_simp
        rw [cancellation] at scaled
        linarith
      _ = ENNReal.ofReal (Real.exp 1) *
          (∫⁻ marks, ENNReal.ofReal (Real.exp (-parameter * base marks))
            ∂independentInnovationLaw rule p positive belowOne fixedPoint) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (ratio / Real.exp 1) :=
        mul_le_mul_right (laplaceBound base baseMember) _
      _ = ENNReal.ofReal ratio := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg 1)]
        congr 1
        field_simp
  exact integral_le_of_lintegral_ofReal_le _ _ pairedIntegrable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)) ratioPositive.le pairedBound

end IGSIII.Chemical.Substitution
