import IGSIII.Chemical.SmallBall.ChemicalInvariantGapLaplace
import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier
import IGSIII.Chemical.SmallBall.PairedUniformBarrier
import IGSIII.Chemical.ChemicalOmega
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Set IGSIII.Probability Filter
open scoped ENNReal Topology

noncomputable section

theorem normalizedChemicalTransferLp_iterate_gap_le (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (upper value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth upper = upper)
    (depth : ℕ) :
    (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth] (upper - value) ≤
      upper - (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth] value := by
  induction depth with
  | zero => exact le_rfl
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (normalizedChemicalTransferLp_monotone rule p positive lessOne fixedPoint 2 growth growthNonnegative inductionHypothesis).trans
        (normalizedChemicalTransferLp_gap_le_successor_gap rule p positive lessOne fixedPoint growth growthNonnegative upper _ upperFixed)

theorem exists_uniform_invariant_gap_unit_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (family : Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)))
    (compact : IsCompact family) (familyNonnegative : ∀ value ∈ family, 0 ≤ value)
    (mapsTo : Set.MapsTo (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (onto : Set.SurjOn (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth) family family)
    (upper : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth upper = upper)
    (upperBound : ∀ value ∈ family, value ≤ upper) (absent : upper ∉ family)
    {ratio : ℝ} (ratioPositive : 0 < ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) :
    ∃ scale : ℝ, 1 ≤ scale ∧ ∀ value ∈ family, ∀ depth : ℕ,
      (independentInnovationLaw rule p positive lessOne fixedPoint).real
        {marks | scale * (upper - value) marks < chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1) marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  have targetPositive : 0 < ratio / Real.exp 1 := div_pos ratioPositive (Real.exp_pos _)
  obtain ⟨parameter, parameterPositive, laplace⟩ := exists_uniform_invariant_gap_laplace rule classical
    p positive lessOne fixedPoint growth growthPositive family compact familyNonnegative mapsTo onto upper upperFixed upperBound absent targetPositive
  refine ⟨max 1 parameter, le_max_left _ _, fun value membership depth => ?_⟩
  obtain ⟨preimage, preimageMembership, preimageEquality⟩ := onto.iterate (depth + 1) membership
  have gapNonnegative : 0 ≤ upper - preimage := sub_nonneg.mpr (upperBound preimage preimageMembership)
  have gapNonnegativeAe := (Lp.coeFn_nonneg (upper - preimage)).mpr gapNonnegative
  have laplaceIntegrable (coefficient : ℝ) (coefficientNonnegative : 0 ≤ coefficient) :
      Integrable (fun marks => Real.exp (-coefficient * (upper - preimage) marks))
        (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    apply (integrable_const (1 : ℝ)).mono'
      (((Lp.stronglyMeasurable (upper - preimage)).measurable.const_mul (-coefficient)).exp.aestronglyMeasurable)
    filter_upwards [gapNonnegativeAe] with marks nonnegative
    change 0 ≤ (upper - preimage) marks at nonnegative
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr coefficientNonnegative) nonnegative)
  have pairedIntegrable : Integrable (fun marks => Real.exp
      (chemicalUnitLp rule p positive lessOne fixedPoint 2 marks - max 1 parameter * (upper - preimage) marks))
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
    apply (integrable_const (Real.exp 1)).mono'
      (((Lp.stronglyMeasurable (chemicalUnitLp rule p positive lessOne fixedPoint 2)).measurable.sub
        ((Lp.stronglyMeasurable (upper - preimage)).measurable.const_mul (max 1 parameter))).exp.aestronglyMeasurable)
    filter_upwards [chemicalUnitLp_ae rule p positive lessOne fixedPoint 2, gapNonnegativeAe]
      with marks unitEquality nonnegative
    change 0 ≤ (upper - preimage) marks at nonnegative
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change Real.exp (chemicalUnitLp rule p positive lessOne fixedPoint 2 marks -
      max 1 parameter * (upper - preimage) marks) ≤ Real.exp 1
    rw [unitEquality]
    apply Real.exp_le_exp.mpr
    nlinarith [le_max_left (1 : ℝ) parameter]
  have pairedBound : (∫ marks, Real.exp
      (chemicalUnitLp rule p positive lessOne fixedPoint 2 marks - max 1 parameter * (upper - preimage) marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio := by
    have equality : (fun marks => Real.exp
        (chemicalUnitLp rule p positive lessOne fixedPoint 2 marks - max 1 parameter * (upper - preimage) marks)) =ᵐ[
        independentInnovationLaw rule p positive lessOne fixedPoint]
        fun marks => Real.exp 1 * Real.exp (-max 1 parameter * (upper - preimage) marks) := by
      filter_upwards [chemicalUnitLp_ae rule p positive lessOne fixedPoint 2] with marks unitEquality
      rw [unitEquality, sub_eq_add_neg, Real.exp_add]
      congr 2
      ring
    rw [integral_congr_ae equality, integral_const_mul]
    have bound : (∫ marks, Real.exp (-max 1 parameter * (upper - preimage) marks)
        ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio / Real.exp 1 := by
      apply (integral_mono_ae (laplaceIntegrable (max 1 parameter) (zero_le_one.trans (le_max_left _ _)))
        (laplaceIntegrable parameter parameterPositive.le) ?_).trans (laplace preimage preimageMembership)
      filter_upwards [gapNonnegativeAe] with marks nonnegative
      change 0 ≤ (upper - preimage) marks at nonnegative
      apply Real.exp_le_exp.mpr
      nlinarith [le_max_right (1 : ℝ) parameter]
    exact (mul_le_mul_of_nonneg_left bound (Real.exp_nonneg _)).trans_eq
      (mul_div_cancel₀ ratio (Real.exp_ne_zero _))
  have barrier := chemicalTransfer_iterate_paired_comparison_bound rule classical p positive lessOne fixedPoint
    (chemicalUnitLp rule p positive lessOne fixedPoint 2) (upper - preimage)
    ratioPositive.le pairedIntegrable pairedBound geometricBelowOne depth
  have gapOrder := normalizedChemicalTransferLp_iterate_gap_le rule p positive lessOne fixedPoint
    growth growthPositive.le upper preimage upperFixed (depth + 1)
  rw [preimageEquality] at gapOrder
  have inclusion : {marks | max 1 parameter * (upper - value) marks <
      chemicalOrbit rule p positive lessOne fixedPoint growth (depth + 1) marks} ≤ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      {marks | max 1 parameter * ((chemicalTransfer rule)^[depth + 1] ⇑(upper - preimage)) marks <
        ((chemicalTransfer rule)^[depth + 1] (chemicalUnitLp rule p positive lessOne fixedPoint 2)) marks} := by
    filter_upwards [(Lp.coeFn_le _ _).mpr gapOrder,
      normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthPositive.le
        (upper - preimage) (depth + 1),
      normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthPositive.le
        (chemicalUnitLp rule p positive lessOne fixedPoint 2) (depth + 1)]
      with marks comparison gapEquality unitEquality bad
    change max 1 parameter * ((chemicalTransfer rule)^[depth + 1] ⇑(upper - preimage)) marks <
      ((chemicalTransfer rule)^[depth + 1] (chemicalUnitLp rule p positive lessOne fixedPoint 2)) marks
    change max 1 parameter * (upper - value) marks <
      ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1]
        (chemicalUnitLp rule p positive lessOne fixedPoint 2)) marks at bad
    rw [gapEquality] at comparison
    rw [unitEquality] at bad
    have scaled := (mul_le_mul_of_nonneg_left comparison (zero_le_one.trans (le_max_left _ _))).trans_lt bad
    have scalarPositive : 0 < (growth⁻¹) ^ (depth + 1) := pow_pos (inv_pos.mpr growthPositive) _
    apply (mul_lt_mul_iff_right₀ scalarPositive).mp
    simpa only [mul_left_comm (max 1 parameter) ((growth⁻¹) ^ (depth + 1))] using scaled
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae inclusion)).trans barrier

end
end IGSIII.Chemical.SmallBall
