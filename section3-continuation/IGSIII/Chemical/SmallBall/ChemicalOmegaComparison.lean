import IGSIII.Chemical.SmallBall.ChemicalOmegaPairedMarginals
import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier
import IGSIII.Chemical.SmallBall.PairedBarrierLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Filter Set
open scoped ENNReal Topology

noncomputable section

theorem chemicalOmega_pairwise_comparison_of_paired_barrier (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {scale ratio : ℝ} (ratioNonnegative : 0 ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1)
    (paired : ∀ first ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      ∀ second ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
        Integrable (fun marks => Real.exp (first marks - scale * second marks))
          (independentInnovationLaw rule p positive lessOne fixedPoint) ∧
        (∫ marks, Real.exp (first marks - scale * second marks)
          ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (firstMembership : first ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth)
    (secondMembership : second ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      first marks ≤ scale * second marks := by
  have onto := (chemicalOmegaSet_properties rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds).2.2.2
  have bound (depth : ℕ) : (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * second marks < first marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
    obtain ⟨firstPreimage, firstPreimageMembership, firstPreimageEquality⟩ := onto.iterate (depth + 1) firstMembership
    obtain ⟨secondPreimage, secondPreimageMembership, secondPreimageEquality⟩ := onto.iterate (depth + 1) secondMembership
    have firstValue := normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint
      2 growth growthPositive.le firstPreimage (depth + 1)
    have secondValue := normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint
      2 growth growthPositive.le secondPreimage (depth + 1)
    rw [firstPreimageEquality] at firstValue
    rw [secondPreimageEquality] at secondValue
    have eventEquality : {marks | scale * second marks < first marks} =ᵐ[
        independentInnovationLaw rule p positive lessOne fixedPoint]
        {marks | scale * ((chemicalTransfer rule)^[depth + 1] secondPreimage) marks <
          ((chemicalTransfer rule)^[depth + 1] firstPreimage) marks} := by
      filter_upwards [firstValue, secondValue] with marks firstEquality secondEquality
      apply propext
      change (scale * second marks < first marks) ↔
        (scale * ((chemicalTransfer rule)^[depth + 1] secondPreimage) marks <
          ((chemicalTransfer rule)^[depth + 1] firstPreimage) marks)
      rw [firstEquality, secondEquality]
      simpa only [mul_left_comm scale ((growth⁻¹) ^ (depth + 1))] using
        (mul_lt_mul_iff_right₀ (pow_pos (inv_pos.mpr growthPositive) (depth + 1)) :
          ((growth⁻¹) ^ (depth + 1)) *
              (scale * ((chemicalTransfer rule)^[depth + 1] secondPreimage) marks) <
            ((growth⁻¹) ^ (depth + 1)) * ((chemicalTransfer rule)^[depth + 1] firstPreimage) marks ↔ _)
    rw [measureReal_congr eventEquality]
    exact chemicalTransfer_iterate_paired_comparison_bound rule classical p positive lessOne fixedPoint
      firstPreimage secondPreimage ratioNonnegative
      (paired firstPreimage firstPreimageMembership secondPreimage secondPreimageMembership).1
      (paired firstPreimage firstPreimageMembership secondPreimage secondPreimageMembership).2 geometricBelowOne depth
  have summable := (geometric_power_geometric_summable classical.scale
    (mul_nonneg (Nat.cast_nonneg _) ratioNonnegative) geometricBelowOne).div_const
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio)
  have errorTendstoZero := ((summable_nat_add_iff 1).mpr summable).tendsto_atTop_zero
  have zeroReal : (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * second marks < first marks} = 0 :=
    le_antisymm (ge_of_tendsto' errorTendstoZero bound) measureReal_nonneg
  have zeroMeasure := (measureReal_eq_zero_iff).mp zeroReal
  simpa only [ae_iff, not_le] using zeroMeasure

theorem exists_uniform_chemicalOmega_pairwise_comparison (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    ∃ scale : ℝ, 1 ≤ scale ∧
      ∀ first ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
      ∀ second ∈ chemicalOmegaSet rule p positive lessOne fixedPoint growth,
        ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
          first marks ≤ scale * second marks := by
  have countPositive : (0 : ℝ) < (((rule.edges + 3) ^ 4 : ℕ) : ℝ) := by positivity
  have ratioPositive : 0 < (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨scale, scaleAtLeastOne, paired⟩ := exists_uniform_chemicalOmega_paired_exponential_barrier
    rule classical p positive lessOne fixedPoint constant growth constantPositive growthPositive meanBounds ratioPositive
  refine ⟨scale, scaleAtLeastOne, fun first firstMembership second secondMembership => ?_⟩
  apply chemicalOmega_pairwise_comparison_of_paired_barrier rule classical p positive lessOne fixedPoint
    constant growth growthPositive meanBounds ratioPositive.le _ paired first second firstMembership secondMembership
  have identity : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) *
      (2 * (((rule.edges + 3) ^ 4 : ℕ) : ℝ))⁻¹ = 1 / 2 := by
    field_simp
  rw [identity]
  norm_num

end
end IGSIII.Chemical.SmallBall
