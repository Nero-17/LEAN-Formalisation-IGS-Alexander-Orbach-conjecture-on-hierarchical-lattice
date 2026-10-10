import IGSIII.Chemical.SmallBall.ChemicalTransferPairedBarrier
import IGSIII.Chemical.TransferOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution Set
open scoped ENNReal

noncomputable section

theorem normalizedChemicalTransferLp_iterate_smul (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) (depth : ℕ) :
    (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth] (scalar • value) =
      scalar • (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth] value := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis,
        normalizedChemicalTransferLp_smul rule p positive lessOne fixedPoint 2 growth scalar scalarNonnegative,
        Function.iterate_succ_apply']

theorem normalizedChemicalTransferLp_iterate_paired_comparison_bound (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    {scale ratio : ℝ} (ratioNonnegative : 0 ≤ ratio)
    (pairedIntegrable : Integrable (fun marks => Real.exp (first marks - scale * second marks))
      (independentInnovationLaw rule p positive lessOne fixedPoint))
    (pairedBound : (∫ marks, Real.exp (first marks - scale * second marks)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks <
        ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  have equality : {marks | scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks <
        ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks} =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      {marks | scale * ((chemicalTransfer rule)^[depth + 1] second) marks < ((chemicalTransfer rule)^[depth + 1] first) marks} := by
    filter_upwards [normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthPositive.le first (depth + 1),
      normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthPositive.le second (depth + 1)]
      with marks firstEquality secondEquality
    apply propext
    change (scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks <
      ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks) ↔
      (scale * ((chemicalTransfer rule)^[depth + 1] second) marks < ((chemicalTransfer rule)^[depth + 1] first) marks)
    rw [firstEquality, secondEquality]
    simpa only [mul_left_comm scale ((growth⁻¹) ^ (depth + 1))] using
      (mul_lt_mul_iff_right₀ (pow_pos (inv_pos.mpr growthPositive) (depth + 1)) :
        ((growth⁻¹) ^ (depth + 1)) * (scale * ((chemicalTransfer rule)^[depth + 1] second) marks) <
          ((growth⁻¹) ^ (depth + 1)) * ((chemicalTransfer rule)^[depth + 1] first) marks ↔ _)
  rw [measureReal_congr equality]
  exact chemicalTransfer_iterate_paired_comparison_bound rule classical p positive lessOne fixedPoint
    first second ratioNonnegative pairedIntegrable pairedBound geometricBelowOne depth

theorem normalizedChemicalTransferLp_iterate_paired_comparison_bound_parameter (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    {parameter scale ratio : ℝ} (parameterPositive : 0 < parameter) (ratioNonnegative : 0 ≤ ratio)
    (pairedIntegrable : Integrable (fun marks => Real.exp (parameter * (first marks - scale * second marks)))
      (independentInnovationLaw rule p positive lessOne fixedPoint))
    (pairedBound : (∫ marks, Real.exp (parameter * (first marks - scale * second marks))
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) ≤ ratio)
    (geometricBelowOne : (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio < 1) (depth : ℕ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks <
        ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks} ≤
      ((((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) ^
        (rule.network.fullGraph.dist rule.network.source rule.network.target ^ (depth + 1)) /
      (1 - (((rule.edges + 3) ^ 4 : ℕ) : ℝ) * ratio) := by
  have integrandEquality : (fun marks => Real.exp ((parameter • first) marks - scale * (parameter • second) marks)) =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      fun marks => Real.exp (parameter * (first marks - scale * second marks)) := by
    filter_upwards [Lp.coeFn_smul parameter first, Lp.coeFn_smul parameter second] with marks firstEquality secondEquality
    rw [firstEquality, secondEquality, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    congr 1
    ring
  have bound := normalizedChemicalTransferLp_iterate_paired_comparison_bound rule classical p positive lessOne fixedPoint
    growth growthPositive (parameter • first) (parameter • second) ratioNonnegative
    (pairedIntegrable.congr integrandEquality.symm) (by rwa [integral_congr_ae integrandEquality]) geometricBelowOne depth
  have equality : {marks | scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks <
        ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks} =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      {marks | scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] (parameter • second)) marks <
        ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] (parameter • first)) marks} := by
    rw [normalizedChemicalTransferLp_iterate_smul rule p positive lessOne fixedPoint growth parameter parameterPositive.le,
      normalizedChemicalTransferLp_iterate_smul rule p positive lessOne fixedPoint growth parameter parameterPositive.le]
    filter_upwards [Lp.coeFn_smul parameter
      ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first),
      Lp.coeFn_smul parameter ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second)]
      with marks firstEquality secondEquality
    apply propext
    change (scale * ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks < ((normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks) ↔ (scale * (parameter • (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] second) marks < (parameter • (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth)^[depth + 1] first) marks)
    rw [firstEquality, secondEquality, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    simpa only [mul_left_comm scale parameter] using (mul_lt_mul_iff_right₀ parameterPositive).symm
  rw [measureReal_congr equality]
  exact bound

end
end IGSIII.Chemical.SmallBall
