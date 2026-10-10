import IGSIII.Chemical.SmallBall.TransferValue
import IGSIII.Chemical.TransferOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution
open scoped ENNReal

theorem normalizedChemicalTransferLp_superadditive (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (first second : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :
    normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth first +
      normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth second ≤
      normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth (first + second) := by
  have congruent := chemicalTransfer_congr_ae rule p positive lessOne fixedPoint (Lp.coeFn_add first second)
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [Lp.coeFn_add
      (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth first)
      (normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth second),
    normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthNonnegative first 1,
    normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthNonnegative second 1,
    normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint 2 growth growthNonnegative (first + second) 1,
    congruent] with marks addEquality firstEquality secondEquality sumEquality transferEquality
  simp only [Function.iterate_one, pow_one] at firstEquality secondEquality sumEquality
  rw [addEquality, Pi.add_apply, firstEquality, secondEquality, sumEquality, transferEquality]
  calc
    growth⁻¹ * chemicalTransfer rule first marks + growth⁻¹ * chemicalTransfer rule second marks =
      growth⁻¹ * (chemicalTransfer rule first marks + chemicalTransfer rule second marks) := by ring
    _ ≤ growth⁻¹ * chemicalTransfer rule (⇑first + ⇑second) marks :=
      mul_le_mul_of_nonneg_left (chemicalTransfer_superadditive rule first second marks) (inv_nonneg.mpr growthNonnegative)

theorem normalizedChemicalTransferLp_gap_le_successor_gap (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (upper value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (upperFixed : normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth upper = upper) :
    normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth (upper - value) ≤
      upper - normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth value := by
  apply le_sub_iff_add_le.mpr
  have bound := normalizedChemicalTransferLp_superadditive rule p positive lessOne fixedPoint
    growth growthNonnegative (upper - value) value
  simpa only [sub_add_cancel, upperFixed] using bound

end IGSIII.Chemical.SmallBall
