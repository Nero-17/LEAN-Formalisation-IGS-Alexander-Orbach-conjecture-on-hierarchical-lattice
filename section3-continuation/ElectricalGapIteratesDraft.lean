import IGSIII34.Percolation.ElectricalTransferBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem normalizedElectricalTransferLp_iterate_below_fixed (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (upper value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueNonnegative : 0 ≤ value) (valueUpper : value ≤ upper)
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper) (depth : ℕ) :
    0 ≤ (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth] value ∧
      (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth] value ≤ upper := by
  induction depth with
  | zero => exact ⟨valueNonnegative, valueUpper⟩
  | succ depth previous =>
      rw [Function.iterate_succ_apply']
      exact ⟨normalizedElectricalTransferLp_nonnegative rule p positive belowOne fixedPoint growth growthNonnegative _,
        (normalizedElectricalTransferLp_monotone rule p positive belowOne fixedPoint 2 growth growthNonnegative previous.2).trans_eq upperFixed⟩

theorem normalizedElectricalTransferLp_iterate_gap_le (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (upper value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueNonnegative : 0 ≤ value) (valueUpper : value ≤ upper)
    (upperFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth upper = upper) (depth : ℕ) :
    (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth] (upper - value) ≤
      upper - (normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth] value := by
  induction depth with
  | zero => exact le_rfl
  | succ depth previous =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have bounds := normalizedElectricalTransferLp_iterate_below_fixed rule p positive belowOne fixedPoint
        growth growthNonnegative upper value valueNonnegative valueUpper upperFixed depth
      exact (normalizedElectricalTransferLp_monotone rule p positive belowOne fixedPoint 2 growth growthNonnegative previous).trans
        (normalizedElectricalTransferLp_gap_le_successor_gap rule p positive belowOne fixedPoint
          growth growthNonnegative upper _ bounds.1 bounds.2 upperFixed)

end
end IGSIII34.Percolation
