import IGSIII34.Percolation.ElectricalContinuity
import IGSIII34.Percolation.ElectricalOrder
import IGSIII.Chemical.TransferNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution
open scoped ENNReal

theorem nonnegativeElectricalTransferLp_iterate_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) (depth : ℕ) :
    ⇑((nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      (nonnegativeElectricalTransfer rule)^[depth] (fun _ => 1) := by
  induction depth with
  | zero => exact chemicalUnitLp_ae rule p positive belowOne fixedPoint order
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order _).trans
      (nonnegativeElectricalTransfer_congr_ae rule p positive belowOne fixedPoint inductionHypothesis)

noncomputable def normalizedElectricalTransferLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) (growth : ℝ)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  growth⁻¹ • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order value

theorem normalizedElectricalTransferLp_continuous (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) [Fact (1 ≤ order)] (growth : ℝ) :
    Continuous (normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth) := by
  unfold normalizedElectricalTransferLp
  exact (continuous_const : Continuous (fun _ : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) => (growth⁻¹ : ℝ))).smul (nonnegativeElectricalTransferLp_lipschitz rule p positive belowOne fixedPoint order).continuous

theorem normalizedElectricalTransferLp_iterate (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) (depth : ℕ) :
    (normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth)^[depth] value =
      (growth⁻¹) ^ depth • (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order)^[depth] value := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', inductionHypothesis, normalizedElectricalTransferLp,
      nonnegativeElectricalTransferLp_smul rule p positive belowOne fixedPoint order _ _
        (pow_nonneg (inv_nonneg.mpr growthNonnegative) depth), smul_smul,
      Function.iterate_succ_apply', pow_succ]
    congr 1
    ring

theorem normalizedElectricalTransferLp_iterate_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    ⇑((normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => (growth⁻¹) ^ depth * ((nonnegativeElectricalTransfer rule)^[depth] (fun _ => 1)) marks := by
  rw [normalizedElectricalTransferLp_iterate rule p positive belowOne fixedPoint order growth growthNonnegative]
  filter_upwards [Lp.coeFn_smul ((growth⁻¹) ^ depth)
    ((nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)),
    nonnegativeElectricalTransferLp_iterate_ae rule p positive belowOne fixedPoint order depth] with marks scalarEqual iterateEqual
  simp only [scalarEqual, Pi.smul_apply, smul_eq_mul, iterateEqual]

theorem normalizedElectricalTransferLp_monotone (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) :
    Monotone (normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth) := by
  intro first second comparison
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [Lp.coeFn_smul growth⁻¹ (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order first),
    Lp.coeFn_smul growth⁻¹ (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order second),
    (Lp.coeFn_le _ _).mpr (nonnegativeElectricalTransferLp_monotone rule p positive belowOne fixedPoint order comparison)]
    with marks firstEquality secondEquality inequality
  change (growth⁻¹ • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order first) marks ≤
    (growth⁻¹ • nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order second) marks
  rw [firstEquality, secondEquality, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left inequality (inv_nonneg.mpr growthNonnegative)

theorem normalizedElectricalTransferLp_smul (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth (scalar • value) =
      scalar • normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth value := by
  unfold normalizedElectricalTransferLp
  rw [nonnegativeElectricalTransferLp_smul rule p positive belowOne fixedPoint order value scalar scalarNonnegative,
    smul_smul, smul_smul, mul_comm growth⁻¹ scalar]

theorem normalizedElectricalTransferLp_zero (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth : ℝ) :
    normalizedElectricalTransferLp rule p positive belowOne fixedPoint order growth 0 = 0 := by
  simpa only [zero_smul] using normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint
    order growth 0 (le_refl 0) (chemicalUnitLp rule p positive belowOne fixedPoint order)

theorem nonnegativeElectricalTransfer_iteration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ) :
    nonnegativeElectricalTransfer rule (fun marks => electricalIteration rule marks depth []) marks =
      electricalIteration rule marks (depth+1) [] := by
  unfold nonnegativeElectricalTransfer
  have clipping : (fun marks => max (electricalIteration rule marks depth []) 0) =
      (fun marks => electricalIteration rule marks depth []) :=
    funext (fun marks => max_eq_left (electricalIteration_nonnegative rule marks depth []))
  rw [clipping]
  exact electricalTransfer_iteration rule marks depth

theorem nonnegativeElectricalTransfer_iterate_actual (rule : Rule) (depth : ℕ) :
    (nonnegativeElectricalTransfer rule)^[depth] (fun _ => 1) =
      (fun marks => electricalIteration rule marks depth []) := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    rw [Function.iterate_succ_apply', previous]
    exact funext (fun marks => nonnegativeElectricalTransfer_iteration rule marks depth)


end
end IGSIII34.Percolation
