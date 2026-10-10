import IGSIII.Chemical.TransferNormalization
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Order.Iterate

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open scoped ENNReal

theorem chemicalTransferLp_monotone (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) :
    Monotone (chemicalTransferLp rule p positive belowOne fixedPoint order) := by
  intro first second comparison
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint order first,
    chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint order second,
    chemicalTransfer_mono_ae rule p positive belowOne fixedPoint ((Lp.coeFn_le first second).mpr comparison)]
    with marks firstEquality secondEquality inequality
  simpa only [firstEquality, secondEquality] using inequality

theorem normalizedChemicalTransferLp_monotone (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) :
    Monotone (normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth) := by
  intro first second comparison
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [Lp.coeFn_smul growth⁻¹ (chemicalTransferLp rule p positive belowOne fixedPoint order first),
    Lp.coeFn_smul growth⁻¹ (chemicalTransferLp rule p positive belowOne fixedPoint order second),
    (Lp.coeFn_le _ _).mpr (chemicalTransferLp_monotone rule p positive belowOne fixedPoint order comparison)]
    with marks firstEquality secondEquality inequality
  change (growth⁻¹ • chemicalTransferLp rule p positive belowOne fixedPoint order first) marks ≤
    (growth⁻¹ • chemicalTransferLp rule p positive belowOne fixedPoint order second) marks
  rw [firstEquality, secondEquality, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left inequality (inv_nonneg.mpr growthNonnegative)

theorem normalizedChemicalTransferLp_smul (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth (scalar • value) =
      scalar • normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth value := by
  unfold normalizedChemicalTransferLp
  rw [chemicalTransferLp_smul rule p positive belowOne fixedPoint order value scalar scalarNonnegative,
    smul_smul, smul_smul, mul_comm growth⁻¹ scalar]

theorem normalizedChemicalTransferLp_zero (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (growth : ℝ) :
    normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth 0 = 0 := by
  simpa only [zero_smul] using normalizedChemicalTransferLp_smul rule p positive belowOne fixedPoint
    order growth 0 (le_refl 0) (chemicalUnitLp rule p positive belowOne fixedPoint order)

end IGSIII.Chemical.Substitution
