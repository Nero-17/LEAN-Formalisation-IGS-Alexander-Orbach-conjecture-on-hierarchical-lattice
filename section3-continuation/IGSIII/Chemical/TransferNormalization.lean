import IGSIII.Chemical.TransferContinuity
import IGSIII.Chemical.TransferIteration
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability
open scoped ENNReal

noncomputable def chemicalUnitLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  (memLp_const (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
    (p := order) (1 : ℝ)).toLp (fun _ => 1)

theorem chemicalUnitLp_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) :
    ⇑(chemicalUnitLp rule p positive belowOne fixedPoint order) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] (fun _ => 1) :=
  MemLp.coeFn_toLp _

theorem chemicalTransferLp_smul (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint))
    (scalar : ℝ) (nonnegative : 0 ≤ scalar) :
    chemicalTransferLp rule p positive belowOne fixedPoint order (scalar • value) =
      scalar • chemicalTransferLp rule p positive belowOne fixedPoint order value := by
  have congruent := chemicalTransfer_congr_ae rule p positive belowOne fixedPoint
    (Lp.coeFn_smul scalar value)
  apply Lp.ext
  filter_upwards [chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint order (scalar • value),
    Lp.coeFn_smul scalar (chemicalTransferLp rule p positive belowOne fixedPoint order value),
    chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint order value, congruent]
    with marks firstEqual scalarEqual secondEqual transferEqual
  rw [firstEqual, transferEqual, scalarEqual, Pi.smul_apply, smul_eq_mul, secondEqual]
  change chemicalTransfer rule (fun sample => scalar * value sample) marks = scalar * chemicalTransfer rule value marks
  exact congrFun (chemicalTransfer_scale rule value nonnegative) marks

theorem chemicalTransferLp_iterate_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) (depth : ℕ) :
    ⇑((chemicalTransferLp rule p positive belowOne fixedPoint order)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      (chemicalTransfer rule)^[depth] (fun _ => 1) := by
  induction depth with
  | zero => exact chemicalUnitLp_ae rule p positive belowOne fixedPoint order
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (chemicalTransferLp_coe_ae rule p positive belowOne fixedPoint order _).trans
      (chemicalTransfer_congr_ae rule p positive belowOne fixedPoint inductionHypothesis)

noncomputable def normalizedChemicalTransferLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) (order : ℝ≥0∞) (growth : ℝ)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  growth⁻¹ • chemicalTransferLp rule p positive belowOne fixedPoint order value

theorem normalizedChemicalTransferLp_continuous (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) [Fact (1 ≤ order)] (growth : ℝ) :
    Continuous (normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth) := by
  unfold normalizedChemicalTransferLp
  exact (continuous_const : Continuous (fun _ : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) => (growth⁻¹ : ℝ))).smul (chemicalTransferLp_lipschitz rule p positive belowOne fixedPoint order).continuous

theorem normalizedChemicalTransferLp_iterate (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) (depth : ℕ) :
    (normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth)^[depth] value =
      (growth⁻¹) ^ depth • (chemicalTransferLp rule p positive belowOne fixedPoint order)^[depth] value := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', inductionHypothesis, normalizedChemicalTransferLp,
      chemicalTransferLp_smul rule p positive belowOne fixedPoint order _ _
        (pow_nonneg (inv_nonneg.mpr growthNonnegative) depth), smul_smul,
      Function.iterate_succ_apply', pow_succ]
    congr 1
    ring

theorem normalizedChemicalTransferLp_iterate_ae (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    ⇑((normalizedChemicalTransferLp rule p positive belowOne fixedPoint order growth)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => (growth⁻¹) ^ depth * ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks := by
  rw [normalizedChemicalTransferLp_iterate rule p positive belowOne fixedPoint order growth growthNonnegative]
  filter_upwards [Lp.coeFn_smul ((growth⁻¹) ^ depth)
    ((chemicalTransferLp rule p positive belowOne fixedPoint order)^[depth]
      (chemicalUnitLp rule p positive belowOne fixedPoint order)),
    chemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint order depth] with marks scalarEqual iterateEqual
  simp only [scalarEqual, Pi.smul_apply, smul_eq_mul, iterateEqual]

end IGSIII.Chemical.Substitution

