import IGSIII.Chemical.TransferNormalization

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Universality MeasureTheory Substitution
open scoped ENNReal

theorem chemicalTransferLp_iterate_value_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (value : Lp ℝ order (independentInnovationLaw rule p positive lessOne fixedPoint)) (depth : ℕ) :
    ⇑((chemicalTransferLp rule p positive lessOne fixedPoint order)^[depth] value) =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint] (chemicalTransfer rule)^[depth] value := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (chemicalTransferLp_coe_ae rule p positive lessOne fixedPoint order _).trans
        (chemicalTransfer_congr_ae rule p positive lessOne fixedPoint inductionHypothesis)

theorem normalizedChemicalTransferLp_iterate_value_ae (rule : Rule) (p : ℝ)
    (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ order (independentInnovationLaw rule p positive lessOne fixedPoint)) (depth : ℕ) :
    ⇑((normalizedChemicalTransferLp rule p positive lessOne fixedPoint order growth)^[depth] value) =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      fun marks => (growth⁻¹) ^ depth * ((chemicalTransfer rule)^[depth] value) marks := by
  rw [normalizedChemicalTransferLp_iterate rule p positive lessOne fixedPoint order growth growthNonnegative]
  filter_upwards [Lp.coeFn_smul ((growth⁻¹) ^ depth)
      ((chemicalTransferLp rule p positive lessOne fixedPoint order)^[depth] value),
    chemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint order value depth]
      with marks scalarEquality transferEquality
  simp only [scalarEquality, Pi.smul_apply, smul_eq_mul, transferEquality]

end IGSIII.Chemical.SmallBall
