import IGSIII.Chemical.ChemicalOmega

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory IGSIII.Probability
open scoped ENNReal

theorem chemicalTransfer_unit_iterate_bounds (rule : Rule) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → FiniteNetwork.Configuration rule.edges) :
    0 ≤ ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks ∧
      ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks ≤ (rule.edges : ℝ) ^ depth := by
  induction depth generalizing marks with
  | zero => simp
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply']
    constructor
    · exact (edgePathFamily rule.network (marks ([], true))).shortest_nonneg
        (fun edge => (inductionHypothesis (innovationTreeShift rule [edge] marks)).1)
    · calc
        _ ≤ |chemicalTransfer rule ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks| := le_abs_self _
        _ ≤ ∑ edge : Fin rule.edges,
            |((chemicalTransfer rule)^[depth] (fun _ => 1)) (innovationTreeShift rule [edge] marks)| :=
          (edgePathFamily rule.network (marks ([], true))).shortest_abs_le _
        _ ≤ ∑ _edge : Fin rule.edges, (rule.edges : ℝ) ^ depth := by
          apply Finset.sum_le_sum
          intro edge _
          rw [abs_of_nonneg (inductionHypothesis _).1]
          exact (inductionHypothesis _).2
        _ = (rule.edges : ℝ) ^ (depth + 1) := by simp [pow_succ, mul_comm]

theorem chemicalOrbit_ae_deterministic_bounds (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
      0 ≤ chemicalOrbit rule p positive belowOne fixedPoint growth depth marks ∧
        chemicalOrbit rule p positive belowOne fixedPoint growth depth marks ≤
          ((rule.edges : ℝ) / growth) ^ depth := by
  apply ae_all_iff.mpr
  intro depth
  filter_upwards [normalizedChemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint
    2 growth growthPositive.le depth] with marks equality
  change chemicalOrbit rule p positive belowOne fixedPoint growth depth marks = _ at equality
  rw [equality]
  constructor
  · exact mul_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) _) (chemicalTransfer_unit_iterate_bounds rule depth marks).1
  · calc
      _ ≤ growth⁻¹ ^ depth * (rule.edges : ℝ) ^ depth :=
        mul_le_mul_of_nonneg_left (chemicalTransfer_unit_iterate_bounds rule depth marks).2
          (pow_nonneg (inv_nonneg.mpr growthPositive.le) _)
      _ = _ := by rw [div_pow, inv_pow]; ring

end IGSIII.Chemical.Substitution
