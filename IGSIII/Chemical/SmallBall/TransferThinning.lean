import IGSIII.Chemical.SmallBall.MeasureThinning
import IGSIII.Chemical.SmallBall.FiniteDepthSmallBall
import IGSIII.Chemical.TransferOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Set IGSIII.Probability
open scoped BigOperators ENNReal

noncomputable section

theorem chemicalTransfer_smallBall_le_thinning (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (nonnegative : 0 ≤ value) (threshold : ℝ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | chemicalTransfer rule value marks ≤ threshold} ≤
      thinningMap rule.network p
        ((independentInnovationLaw rule p positive lessOne fixedPoint).real {marks | value marks ≤ threshold}) := by
  classical
  have retentionMeasurable : Measurable (fun marks => decide (value marks ≤ threshold)) := by
    have smallEvent : MeasurableSet {marks | value marks ≤ threshold} :=
      measurableSet_le (Lp.stronglyMeasurable value).measurable measurable_const
    have measurableIf : Measurable (fun marks => if value marks ≤ threshold then true else false) :=
      Measurable.ite smallEvent measurable_const measurable_const
    have equality : (fun marks => decide (value marks ≤ threshold)) =
        (fun marks => if value marks ≤ threshold then true else false) := by
      funext marks
      by_cases small : value marks ≤ threshold <;> simp [small]
    rw [equality]
    exact measurableIf
  have coordinateNonnegative : ∀ edge : Fin rule.edges,
      ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
        0 ≤ value (innovationTreeShift rule [edge] marks) := fun edge =>
    (innovationTreeShift_preserving rule p positive lessOne fixedPoint [edge]).quasiMeasurePreserving.ae
      ((Lp.coeFn_nonneg value).mpr nonnegative)
  have inclusion : {marks | chemicalTransfer rule value marks ≤ threshold} ≤ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      {marks | rule.network.crosses (fun edge => marks ([], true) edge &&
        decide (value (innovationTreeShift rule [edge] marks) ≤ threshold)) = true} := by
    filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint,
      ae_all_iff.mpr coordinateNonnegative] with marks crossing childNonnegative small
    exact small_shortest_crosses_retained_configuration rule.network classical.simple _ (crossing [] true)
      (fun edge => value (innovationTreeShift rule [edge] marks)) childNonnegative small
  have bound := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae inclusion)
  have thinning := actual_tree_retention_crossing_probability rule p positive lessOne fixedPoint
      (fun marks => decide (value marks ≤ threshold)) retentionMeasurable
  exact bound.trans_eq (by simpa only [measureReal_def, decide_eq_true_eq] using thinning)

theorem normalizedChemicalTransferLp_smallBall_le_thinning (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (nonnegative : 0 ≤ value) (threshold : ℝ) :
    (independentInnovationLaw rule p positive lessOne fixedPoint).real
      {marks | normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth value marks ≤ threshold} ≤
      thinningMap rule.network p
        ((independentInnovationLaw rule p positive lessOne fixedPoint).real {marks | value marks ≤ growth * threshold}) := by
  have equality : {marks | normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth value marks ≤ threshold} =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
      {marks | chemicalTransfer rule value marks ≤ growth * threshold} := by
    filter_upwards [normalizedChemicalTransferLp_iterate_value_ae rule p positive lessOne fixedPoint
      2 growth growthPositive.le value 1] with marks representative
    simp only [Function.iterate_one, pow_one] at representative
    apply propext
    change normalizedChemicalTransferLp rule p positive lessOne fixedPoint 2 growth value marks ≤ threshold ↔
      chemicalTransfer rule value marks ≤ growth * threshold
    rw [representative]
    rw [inv_mul_le_iff₀ growthPositive]
  rw [measureReal_congr equality]
  exact chemicalTransfer_smallBall_le_thinning rule classical p positive lessOne fixedPoint value nonnegative _

end
end IGSIII.Chemical.SmallBall
