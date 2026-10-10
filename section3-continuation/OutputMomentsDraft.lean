import IGSIII34.Percolation.LawMap
import IGSIII34.Probability.MeanContinuity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Resistance.FiniteNetwork
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal

theorem electricalCellNNReal_secondMoment_bound {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ≥0) :
    electricalCellNNReal rule configuration input ^ 2 ≤
      (edges : ℝ≥0) * ∑ edge, input edge ^ 2 := by
  have pathBound : electricalCellNNReal rule configuration input ≤ ∑ edge, input edge := by
    apply NNReal.coe_le_coe.mp
    change electricalCell rule configuration (fun edge => (input edge : ℝ)) ≤
      ((∑ edge, input edge : ℝ≥0) : ℝ)
    convert electricalCell_le_sum rule configuration (fun edge => (input edge).2) using 1
    congr 1
    exact NNReal.coe_sum Finset.univ input
  have sumBound : (∑ edge, input edge) ^ 2 ≤ (edges : ℝ≥0) * ∑ edge, input edge ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ≥0) Finset.univ (fun _ : Fin edges => 1) input
  exact (pow_le_pow_left' pathBound 2).trans sumBound

theorem electricalInputLaw_coordinate_preserving (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (edge : Fin rule.edges) :
    MeasurePreserving (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) => data.2 edge)
      (electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _)
      (law : Measure ℝ≥0) :=
  (measurePreserving_eval (fun _ : Fin rule.edges => (law : Measure ℝ≥0)) edge).comp measurePreserving_snd

theorem electricalOutputLaw_secondMoment_le (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) :
    (∫⁻ value, (value : ℝ≥0∞) ^ 2
      ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) ≤
      (rule.edges : ℝ≥0∞) ^ 2 * (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) := by
  change (∫⁻ value, (value : ℝ≥0∞) ^ 2
    ∂((electricalInputLaw rule parameter positive belowOne fixedPoint law :
      Measure (Configuration rule.edges × (Fin rule.edges → ℝ≥0))).map
        (fun data : Configuration rule.edges × (Fin rule.edges → ℝ≥0) =>
          electricalCellNNReal rule.network data.1 data.2))) ≤ _
  rw [lintegral_map (f := fun value : ℝ≥0 => (value : ℝ≥0∞) ^ 2)
    (measurable_id.coe_nnreal_ennreal.pow_const 2)
    (electricalCellNNReal_joint_continuous rule.network).measurable]
  calc
    _ ≤ ∫⁻ data : Configuration rule.edges × (Fin rule.edges → ℝ≥0),
        (rule.edges : ℝ≥0∞) * ∑ edge, (data.2 edge : ℝ≥0∞) ^ 2
        ∂(electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _) := by
      apply lintegral_mono
      intro data
      convert ENNReal.coe_le_coe.mpr
        (electricalCellNNReal_secondMoment_bound rule.network data.1 data.2) using 1 <;> norm_cast
    _ = (rule.edges : ℝ≥0∞) * ∑ edge : Fin rule.edges,
        ∫⁻ data : Configuration rule.edges × (Fin rule.edges → ℝ≥0),
          (data.2 edge : ℝ≥0∞) ^ 2
          ∂(electricalInputLaw rule parameter positive belowOne fixedPoint law : Measure _) := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top rule.edges)]
      rw [lintegral_finsetSum]
      intro edge _
      exact ((measurable_pi_apply edge).comp measurable_snd).coe_nnreal_ennreal.pow_const 2
    _ = (rule.edges : ℝ≥0∞) * ∑ _edge : Fin rule.edges,
        ∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro edge _
      exact (electricalInputLaw_coordinate_preserving rule parameter positive belowOne fixedPoint law edge).lintegral_comp
        (measurable_id.coe_nnreal_ennreal.pow_const 2)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem electricalOutputLaw_secondMoment_bound (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) (bound : ℝ≥0)
    (momentBound : (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ bound) :
    (∫⁻ value, (value : ℝ≥0∞) ^ 2
      ∂(electricalOutputLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)) ≤
        (rule.edges : ℝ≥0) ^ 2 * bound := by
  exact (electricalOutputLaw_secondMoment_le rule parameter positive belowOne fixedPoint law).trans
    (by
      convert mul_le_mul_right momentBound ((rule.edges : ℝ≥0∞) ^ 2) using 1 <;> norm_cast)

end
end IGSIII34.Percolation
