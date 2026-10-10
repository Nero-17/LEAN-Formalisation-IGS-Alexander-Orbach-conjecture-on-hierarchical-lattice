import IGSIII4.TransferAlgebra

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation

theorem electricalTransfer_monotone_ae (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      0 ≤ first marks)
    (comparison : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      first marks ≤ second marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule first marks ≤ electricalTransfer rule second marks := by
  have childrenNonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, 0 ≤ first (innovationTreeShift rule [edge] marks) := by
    apply ae_all_iff.mpr
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae nonnegative
  have childrenComparison : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, first (innovationTreeShift rule [edge] marks) ≤ second (innovationTreeShift rule [edge] marks) := by
    apply ae_all_iff.mpr
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae comparison
  filter_upwards [childrenNonnegative, childrenComparison] with marks nonnegative comparison
  exact electricalCell_monotone rule.network (marks ([], true)) nonnegative comparison

theorem electricalTransfer_iterate_nonnegative (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (nonnegative : ∀ marks, 0 ≤ value marks) (depth : ℕ) :
    ∀ marks, 0 ≤ (electricalTransfer rule)^[depth] value marks := by
  induction depth with
  | zero => exact nonnegative
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact electricalTransfer_nonnegative rule _ inductionHypothesis

theorem electricalTransfer_iterate_measurable (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value) (nonnegative : ∀ marks, 0 ≤ value marks) (depth : ℕ) :
    Measurable ((electricalTransfer rule)^[depth] value) := by
  induction depth with
  | zero => exact measurable
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact electricalTransfer_measurable rule _ inductionHypothesis
        (electricalTransfer_iterate_nonnegative rule value nonnegative depth)

theorem electricalTransfer_iterate_integrable (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value) (nonnegative : ∀ marks, 0 ≤ value marks)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (depth : ℕ) :
    Integrable ((electricalTransfer rule)^[depth] value)
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
  induction depth with
  | zero => exact integrable
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact electricalTransfer_integrable rule probability positive belowOne fixedPoint _
        (electricalTransfer_iterate_measurable rule value measurable nonnegative depth)
        (electricalTransfer_iterate_nonnegative rule value nonnegative depth) inductionHypothesis

theorem supersolution_iterate_bound (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (nonnegative : ∀ marks, 0 ≤ value marks) {factor : ℝ} (factorNonnegative : 0 ≤ factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ factor * value marks) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      (electricalTransfer rule)^[depth] value marks ≤ factor ^ depth * value marks := by
  induction depth with
  | zero => exact Filter.Eventually.of_forall (fun _ => by simp)
  | succ depth inductionHypothesis =>
      have iteratedComparison := electricalTransfer_monotone_ae rule probability positive belowOne fixedPoint
        (Filter.Eventually.of_forall (electricalTransfer_iterate_nonnegative rule value nonnegative depth))
        inductionHypothesis
      have scaling := electricalTransfer_scale_ae rule probability positive belowOne fixedPoint
        (Filter.Eventually.of_forall nonnegative) (pow_nonneg factorNonnegative depth)
      filter_upwards [iteratedComparison, scaling, supersolution] with marks comparison scale bound
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ electricalTransfer rule (fun marks => factor ^ depth * value marks) marks := comparison
        _ = factor ^ depth * electricalTransfer rule value marks := scale
        _ ≤ factor ^ depth * (factor * value marks) :=
          mul_le_mul_of_nonneg_left bound (pow_nonneg factorNonnegative depth)
        _ = _ := by rw [pow_succ]; ring

end
end IGSIII4
