import IGSIII4.CorePopulation
import IGSIII4.InnovationRootIntegral
import IGSIII.Probability.IndependentTreeChildren
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability

theorem rootCoreIndicator_integrable (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (edge : Fin rule.edges) :
    Integrable (fun marks => coreEdgeIndicator rule.network (marks ([], true)) edge)
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_of_finite (fun configuration => coreEdgeIndicator rule.network configuration edge)).comp
      (measurable_pi_apply ([], true))).aestronglyMeasurable)
  filter_upwards [] with marks
  change ‖coreEdgeIndicator rule.network (marks ([], true)) edge‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (coreEdgeIndicator_nonnegative _ _ _)]
  exact coreEdgeIndicator_le_one _ _ _

theorem rootCoreIndicators_integral (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) :
    (∑ edge, ∫ marks, coreEdgeIndicator rule.network (marks ([], true)) edge
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) = terminalCoreMean rule.network probability := by
  rw [← integral_finsetSum Finset.univ (fun edge _ => rootCoreIndicator_integrable rule probability positive belowOne fixedPoint edge)]
  have countIdentity : (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) => ∑ edge, coreEdgeIndicator rule.network (marks ([], true)) edge) =
      (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) => ((terminalCoreEdges rule.network (marks ([], true))).card : ℝ)) := by
    funext marks
    exact (terminalCoreEdges_card_eq_sum rule.network (marks ([], true))).symm
  rw [countIdentity]
  exact innovation_root_integral rule probability positive belowOne fixedPoint
    (fun configuration => ((terminalCoreEdges rule.network configuration).card : ℝ))

theorem corePopulation_integral (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (depth : ℕ) :
    (∫ marks, corePopulation rule marks depth []
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
      terminalCoreMean rule.network probability ^ depth := by
  classical
  induction depth with
  | zero => simp [corePopulation]
  | succ depth inductionHypothesis =>
      have childMean (edge : Fin rule.edges) :
          (∫ marks, corePopulation rule marks depth [edge]
            ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
          ∫ marks, corePopulation rule marks depth []
            ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
        have mapIdentity := integral_map_of_stronglyMeasurable
          (μ := independentInnovationLaw rule probability positive belowOne fixedPoint)
          (φ := innovationTreeShift rule [edge]) (f := fun marks => corePopulation rule marks depth [])
          (innovationTreeShift_measurable rule [edge]) (corePopulation_measurable rule depth []).stronglyMeasurable
        rw [(innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).map_eq] at mapIdentity
        simpa only [corePopulation_shift, List.append_nil] using mapIdentity.symm
      have rootMeasurable (edge : Fin rule.edges) :
          Measurable (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) => coreEdgeIndicator rule.network (marks ([], true)) edge) :=
        (measurable_of_finite (fun configuration => coreEdgeIndicator rule.network configuration edge)).comp
          (measurable_pi_apply ([], true))
      have independent (edge : Fin rule.edges) : IndepFun
          (fun marks => coreEdgeIndicator rule.network (marks ([], true)) edge)
          (fun marks => corePopulation rule marks depth [edge])
          (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
        have independence := (innovationTreeRoot_children_independent rule probability positive belowOne fixedPoint true).comp
          (measurable_of_finite (fun configuration => coreEdgeIndicator rule.network configuration edge))
          ((corePopulation_measurable rule depth []).comp (measurable_pi_apply edge))
        simpa only [Function.comp_def, corePopulation_shift, List.append_nil] using independence
      have termIntegrable (edge : Fin rule.edges) :
          Integrable (fun marks => coreEdgeIndicator rule.network (marks ([], true)) edge *
            corePopulation rule marks depth [edge])
            (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
        apply (integrable_const ((rule.edges : ℝ) ^ depth)).mono'
          ((rootMeasurable edge).mul (corePopulation_measurable rule depth [edge])).aestronglyMeasurable
        filter_upwards [] with marks
        change ‖coreEdgeIndicator rule.network (marks ([], true)) edge *
          corePopulation rule marks depth [edge]‖ ≤ (rule.edges : ℝ) ^ depth
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coreEdgeIndicator_nonnegative _ _ _)
          (corePopulation_nonnegative rule marks depth [edge]))]
        calc
          _ ≤ 1 * corePopulation rule marks depth [edge] :=
            mul_le_mul_of_nonneg_right (coreEdgeIndicator_le_one rule.network (marks ([], true)) edge)
              (corePopulation_nonnegative rule marks depth [edge])
          _ = corePopulation rule marks depth [edge] := one_mul _
          _ ≤ _ := corePopulation_le_pow rule marks depth [edge]
      change (∫ marks, ∑ edge, coreEdgeIndicator rule.network (marks ([], true)) edge *
        corePopulation rule marks depth [edge] ∂independentInnovationLaw rule probability positive belowOne fixedPoint) = _
      rw [integral_finsetSum Finset.univ (fun edge _ => termIntegrable edge)]
      calc
        _ = ∑ edge, (∫ marks, coreEdgeIndicator rule.network (marks ([], true)) edge
            ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
              terminalCoreMean rule.network probability ^ depth := by
          apply Finset.sum_congr rfl
          intro edge _
          rw [(independent edge).integral_fun_mul_eq_mul_integral
            (rootMeasurable edge).aestronglyMeasurable (corePopulation_measurable rule depth [edge]).aestronglyMeasurable,
            childMean, inductionHypothesis]
        _ = (∑ edge, ∫ marks, coreEdgeIndicator rule.network (marks ([], true)) edge
            ∂independentInnovationLaw rule probability positive belowOne fixedPoint) *
              terminalCoreMean rule.network probability ^ depth := (Finset.sum_mul _ _ _).symm
        _ = _ := by rw [rootCoreIndicators_integral, pow_succ]; ring

theorem generation_core_count_integral (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability) (depth : ℕ) :
    (∫ marks, ((terminalCoreEdges (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)).card : ℝ)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
      terminalCoreMean rule.network probability ^ (depth + 1) := by
  rw [← corePopulation_integral rule probability positive belowOne fixedPoint (depth + 1)]
  apply integral_congr_ae
  filter_upwards [independentInnovationLaw_crosses rule probability positive belowOne fixedPoint] with marks crossing
  exact (corePopulation_eq_generation_count rule classicalRule marks crossing depth []).symm

end
end IGSIII4
