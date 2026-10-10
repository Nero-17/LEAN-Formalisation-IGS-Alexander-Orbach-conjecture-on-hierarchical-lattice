import IGSIII34.Percolation.ElectricalMeasurability
import IGSIII34.Resistance.IntegralJensen

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability MeasureTheory ProbabilityTheory

theorem electricalCell_eq_zero_of_not_crosses {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (doesNotCross : rule.crosses configuration ≠ true) (input : Fin edges → ℝ) :
    electricalCell rule configuration input = 0 := by
  have disconnected : ¬ (network rule configuration).graph.Reachable
      (network rule configuration).source (network rule configuration).target := by
    change ¬ (network rule configuration).graph.Reachable rule.source rule.target
    rw [graph_eq_openGraph]
    exact fun reachable => doesNotCross ((rule.crosses_eq_true configuration).mpr reachable)
  exact (network rule configuration).disconnected_effectiveResistance disconnected _

theorem electricalCell_monotone {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    {first second : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ first edge)
    (comparison : ∀ edge, first edge ≤ second edge) :
    electricalCell rule configuration first ≤ electricalCell rule configuration second := by
  by_cases crosses : rule.crosses configuration = true
  · exact (network rule configuration).effectiveResistance_mono
      ((network rule configuration).unitFlows_nonempty_of_connected (connected_of_crosses _ _ crosses))
      (fun edge => nonnegative edge.val) (fun edge => comparison edge.val)
  · simp only [electricalCell_eq_zero_of_not_crosses rule configuration crosses, le_refl]

theorem electricalCell_superadditive {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    {first second : Fin edges → ℝ} (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge) :
    electricalCell rule configuration first + electricalCell rule configuration second ≤
      electricalCell rule configuration (fun edge => first edge + second edge) := by
  by_cases crosses : rule.crosses configuration = true
  · exact (network rule configuration).effectiveResistance_superadditive
      ((network rule configuration).unitFlows_nonempty_of_connected (connected_of_crosses _ _ crosses))
      (fun edge => firstNonnegative edge.val) (fun edge => secondNonnegative edge.val)
  · simp only [electricalCell_eq_zero_of_not_crosses rule configuration crosses, zero_add, le_refl]

theorem electricalCell_scale {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    {input : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge)
    {scalar : ℝ} (scalarNonnegative : 0 ≤ scalar) :
    electricalCell rule configuration (fun edge => scalar * input edge) =
      scalar * electricalCell rule configuration input := by
  by_cases crosses : rule.crosses configuration = true
  · exact (network rule configuration).effectiveResistance_scale
      ((network rule configuration).unitFlows_nonempty_of_connected (connected_of_crosses _ _ crosses))
      (fun edge => nonnegative edge.val) scalarNonnegative
  · simp only [electricalCell_eq_zero_of_not_crosses rule configuration crosses, mul_zero]

theorem sum_open_edges_le_sum {edges : ℕ} (configuration : Configuration edges)
    (input : Fin edges → ℝ) (nonnegative : ∀ edge, 0 ≤ input edge) :
    (∑ edge : {edge : Fin edges // configuration edge = true}, input edge.val) ≤ ∑ edge, input edge := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun edge => configuration edge = true)
    (fun edge => by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun edge _ _ => nonnegative edge)

theorem electricalCell_le_sum {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    {input : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge) :
    electricalCell rule configuration input ≤ ∑ edge, input edge := by
  by_cases crosses : rule.crosses configuration = true
  · obtain ⟨current, unitFlow, bounded, minimizing⟩ :=
      (network rule configuration).exists_bounded_minimizing_unitFlow_of_nonnegative
        (connected_of_crosses _ _ crosses) (fun edge => nonnegative edge.val)
    calc
      _ = energy (fun edge : {edge : Fin edges // configuration edge = true} => input edge.val) current := minimizing.symm
      _ ≤ ∑ edge : {edge : Fin edges // configuration edge = true}, input edge.val := by
        apply Finset.sum_le_sum
        intro edge _
        have currentSquare : current edge ^ 2 ≤ 1 := by
          have bound := bounded edge
          nlinarith [abs_nonneg (current edge), sq_abs (current edge)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left currentSquare (nonnegative edge.val)
      _ ≤ _ := sum_open_edges_le_sum configuration input nonnegative
  · rw [electricalCell_eq_zero_of_not_crosses rule configuration crosses]
    exact Finset.sum_nonneg (fun edge _ => nonnegative edge)

theorem electricalCell_abs_sub_le_sum_abs {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    {first second : Fin edges → ℝ} (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge) :
    |electricalCell rule configuration first - electricalCell rule configuration second| ≤
      ∑ edge, |first edge - second edge| := by
  by_cases crosses : rule.crosses configuration = true
  · exact ((network rule configuration).effectiveResistance_abs_sub_le_sum_abs_of_nonnegative
      (connected_of_crosses _ _ crosses) (fun edge => firstNonnegative edge.val)
      (fun edge => secondNonnegative edge.val)).trans
      (sum_open_edges_le_sum configuration (fun edge => |first edge - second edge|)
        (fun _ => abs_nonneg _))
  · simp only [electricalCell_eq_zero_of_not_crosses rule configuration crosses, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

def electricalTransfer (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  electricalCell rule.network (marks ([], true))
    (fun edge => value (innovationTreeShift rule [edge] marks))

theorem electricalTransfer_measurable (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (valueMeasurable : Measurable value) (nonnegative : ∀ marks, 0 ≤ value marks) :
    Measurable (electricalTransfer rule value) := by
  unfold electricalTransfer
  exact electricalCell_measurable rule.network
    (fun marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges => marks ([], true))
    (measurable_pi_apply ([], true)) (fun marks edge => value (innovationTreeShift rule [edge] marks))
    (measurable_pi_lambda _ (fun edge => valueMeasurable.comp (innovationTreeShift_measurable rule [edge])))
    (fun marks edge => nonnegative (innovationTreeShift rule [edge] marks))

theorem electricalTransfer_iteration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ) :
    electricalTransfer rule (fun marks => electricalIteration rule marks depth []) marks =
      electricalIteration rule marks (depth + 1) [] := by
  simp only [electricalTransfer, electricalIteration, electricalIteration_shift,
    List.append_nil, List.nil_append]

theorem electricalTransfer_nonnegative (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (nonnegative : ∀ marks, 0 ≤ value marks)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    0 ≤ electricalTransfer rule value marks :=
  (network rule.network (marks ([], true))).effectiveResistance_nonnegative_all
    (fun edge => nonnegative (innovationTreeShift rule [edge.val] marks))

theorem electricalTransfer_integrable (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (valueMeasurable : Measurable value) (nonnegative : ∀ marks, 0 ≤ value marks)
    (valueIntegrable : Integrable value (independentInnovationLaw rule parameter positive belowOne fixedPoint)) :
    Integrable (electricalTransfer rule value)
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  have childIntegrable (edge : Fin rule.edges) :
      Integrable (fun marks => value (innovationTreeShift rule [edge] marks))
        (independentInnovationLaw rule parameter positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule parameter positive belowOne fixedPoint [edge]).integrable_comp_of_integrable valueIntegrable
  apply (integrable_finsetSum Finset.univ (fun edge _ => childIntegrable edge)).mono'
    (electricalTransfer_measurable rule value valueMeasurable nonnegative).aestronglyMeasurable
  filter_upwards [] with marks
  rw [Real.norm_eq_abs, abs_of_nonneg (electricalTransfer_nonnegative rule value nonnegative marks)]
  exact electricalCell_le_sum rule.network (marks ([], true))
    (fun edge => nonnegative (innovationTreeShift rule [edge] marks))

theorem electricalTransfer_positive_ae (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      0 < value marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      0 < electricalTransfer rule value marks := by
  have childrenPositive : ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      ∀ edge : Fin rule.edges, 0 < value (innovationTreeShift rule [edge] marks) := by
    apply ae_all_iff.mpr
    intro edge
    have transported := valuePositive
    rw [← (innovationTreeShift_preserving rule parameter positive belowOne fixedPoint [edge]).map_eq] at transported
    exact ae_of_ae_map (innovationTreeShift_measurable rule [edge]).aemeasurable transported
  filter_upwards [childrenPositive, independentInnovationLaw_crosses rule parameter positive belowOne fixedPoint]
    with marks childPositive crossing
  exact (network rule.network (marks ([], true))).effectiveResistance_pos_of_connected
    (connected_of_crosses _ _ (crossing [] true)) (fun edge => childPositive edge.val)

end
end IGSIII34.Percolation
