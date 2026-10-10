import IGSIII34.Percolation.ElectricalTree
import IGSIII34.Resistance.Connectivity
import IGSIII34.Resistance.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.IdentDistrib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem effectiveResistance_continuous_nonnegativeSubtype (network : FiniteNetwork Vertex Edge) :
    Continuous (fun input : {input : Edge → ℝ // ∀ edge, 0 ≤ input edge} =>
      network.effectiveResistance input.val) := by
  by_cases connected : network.graph.Reachable network.source network.target
  · exact (network.effectiveResistance_continuousOn_nonnegative connected).restrict
  · simpa only [network.disconnected_effectiveResistance connected] using
      (continuous_const : Continuous (fun _ : {input : Edge → ℝ // ∀ edge, 0 ≤ input edge} => (0 : ℝ)))

theorem effectiveResistance_nonnegative_all (network : FiniteNetwork Vertex Edge)
    {input : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge) :
    0 ≤ network.effectiveResistance input := by
  by_cases connected : network.graph.Reachable network.source network.target
  · exact network.effectiveResistance_nonneg (network.unitFlows_nonempty_of_connected connected) nonnegative
  · rw [network.disconnected_effectiveResistance connected]

end
end IGSIII34.Resistance.FiniteNetwork

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork MeasureTheory
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem electricalCell_continuous_nonnegative {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) :
    Continuous (fun input : {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge} =>
      electricalCell rule configuration input.val) := by
  have inputContinuous : Continuous (fun input : {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge} =>
      (⟨fun edge : {edge : Fin edges // configuration edge = true} => input.val edge.val,
        fun edge => input.property edge.val⟩ :
        {input : {edge : Fin edges // configuration edge = true} → ℝ // ∀ edge, 0 ≤ input edge})) := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun edge => (continuous_apply edge.val).comp continuous_subtype_val)
  exact (network rule configuration).effectiveResistance_continuous_nonnegativeSubtype.comp inputContinuous

theorem electricalCell_measurable {Outcome : Type*} [MeasurableSpace Outcome]
    {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Outcome → Configuration edges) (configurationMeasurable : Measurable configuration)
    (input : Outcome → Fin edges → ℝ) (inputMeasurable : Measurable input)
    (nonnegative : ∀ outcome edge, 0 ≤ input outcome edge) :
    Measurable (fun outcome => electricalCell rule (configuration outcome) (input outcome)) := by
  have functional : Measurable (fun data : Configuration edges ×
      {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge} => electricalCell rule data.1 data.2.val) :=
    measurable_from_prod_countable_right (fun configuration =>
      (electricalCell_continuous_nonnegative rule configuration).measurable)
  exact functional.comp (configurationMeasurable.prodMk (inputMeasurable.subtype_mk (h := nonnegative)))

theorem electricalIteration_nonnegative (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    0 ≤ electricalIteration rule marks depth address := by
  induction depth generalizing address with
  | zero => norm_num [electricalIteration]
  | succ depth inductionHypothesis =>
      exact (network rule.network (marks (address, true))).effectiveResistance_nonnegative_all
        (fun edge => inductionHypothesis (address ++ [edge.val]))

theorem electricalIteration_measurable (rule : Rule) (depth : ℕ) (address : List (Fin rule.edges)) :
    Measurable (fun marks => electricalIteration rule marks depth address) := by
  induction depth generalizing address with
  | zero => exact measurable_const
  | succ depth inductionHypothesis =>
      exact electricalCell_measurable rule.network (fun marks => marks (address, true))
        (measurable_pi_apply (address, true))
        (fun marks edge => electricalIteration rule marks depth (address ++ [edge]))
        (measurable_pi_lambda _ (fun edge => inductionHypothesis (address ++ [edge])))
        (fun marks edge => electricalIteration_nonnegative rule marks depth (address ++ [edge]))

theorem electricalIteration_positive_ae (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      0 < electricalIteration rule marks depth address := by
  filter_upwards [independentInnovationLaw_crosses rule parameter positive belowOne fixedPoint] with marks crossing
  exact electricalIteration_positive rule marks (fun address => crossing address true) depth address

theorem electricalIteration_children_independent (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    ProbabilityTheory.iIndepFun (fun edge marks => electricalIteration rule marks depth [edge])
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  have independent := IGSIII.Probability.innovationTreeChildren_independent rule parameter positive belowOne fixedPoint
  have independentOutputs := independent.comp (fun _ marks => electricalIteration rule marks depth [])
    (fun _ => electricalIteration_measurable rule depth [])
  simpa only [Function.comp_def, electricalIteration_shift, List.append_nil] using independentOutputs

theorem electricalIteration_child_identDistrib (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) (edge : Fin rule.edges) :
    ProbabilityTheory.IdentDistrib (fun marks => electricalIteration rule marks depth [edge])
      (fun marks => electricalIteration rule marks depth [])
      (independentInnovationLaw rule parameter positive belowOne fixedPoint)
      (independentInnovationLaw rule parameter positive belowOne fixedPoint) := by
  refine ⟨(electricalIteration_measurable rule depth [edge]).aemeasurable,
    (electricalIteration_measurable rule depth []).aemeasurable, ?_⟩
  calc
    _ = ((independentInnovationLaw rule parameter positive belowOne fixedPoint).map
          (IGSIII.Probability.innovationTreeShift rule [edge])).map
          (fun marks => electricalIteration rule marks depth []) := by
      rw [Measure.map_map (electricalIteration_measurable rule depth [])
        (IGSIII.Probability.innovationTreeShift_measurable rule [edge])]
      congr 1
      funext marks
      simp only [Function.comp_apply, electricalIteration_shift, List.append_nil]
    _ = _ := by rw [(IGSIII.Probability.innovationTreeShift_preserving rule parameter positive belowOne fixedPoint [edge]).map_eq]

end
end IGSIII34.Percolation
