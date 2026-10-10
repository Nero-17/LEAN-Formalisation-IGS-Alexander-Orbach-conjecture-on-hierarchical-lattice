import IGSIII34.Percolation.ResistanceMomentExponent
import IGSIII34.Percolation.ResistanceAddress

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability Filter
open IGSIII.Chemical.Substitution
open scoped _root_.Topology NNReal ENNReal

/-- The manuscript resistance-exponent theorem, on the actual critical C/N tree.
All four limits share one deterministic growth, at every fixed connected address;
the almost-sure limits hold simultaneously over the countable address family. -/
theorem exists_actual_resistance_exponent
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (pathLength : Configuration rule.edges → ℕ)
    (distanceBound : ∀ configuration, rule.network.crosses configuration = true →
      (network rule.network configuration).graph.dist rule.network.source rule.network.target ≤ pathLength configuration) :
    ∃ growth : ℝ, 1 < growth ∧ deriv rule.network.reliability parameter ≤ growth ∧
      growth ≤ (∫ configuration, (pathLength configuration : ℝ)
        ∂(connectedConfigurationLaw rule parameter positive belowOne fixedPoint : Measure _)) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
        ∀ address : List (Fin rule.edges),
          Tendsto (fun depth : ℕ => Real.log (electricalIteration rule marks depth address)/depth) atTop (𝓝 (Real.log growth))) ∧
      (∀ address : List (Fin rule.edges),
        Tendsto (fun depth : ℕ => Real.log (∫ marks, electricalIteration rule marks depth address
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth))) ∧
      (∀ address : List (Fin rule.edges),
        Tendsto (fun depth : ℕ => (∫ marks, Real.log (electricalIteration rule marks depth address)
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (Real.log growth))) ∧
      ∀ (address : List (Fin rule.edges)) (exponent : ℝ),
        Tendsto (fun depth : ℕ => Real.log (∫ marks, (electricalIteration rule marks depth address)^exponent
          ∂independentInnovationLaw rule parameter positive belowOne fixedPoint)/depth) atTop (𝓝 (exponent*Real.log growth)) := by
  obtain ⟨growth, aboveOne, lower, upper, almostSure, meanLimit, meanLogLimit, momentLimit⟩ :=
    exists_actual_electrical_exponent rule classical parameter positive belowOne fixedPoint pathLength distanceBound
  refine ⟨growth, aboveOne, lower, upper,
    electricalIteration_log_limit_at_all_addresses rule parameter positive belowOne fixedPoint growth almostSure, ?_, ?_, ?_⟩
  · intro address
    apply meanLimit.congr'
    filter_upwards with depth
    rw [electricalIteration_integral_at_address rule parameter positive belowOne fixedPoint depth address (fun value => value) measurable_id]
  · intro address
    apply meanLogLimit.congr'
    filter_upwards with depth
    rw [electricalIteration_integral_at_address rule parameter positive belowOne fixedPoint depth address Real.log Real.measurable_log]
  · intro address exponent
    apply (momentLimit exponent).congr'
    filter_upwards with depth
    rw [electricalIteration_integral_at_address rule parameter positive belowOne fixedPoint depth address
      (fun value => value^exponent) (measurable_id.pow measurable_const)]

end
end IGSIII34.Percolation
