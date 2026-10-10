import IGSIII34.Resistance.IntegralJensen

set_option autoImplicit false
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory
attribute [local irreducible] effectiveResistance
variable {Vertex Edge Outcome : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge] [MeasurableSpace Outcome]

theorem nonnegative_resistance_measurable (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (inputMeasurable : Measurable resistance)
    (nonnegative : ∀ outcome edge, 0 ≤ resistance outcome edge) :
    Measurable (fun outcome => network.effectiveResistance (resistance outcome)) := by
  have functional : Continuous
      (fun value : {value : Edge → ℝ // ∀ edge, 0 ≤ value edge} =>
        network.effectiveResistance value.val) :=
    (network.effectiveResistance_continuousOn_nonnegative connected).restrict
  exact functional.measurable.comp (inputMeasurable.subtype_mk (h := nonnegative))

theorem nonnegative_resistance_integrable (measure : Measure Outcome)
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (inputMeasurable : Measurable resistance)
    (nonnegative : ∀ outcome edge, 0 ≤ resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure) :
    Integrable (fun outcome => network.effectiveResistance (resistance outcome)) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inputIntegrable edge)).mono'
    (network.nonnegative_resistance_measurable connected resistance inputMeasurable nonnegative).aestronglyMeasurable
  filter_upwards [] with outcome
  rw [Real.norm_eq_abs, abs_of_nonneg (network.effectiveResistance_nonneg
    (network.unitFlows_nonempty_of_connected connected) (nonnegative outcome))]
  obtain ⟨current, flow, bounded, minimal⟩ :=
    network.exists_bounded_minimizing_unitFlow_of_nonnegative connected (nonnegative outcome)
  rw [← minimal]
  apply Finset.sum_le_sum
  intro edge _
  have squareBound : current edge ^ 2 ≤ 1 := by
    nlinarith [bounded edge, abs_nonneg (current edge), sq_abs (current edge)]
  exact (mul_le_mul_of_nonneg_left squareBound (nonnegative outcome edge)).trans_eq (mul_one _)

theorem nonnegative_resistance_integral_jensen (measure : Measure Outcome)
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (inputMeasurable : Measurable resistance)
    (nonnegative : ∀ outcome edge, 0 ≤ resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure) :
    (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ≤
      network.effectiveResistance (fun edge => ∫ outcome, resistance outcome edge ∂measure) := by
  apply network.le_effectiveResistance (network.unitFlows_nonempty_of_connected connected)
  intro current flow
  have trialIntegrable := integrable_finsetSum Finset.univ
    (fun edge _ => (inputIntegrable edge).mul_const (current edge ^ 2))
  have comparison := integral_mono
    (network.nonnegative_resistance_integrable measure connected resistance inputMeasurable nonnegative inputIntegrable)
    trialIntegrable (fun outcome => network.effectiveResistance_le_energy (nonnegative outcome) flow)
  change (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ≤
    ∫ outcome, ∑ edge, resistance outcome edge * current edge ^ 2 ∂measure at comparison
  rw [integral_finsetSum Finset.univ (fun edge _ => (inputIntegrable edge).mul_const (current edge ^ 2))] at comparison
  simpa only [integral_mul_const, energy] using comparison

end
end IGSIII34.Resistance.FiniteNetwork
