import IGSIII34.Resistance.CurrentContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open MeasureTheory

attribute [local irreducible] effectiveResistance

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem positive_resistance_functional_continuous (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    Continuous (fun resistance : {resistance : Edge → ℝ // ∀ edge, 0 < resistance edge} =>
      network.effectiveResistance resistance.val) := by
  have positiveContinuous : ContinuousOn network.effectiveResistance
      {resistance | ∀ edge, 0 < resistance edge} :=
    (network.effectiveResistance_continuousOn_nonnegative connected).mono
      (fun _ positive edge => (positive edge).le)
  exact positiveContinuous.restrict

theorem effectiveResistance_measurable {Outcome : Type*} [MeasurableSpace Outcome]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge) :
    Measurable (fun outcome => network.effectiveResistance (resistance outcome)) := by
  have measurableFunctional : Measurable
      (fun value : {value : Edge → ℝ // ∀ edge, 0 < value edge} =>
        network.effectiveResistance value.val) :=
    (network.positive_resistance_functional_continuous connected).measurable
  have measurablePositiveInput : Measurable
      (fun outcome => (⟨resistance outcome, positive outcome⟩ :
        {value : Edge → ℝ // ∀ edge, 0 < value edge})) :=
    measurableInput.subtype_mk
  exact measurableFunctional.comp measurablePositiveInput

theorem minimizingCurrent_measurable {Outcome : Type*} [MeasurableSpace Outcome]
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge) :
    Measurable (fun outcome => network.minimizingCurrent connected (resistance outcome) (positive outcome)) :=
  (network.positiveCurrent_continuous connected).measurable.comp
    (measurableInput.subtype_mk (h := positive))

theorem effectiveResistance_le_sum_resistances (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    network.effectiveResistance resistance ≤ ∑ edge, resistance edge := by
  obtain ⟨current, unitFlow, minimal⟩ := network.exists_minimizing_unitFlow_of_connected connected positive
  rw [← minimal]
  apply Finset.sum_le_sum
  intro edge _
  have currentBound := network.minimizing_current_abs_le_one positive unitFlow minimal edge
  have squareBound : current edge ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (current edge), sq_abs (current edge)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left squareBound (positive edge).le

theorem effectiveResistance_integrable {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure) :
    Integrable (fun outcome => network.effectiveResistance (resistance outcome)) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inputIntegrable edge)).mono'
    (network.effectiveResistance_measurable connected resistance measurableInput positive).aestronglyMeasurable
  filter_upwards [] with outcome
  rw [Real.norm_eq_abs, abs_of_nonneg
    (network.effectiveResistance_nonneg (network.unitFlows_nonempty_of_connected connected)
      (fun edge => (positive outcome edge).le))]
  exact network.effectiveResistance_le_sum_resistances connected (positive outcome)

theorem effectiveResistance_integral_jensen {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Outcome → Edge → ℝ) (measurableInput : Measurable resistance)
    (positive : ∀ outcome edge, 0 < resistance outcome edge)
    (inputIntegrable : ∀ edge, Integrable (fun outcome => resistance outcome edge) measure) :
    (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ≤
      network.effectiveResistance (fun edge => ∫ outcome, resistance outcome edge ∂measure) := by
  apply network.le_effectiveResistance (network.unitFlows_nonempty_of_connected connected)
  intro current unitFlow
  have energyIntegrable := integrable_finsetSum Finset.univ
    (fun edge _ => (inputIntegrable edge).mul_const (current edge ^ 2))
  have comparison := integral_mono
    (network.effectiveResistance_integrable measure connected resistance measurableInput positive inputIntegrable)
    energyIntegrable (fun outcome =>
      network.effectiveResistance_le_energy (fun edge => (positive outcome edge).le) unitFlow)
  change (∫ outcome, network.effectiveResistance (resistance outcome) ∂measure) ≤
    ∫ outcome, ∑ edge, resistance outcome edge * current edge ^ 2 ∂measure at comparison
  rw [integral_finsetSum Finset.univ
    (fun edge _ => (inputIntegrable edge).mul_const (current edge ^ 2))] at comparison
  simpa only [integral_mul_const, energy] using comparison

end
end IGSIII34.Resistance.FiniteNetwork
