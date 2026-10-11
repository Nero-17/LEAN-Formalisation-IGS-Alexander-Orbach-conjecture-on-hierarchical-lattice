import IGSIII34.Percolation.Continuation.ElectricalFiniteLawVariance
import Mathlib.MeasureTheory.Function.SimpleFunc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open scoped ENNReal

theorem simpleFunc_electricalCell_variance_le_product_moments
    {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (crosses : network.crosses configuration = true)
    (resistance : SimpleFunc Sample ℝ) (positive : ∀ sample, 0 < resistance sample)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) (inverseMoment : ℝ)
    (inverseBound : (∫ sample, (resistance sample)⁻¹^power ∂measure) ≤ inverseMoment) :
    (∫ input, (electricalCell network configuration (fun edge => resistance (input edge)) -
      ∫ input, electricalCell network configuration (fun edge => resistance (input edge))
        ∂Measure.pi (fun _ : Fin edges => measure))^2 ∂Measure.pi (fun _ : Fin edges => measure)) ≤
      2*(∫ sample, resistance sample^2 ∂measure) *
        (∫ input, electricalCell network configuration (fun edge => resistance (input edge))^2
          ∂Measure.pi (fun _ : Fin edges => measure))^(1/(2:ℝ)) *
            ((edges:ℝ)*inverseMoment)^(1/power) := by
  let State := {value : ℝ // value ∈ resistance.range}
  let resistanceMap (sample : Sample) : State := ⟨resistance sample, resistance.mem_range_self sample⟩
  have resistanceMapMeasurable : Measurable resistanceMap := by
    exact (resistance.measurable : Measurable (resistance : Sample → ℝ)).subtype_mk
  let finiteLaw := measure.map resistanceMap
  letI : IsProbabilityMeasure finiteLaw := Measure.isProbabilityMeasure_map resistanceMapMeasurable.aemeasurable
  have statePositive (state : State) : 0 < (state:ℝ) := by
    obtain ⟨sample, equality⟩ := SimpleFunc.mem_range.mp state.property
    rw [← equality]
    exact positive sample
  have transportSingle (response : State → ℝ) :
      (∫ state, response state ∂finiteLaw) = ∫ sample, response (resistanceMap sample) ∂measure := by
    exact integral_map_of_stronglyMeasurable resistanceMapMeasurable (measurable_of_countable response).stronglyMeasurable
  have transportProduct (response : (Fin edges → State) → ℝ) :
      (∫ input, response input ∂Measure.pi (fun _ : Fin edges => finiteLaw)) =
        ∫ input, response (fun edge => resistanceMap (input edge)) ∂Measure.pi (fun _ : Fin edges => measure) := by
    have mapEquality := Measure.pi_map_pi (μ := fun _ : Fin edges => measure)
      (fun _ : Fin edges => resistanceMapMeasurable.aemeasurable)
    rw [← mapEquality]
    exact integral_map_of_stronglyMeasurable
      (measurable_pi_lambda _ (fun edge => resistanceMapMeasurable.comp (measurable_pi_apply edge)))
      (measurable_of_countable response).stronglyMeasurable
  have bound := finite_probability_electricalCell_variance_le_product_moments finiteLaw network configuration crosses
    (fun state : State => (state:ℝ)) statePositive powerAtLeastTwo inverseMoment
    (by simpa only [transportSingle, resistanceMap] using inverseBound)
  simp_rw [transportSingle, transportProduct] at bound
  exact bound

end
end IGSIII34.Percolation
