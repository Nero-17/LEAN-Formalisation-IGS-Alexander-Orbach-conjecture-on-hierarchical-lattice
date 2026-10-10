import IGSIII34.Percolation.ElectricalConditionalJensen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII34.Probability
open scoped ENNReal

theorem electricalCell_integral_mean_upper
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Sample → Fin edges → ℝ) (measurable : Measurable input) (positive : ∀ sample edge, 0 < input sample edge)
    (inputIntegrable : ∀ edge, Integrable (fun sample => input sample edge) measure)
    (mean : ℝ) (meanNonnegative : 0 ≤ mean)
    (commonMean : ∀ edge, (∫ sample, input sample edge ∂measure) = mean) :
    (∫ sample, electricalCell network configuration (input sample) ∂measure) ≤
      mean * unitConfigurationResistance network configuration := by
  by_cases crossing : network.crosses configuration = true
  · have connected := connected_of_crosses network configuration crossing
    have bound : (∫ sample, electricalCell network configuration (input sample) ∂measure) ≤
        electricalCell network configuration (fun edge => mean) := by
      have comparison := (IGSIII34.Percolation.network network configuration).effectiveResistance_integral_jensen
        measure connected (fun sample edge => input sample edge.val)
        (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).comp measurable))
        (fun sample edge => positive sample edge.val) (fun edge => inputIntegrable edge.val)
      simpa only [commonMean, electricalCell] using comparison
    convert bound using 1
    exact (by simpa only [mul_one, unitConfigurationResistance] using (electricalCell_scale network configuration (input := fun _ => 1) (fun _ => zero_le_one) meanNonnegative).symm)
  · simp only [electricalCell_eq_zero_of_not_crosses network configuration crossing,
      unitConfigurationResistance, integral_zero, mul_zero, le_refl]

theorem independent_conditional_electrical_mean_upper
    {Sample History Boundary : Type*} [MeasurableSpace Sample] [MeasurableSpace History]
    [MeasurableSpace Boundary] [StandardBorelSpace Boundary] [Nonempty Boundary]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (history : Sample → History) (boundary : Sample → Boundary)
    (historyMeasurable : Measurable history) (boundaryMeasurable : Measurable boundary)
    (independent : IndepFun history boundary measure)
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : History → Configuration edges) (configurationMeasurable : Measurable configuration)
    (input : Boundary → Fin edges → ℝ) (inputMeasurable : Measurable input)
    (positive : ∀ sample edge, 0 < input sample edge)
    (inputIntegrable : ∀ edge, Integrable (fun sample => input sample edge) (measure.map boundary))
    (mean : ℝ) (meanNonnegative : 0 ≤ mean)
    (commonMean : ∀ edge, (∫ sample, input sample edge ∂measure.map boundary) = mean) :
    ∀ᵐ sample ∂measure,
      measure[fun sample => electricalCell network (configuration (history sample)) (input (boundary sample)) |
        (inferInstance : MeasurableSpace History).comap history] sample ≤
      mean * unitConfigurationResistance network (configuration (history sample)) := by
  letI : IsProbabilityMeasure (measure.map boundary) := Measure.isProbabilityMeasure_map boundaryMeasurable.aemeasurable
  have actualInputIntegrable (edge : Fin edges) : Integrable (fun sample => input (boundary sample) edge) measure :=
    (integrable_map_measure ((measurable_pi_apply edge).comp inputMeasurable).aestronglyMeasurable
      boundaryMeasurable.aemeasurable).mp (inputIntegrable edge)
  have responseMeasurable : Measurable (fun data : History × Boundary =>
      electricalCell network (configuration data.1) (input data.2)) :=
    electricalCell_measurable network _ (configurationMeasurable.comp measurable_fst) _
      (inputMeasurable.comp measurable_snd) (fun data edge => (positive data.2 edge).le)
  have responseIntegrable : Integrable (fun sample => electricalCell network
      (configuration (history sample)) (input (boundary sample))) measure :=
    electricalCell_random_integrable measure network _ (configurationMeasurable.comp historyMeasurable)
      _ (inputMeasurable.comp boundaryMeasurable) (fun sample edge => positive (boundary sample) edge) actualInputIntegrable
  have conditional := independent_pair_condExp_eq_integral measure history boundary historyMeasurable boundaryMeasurable
    independent _ responseMeasurable.stronglyMeasurable responseIntegrable
  filter_upwards [conditional] with sample equality
  rw [equality]
  exact electricalCell_integral_mean_upper (measure.map boundary) network _ input inputMeasurable positive
    inputIntegrable mean meanNonnegative commonMean

end
end IGSIII34.Percolation

