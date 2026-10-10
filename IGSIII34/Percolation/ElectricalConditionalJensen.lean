import IGSIII34.Percolation.ElectricalIntegralLower
import IGSIII34.Probability.IndependentConditioning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII34.Probability
open scoped ENNReal

theorem electricalCell_random_integrable {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Sample → Configuration edges) (configurationMeasurable : Measurable configuration)
    (input : Sample → Fin edges → ℝ) (inputMeasurable : Measurable input)
    (positive : ∀ sample edge, 0 < input sample edge)
    (inputIntegrable : ∀ edge, Integrable (fun sample => input sample edge) measure) :
    Integrable (fun sample => electricalCell network (configuration sample) (input sample)) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inputIntegrable edge)).mono'
    (electricalCell_measurable network configuration configurationMeasurable input inputMeasurable
      (fun sample edge => (positive sample edge).le)).aestronglyMeasurable
  filter_upwards [] with sample
  have resistanceNonnegative : 0 ≤ electricalCell network (configuration sample) (input sample) :=
    (IGSIII34.Percolation.network network (configuration sample)).effectiveResistance_nonnegative_all
      (fun edge => (positive sample edge.val).le)
  rw [Real.norm_eq_abs, abs_of_nonneg resistanceNonnegative]
  exact electricalCell_le_sum network (configuration sample) (fun edge => (positive sample edge).le)

theorem electricalCell_random_inverse_integrable {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Sample → Configuration edges) (configurationMeasurable : Measurable configuration)
    (input : Sample → Fin edges → ℝ) (inputMeasurable : Measurable input)
    (positive : ∀ sample edge, 0 < input sample edge)
    (inverseIntegrable : ∀ edge, Integrable (fun sample => (input sample edge)⁻¹) measure) :
    Integrable (fun sample => (electricalCell network (configuration sample) (input sample))⁻¹) measure := by
  apply (integrable_finsetSum Finset.univ (fun edge _ => inverseIntegrable edge)).mono'
    ((electricalCell_measurable network configuration configurationMeasurable input inputMeasurable
      (fun sample edge => (positive sample edge).le)).inv.aestronglyMeasurable)
  filter_upwards [] with sample
  change ‖(electricalCell network (configuration sample) (input sample))⁻¹‖ ≤ _
  have resistanceNonnegative : 0 ≤ electricalCell network (configuration sample) (input sample) :=
    (IGSIII34.Percolation.network network (configuration sample)).effectiveResistance_nonnegative_all
      (fun edge => (positive sample edge.val).le)
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr resistanceNonnegative)]
  exact electricalCell_inv_le_sum_inv network (configuration sample) (input sample) (positive sample)

theorem independent_conditional_electrical_mean_lower
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
    (inverseIntegrable : ∀ edge, Integrable (fun sample => (input sample edge)⁻¹) (measure.map boundary))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ sample, (input sample edge)⁻¹ ∂measure.map boundary) = inverseMean) :
    ∀ᵐ sample ∂measure, unitConfigurationResistance network (configuration (history sample)) / inverseMean ≤
      measure[fun sample => electricalCell network (configuration (history sample)) (input (boundary sample)) |
        (inferInstance : MeasurableSpace History).comap history] sample := by
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
  by_cases crossing : network.crosses (configuration (history sample)) = true
  · exact electricalCell_integral_mean_lower (measure.map boundary) network _ crossing input inputMeasurable positive
      inputIntegrable inverseIntegrable inverseMean inverseMeanPositive commonInverseMean
  · simp only [unitConfigurationResistance, electricalCell_eq_zero_of_not_crosses network _ crossing,
      zero_div, integral_zero, le_refl]

end
end IGSIII34.Percolation
