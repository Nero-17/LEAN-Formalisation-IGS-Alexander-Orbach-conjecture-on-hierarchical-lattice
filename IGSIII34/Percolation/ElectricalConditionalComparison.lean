import IGSIII34.Percolation.ElectricalConditionalJensen
import IGSIII34.Resistance.IntegralComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII34.Probability
open scoped ENNReal

theorem electricalCell_independent_pair_integral_comparison
    {Sample State : Type*} [MeasurableSpace Sample] [MeasurableSpace State]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (edgeInputs : Fin edges → Sample → State) (independent : iIndepFun edgeInputs measure)
    (inputsMeasurable : ∀ edge, Measurable (edgeInputs edge)) (base : State)
    (first second : State → ℝ) (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (firstPositive : ∀ value, 0 < first value) (secondPositive : ∀ value, 0 < second value)
    (firstIntegrable : ∀ edge, Integrable (fun sample => first (edgeInputs edge sample)) measure)
    (secondIntegrable : ∀ edge, Integrable (fun sample => second (edgeInputs edge sample)) measure)
    (numeratorIntegrable : ∀ edge, Integrable (fun sample =>
      max (first (edgeInputs edge sample)-second (edgeInputs edge sample)) 0 *
        max 1 ((second (edgeInputs edge sample))⁻¹^2)) measure)
    {numerator denominator : ℝ} (numeratorNonnegative : 0 ≤ numerator) (denominatorPositive : 0 < denominator)
    (commonNumerator : ∀ edge, (∫ sample,
      max (first (edgeInputs edge sample)-second (edgeInputs edge sample)) 0 *
        max 1 ((second (edgeInputs edge sample))⁻¹^2) ∂measure) = numerator)
    (commonDenominator : ∀ edge, (∫ sample,
      min (second (edgeInputs edge sample)) (second (edgeInputs edge sample))⁻¹ ∂measure) = denominator) :
    (∫ sample, max (electricalCell network configuration (fun edge => first (edgeInputs edge sample))-
      electricalCell network configuration (fun edge => second (edgeInputs edge sample))) 0 ∂measure) ≤
      (numerator/denominator) * ∫ sample,
        electricalCell network configuration (fun edge => second (edgeInputs edge sample)) ∂measure := by
  by_cases crossing : network.crosses configuration = true
  · exact (IGSIII34.Percolation.network network configuration).independent_pair_resistance_integral_comparison
      measure (connected_of_crosses network configuration crossing)
      (fun edge => edgeInputs edge.val) (independent.precomp Subtype.val_injective)
      (fun edge => inputsMeasurable edge.val) base first second firstMeasurable secondMeasurable firstPositive secondPositive
      (fun edge => firstIntegrable edge.val) (fun edge => secondIntegrable edge.val)
      (fun edge => numeratorIntegrable edge.val) numeratorNonnegative denominatorPositive
      (fun edge => commonNumerator edge.val) (fun edge => commonDenominator edge.val)
  · simp only [electricalCell_eq_zero_of_not_crosses network configuration crossing, sub_self, max_self,
      integral_zero, mul_zero, le_refl]

theorem independent_conditional_electrical_pair_comparison
    {Sample History Boundary State : Type*} [MeasurableSpace Sample] [MeasurableSpace History]
    [MeasurableSpace Boundary] [StandardBorelSpace Boundary] [Nonempty Boundary] [MeasurableSpace State]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (history : Sample → History) (boundary : Sample → Boundary)
    (historyMeasurable : Measurable history) (boundaryMeasurable : Measurable boundary)
    (historyIndependent : IndepFun history boundary measure)
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : History → Configuration edges) (configurationMeasurable : Measurable configuration)
    (edgeInputs : Fin edges → Boundary → State) (independent : iIndepFun edgeInputs (measure.map boundary))
    (inputsMeasurable : ∀ edge, Measurable (edgeInputs edge)) (base : State)
    (first second : State → ℝ) (firstMeasurable : Measurable first) (secondMeasurable : Measurable second)
    (firstPositive : ∀ value, 0 < first value) (secondPositive : ∀ value, 0 < second value)
    (firstIntegrable : ∀ edge, Integrable (fun sample => first (edgeInputs edge sample)) (measure.map boundary))
    (secondIntegrable : ∀ edge, Integrable (fun sample => second (edgeInputs edge sample)) (measure.map boundary))
    (numeratorIntegrable : ∀ edge, Integrable (fun sample =>
      max (first (edgeInputs edge sample)-second (edgeInputs edge sample)) 0 *
        max 1 ((second (edgeInputs edge sample))⁻¹^2)) (measure.map boundary))
    {numerator denominator : ℝ} (numeratorNonnegative : 0 ≤ numerator) (denominatorPositive : 0 < denominator)
    (commonNumerator : ∀ edge, (∫ sample,
      max (first (edgeInputs edge sample)-second (edgeInputs edge sample)) 0 *
        max 1 ((second (edgeInputs edge sample))⁻¹^2) ∂measure.map boundary) = numerator)
    (commonDenominator : ∀ edge, (∫ sample,
      min (second (edgeInputs edge sample)) (second (edgeInputs edge sample))⁻¹ ∂measure.map boundary) = denominator) :
    ∀ᵐ sample ∂measure,
      measure[fun sample => max
        (electricalCell network (configuration (history sample)) (fun edge => first (edgeInputs edge (boundary sample)))-
          electricalCell network (configuration (history sample)) (fun edge => second (edgeInputs edge (boundary sample)))) 0 |
        (inferInstance : MeasurableSpace History).comap history] sample ≤
      (numerator/denominator) * measure[fun sample =>
        electricalCell network (configuration (history sample)) (fun edge => second (edgeInputs edge (boundary sample))) |
        (inferInstance : MeasurableSpace History).comap history] sample := by
  letI : IsProbabilityMeasure (measure.map boundary) := Measure.isProbabilityMeasure_map boundaryMeasurable.aemeasurable
  have firstResponseMeasurable : Measurable (fun data : History × Boundary =>
      electricalCell network (configuration data.1) (fun edge => first (edgeInputs edge data.2))) :=
    electricalCell_measurable network _ (configurationMeasurable.comp measurable_fst) _
      (measurable_pi_lambda _ (fun edge => (firstMeasurable.comp (inputsMeasurable edge)).comp measurable_snd))
      (fun data edge => (firstPositive _).le)
  have secondResponseMeasurable : Measurable (fun data : History × Boundary =>
      electricalCell network (configuration data.1) (fun edge => second (edgeInputs edge data.2))) :=
    electricalCell_measurable network _ (configurationMeasurable.comp measurable_fst) _
      (measurable_pi_lambda _ (fun edge => (secondMeasurable.comp (inputsMeasurable edge)).comp measurable_snd))
      (fun data edge => (secondPositive _).le)
  have firstActualIntegrable : Integrable (fun sample => electricalCell network (configuration (history sample))
      (fun edge => first (edgeInputs edge (boundary sample)))) measure := by
    apply electricalCell_random_integrable measure network _ (configurationMeasurable.comp historyMeasurable) _
      (measurable_pi_lambda _ (fun edge => (firstMeasurable.comp (inputsMeasurable edge)).comp boundaryMeasurable))
      (fun sample edge => firstPositive _)
    intro edge
    exact (integrable_map_measure (firstMeasurable.comp (inputsMeasurable edge)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mp (firstIntegrable edge)
  have secondActualIntegrable : Integrable (fun sample => electricalCell network (configuration (history sample))
      (fun edge => second (edgeInputs edge (boundary sample)))) measure := by
    apply electricalCell_random_integrable measure network _ (configurationMeasurable.comp historyMeasurable) _
      (measurable_pi_lambda _ (fun edge => (secondMeasurable.comp (inputsMeasurable edge)).comp boundaryMeasurable))
      (fun sample edge => secondPositive _)
    intro edge
    exact (integrable_map_measure (secondMeasurable.comp (inputsMeasurable edge)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mp (secondIntegrable edge)
  have firstConditional := independent_pair_condExp_eq_integral measure history boundary historyMeasurable boundaryMeasurable
    historyIndependent _ ((firstResponseMeasurable.sub secondResponseMeasurable).max measurable_const).stronglyMeasurable
    ((firstActualIntegrable.sub secondActualIntegrable).sup (integrable_const 0))
  have secondConditional := independent_pair_condExp_eq_integral measure history boundary historyMeasurable boundaryMeasurable
    historyIndependent _ secondResponseMeasurable.stronglyMeasurable secondActualIntegrable
  simp only [Pi.sub_apply] at firstConditional
  filter_upwards [firstConditional, secondConditional] with sample firstEquality secondEquality
  rw [firstEquality, secondEquality]
  exact electricalCell_independent_pair_integral_comparison (measure.map boundary) network (configuration (history sample))
    edgeInputs independent inputsMeasurable base first second firstMeasurable secondMeasurable firstPositive secondPositive
    firstIntegrable secondIntegrable numeratorIntegrable numeratorNonnegative denominatorPositive commonNumerator commonDenominator

end
end IGSIII34.Percolation


