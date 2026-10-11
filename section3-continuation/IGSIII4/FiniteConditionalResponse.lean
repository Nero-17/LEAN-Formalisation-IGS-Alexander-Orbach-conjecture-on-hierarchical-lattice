import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory ProbabilityTheory

/-- Conditioning a finite choice of integrable responses to an independent input.
The choice may depend on the entire conditioning sigma algebra. -/
theorem condExp_finite_independent_response
    {Sample Label Input : Type*} [ambient : MeasurableSpace Sample]
    [Fintype Label] [labelSpace : MeasurableSpace Label] [MeasurableSingletonClass Label]
    [inputSpace : MeasurableSpace Input] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (information : MeasurableSpace Sample) (within : information ≤ ambient)
    (state : Sample → Label) (stateMeasurable : Measurable[information] state)
    (input : Sample → Input) (inputMeasurable : @Measurable Sample Input ambient inputSpace input)
    (independent : Indep (MeasurableSpace.comap input inputSpace) information measure)
    (response : Label → Input → ℝ) (responseMeasurable : ∀ label, Measurable (response label))
    (responseIntegrable : ∀ label, Integrable (fun sample => response label (input sample)) measure) :
    condExp information measure (fun sample => response (state sample) (input sample))
      =ᵐ[measure] fun sample => ∫ other, response (state sample) (input other) ∂measure := by
  classical
  have eventsMeasurable (label : Label) : MeasurableSet[information] {sample | state sample = label} :=
    stateMeasurable (measurableSet_singleton label)
  have inputInformation : @Measurable Sample Input (MeasurableSpace.comap input inferInstance)
      inferInstance input := measurable_iff_comap_le.mpr le_rfl
  have conditionalResponse (label : Label) :
      condExp information measure (fun sample => response label (input sample)) =ᵐ[measure]
        fun _ => ∫ sample, response label (input sample) ∂measure :=
    condExp_indep_eq inputMeasurable.comap_le within
      ((responseMeasurable label).comp inputInformation).stronglyMeasurable independent
  have indicatorsIntegrable (label : Label) :
      Integrable ({sample | state sample = label}.indicator
        (fun sample => response label (input sample))) measure :=
    (responseIntegrable label).indicator (within _ (eventsMeasurable label))
  have decomposition : (fun sample => response (state sample) (input sample)) =
      fun sample => ∑ label, {sample | state sample = label}.indicator
        (fun sample => response label (input sample)) sample := by
    funext sample
    simp [Set.indicator_apply, eq_comm]
  rw [decomposition]
  have sumConditional := condExp_finsetSum (m := information)
    (s := Finset.univ) (fun label _ => indicatorsIntegrable label)
  simp only [Finset.sum_fn] at sumConditional
  have indicatorConditional (label : Label) :=
    condExp_indicator (responseIntegrable label) (eventsMeasurable label)
  filter_upwards [sumConditional, ae_all_iff.mpr conditionalResponse,
    ae_all_iff.mpr indicatorConditional] with sample sumIdentity responses indicators
  refine sumIdentity.trans ?_
  calc
    _ = ∑ label, if state sample = label then
        (∫ other, response label (input other) ∂measure) else 0 := by
      apply Finset.sum_congr rfl
      intro label _
      rw [indicators label]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, responses label]
    _ = _ := by simp [eq_comm]

end
end IGSIII4
