import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory
open scoped MeasureTheory
variable {Outcome History : Type*} [MeasurableSpace Outcome] [MeasurableSpace History]

theorem conditional_expectation_eq_of_history_set_integrals_completion20261011
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : Outcome → History) (historyMeasurable : Measurable history)
    (function : Outcome → ℝ) (functionIntegrable : Integrable function law)
    (expectation : History → ℝ) (expectationMeasurable : StronglyMeasurable expectation)
    (expectationIntegrable : Integrable (fun outcome => expectation (history outcome)) law)
    (setIntegrals : ∀ retained : Set History, MeasurableSet retained →
      (∫ outcome in history ⁻¹' retained, function outcome ∂law) =
        ∫ outcome in history ⁻¹' retained, expectation (history outcome) ∂law) :
    law[function | (inferInstance : MeasurableSpace History).comap history] =ᵐ[law]
      fun outcome => expectation (history outcome) := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq historyMeasurable.comap_le functionIntegrable
  · intro retained _ _
    exact expectationIntegrable.integrableOn
  · rintro _ ⟨retained, measurable, rfl⟩ _
    exact (setIntegrals retained measurable).symm
  · exact (expectationMeasurable.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

end
end IGSIII34.Spectral
