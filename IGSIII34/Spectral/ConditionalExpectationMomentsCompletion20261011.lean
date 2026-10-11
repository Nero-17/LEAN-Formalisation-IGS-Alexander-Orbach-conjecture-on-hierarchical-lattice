import Mathlib.Probability.Kernel.CondDistrib

/-! A proved scalar conditional-expectation identity yields the matching
moment of the genuine regular conditional distribution. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

variable {Outcome History Space : Type*}
  [MeasurableSpace Outcome] [MeasurableSpace History] [MeasurableSpace Space]
  [StandardBorelSpace Space] [Nonempty Space]

theorem conditional_distribution_moment_of_conditional_expectation_completion20261011
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : Outcome → History) (historyMeasurable : Measurable history)
    (future : Outcome → Space) (futureMeasurable : AEMeasurable future law)
    (function : Space → ℝ) (functionMeasurable : StronglyMeasurable function)
    (functionIntegrable : Integrable (fun outcome => function (future outcome)) law)
    (expectation : History → ℝ) (expectationMeasurable : Measurable expectation)
    (identity : law[fun outcome => function (future outcome) | (inferInstance : MeasurableSpace History).comap history] =ᵐ[law]
      (fun outcome => expectation (history outcome))) :
    (fun retained => ∫ other, function other ∂condDistrib future history law retained) =ᵐ[law.map history]
      expectation := by
  have integrationMeasurable : Measurable (fun retained => ∫ other, function other ∂condDistrib future history law retained) :=
    (functionMeasurable.integral_kernel (κ := condDistrib future history law)).measurable
  apply (ae_map_iff historyMeasurable.aemeasurable
    (measurableSet_eq_fun integrationMeasurable expectationMeasurable)).mpr
  exact (condExp_ae_eq_integral_condDistrib historyMeasurable futureMeasurable
    functionMeasurable functionIntegrable).symm.trans identity

end
end IGSIII34.Spectral
