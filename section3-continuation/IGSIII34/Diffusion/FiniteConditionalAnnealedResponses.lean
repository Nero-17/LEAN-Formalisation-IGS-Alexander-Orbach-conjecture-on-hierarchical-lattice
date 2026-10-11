import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal

/-- The actual finite configuration and starting vertex have only finitely
many values. Consequently every conditional response is measurable, and
quenched convergence gives a measurable limit and environment-weighted
annealed convergence without a measurable choice of common ambient spaces. -/
theorem finite_conditional_response_annealed
    {Environment : Type*} [MeasurableSpace Environment]
    (environmentLaw : Measure Environment) [IsProbabilityMeasure environmentLaw]
    (Configurations : ℕ → Type*) [∀ depth, Fintype (Configurations depth)]
    [∀ depth, MeasurableSpace (Configurations depth)]
    [∀ depth, MeasurableSingletonClass (Configurations depth)]
    (configuration : ∀ depth, Environment → Configurations depth)
    (configurationMeasurable : ∀ depth, Measurable (configuration depth))
    (response : ∀ depth, Configurations depth → ℝ)
    (bound : ℝ≥0) (bounded : ∀ depth input, ‖response depth input‖ ≤ bound)
    (limit : Environment → ℝ)
    (quenched : ∀ᵐ environment ∂environmentLaw,
      Tendsto (fun depth => response depth (configuration depth environment)) atTop (𝓝 (limit environment))) :
    AEMeasurable limit environmentLaw ∧
      ∀ (weight : Environment → ℝ), Measurable weight →
      ∀ (weightBound : ℝ≥0), (∀ environment, ‖weight environment‖ ≤ weightBound) →
      Tendsto (fun depth => ∫ environment,
        weight environment * response depth (configuration depth environment) ∂environmentLaw) atTop
        (𝓝 (∫ environment, weight environment * limit environment ∂environmentLaw)) := by
  have measurable (depth : ℕ) :
      Measurable (fun environment => response depth (configuration depth environment)) :=
    (measurable_of_finite (response depth)).comp (configurationMeasurable depth)
  refine ⟨aemeasurable_of_tendsto_metrizable_ae atTop (fun depth => (measurable depth).aemeasurable) quenched, ?_⟩
  intro weight weightMeasurable weightBound weightBounded
  apply tendsto_integral_of_dominated_convergence (fun _ => (weightBound : ℝ) * bound)
  · intro depth
    exact (weightMeasurable.mul (measurable depth)).aestronglyMeasurable
  · exact integrable_const _
  · intro depth
    exact Eventually.of_forall (fun environment => by
      rw [norm_mul]
      exact mul_le_mul (weightBounded environment) (bounded depth (configuration depth environment))
        (norm_nonneg _) weightBound.coe_nonneg)
  · filter_upwards [quenched] with environment convergence
    exact convergence.const_mul (weight environment)

end
end IGSIII34.Diffusion
