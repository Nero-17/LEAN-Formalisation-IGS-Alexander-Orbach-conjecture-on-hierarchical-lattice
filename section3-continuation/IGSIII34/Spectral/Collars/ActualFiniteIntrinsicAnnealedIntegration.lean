import IGSIII34.Spectral.Collars.ActualFiniteIntrinsicJointResponse
import IGSIII34.Diffusion.FiniteConditionalAnnealedResponses

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.Diffusion MeasureTheory Filter
open scoped _root_.Topology NNReal

/-- A finite intrinsic response limit is selected from actual almost-sure
convergence; its measurability follows from the finite environment data. -/
theorem actualFiniteIntrinsicJointResponse_annealed_of_ae_exists
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (scale : ℝ) (scalePositive : 0 < scale)
    (test : IntrinsicJointGHPPathTest)
    (clock : ∀ depth, Configuration (rule.generation depth).edges → ℝ) (kind : Fin 3)
    (initial : ∀ depth, ((List (Fin rule.edges) × Bool) → Configuration rule.edges) →
      Fin (rule.generation depth).vertices)
    (initialMeasurable : ∀ depth, Measurable (initial depth))
    (converges : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ limit : ℝ, Tendsto (fun depth => actualFiniteIntrinsicJointResponse rule scale scalePositive depth test
        (clock depth) kind (markedGenerationConfiguration rule marks depth [] true, initial depth marks))
        atTop (𝓝 limit)) :
    ∃ limit : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ,
      AEMeasurable limit (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        Tendsto (fun depth => actualFiniteIntrinsicJointResponse rule scale scalePositive depth test
          (clock depth) kind (markedGenerationConfiguration rule marks depth [] true, initial depth marks))
          atTop (𝓝 (limit marks))) ∧
      ∀ (weight : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
        Measurable weight → ∀ weightBound : ℝ≥0, (∀ marks, ‖weight marks‖ ≤ weightBound) →
        Tendsto (fun depth => ∫ marks, weight marks * actualFiniteIntrinsicJointResponse rule scale scalePositive depth
          test (clock depth) kind (markedGenerationConfiguration rule marks depth [] true, initial depth marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) atTop
          (𝓝 (∫ marks, weight marks * limit marks ∂independentInnovationLaw rule p positive belowOne fixedPoint)) := by
  classical
  let limit := fun marks => if existsLimit : ∃ value : ℝ,
      Tendsto (fun depth => actualFiniteIntrinsicJointResponse rule scale scalePositive depth test
        (clock depth) kind (markedGenerationConfiguration rule marks depth [] true, initial depth marks))
        atTop (𝓝 value) then existsLimit.choose else 0
  have quenched : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => actualFiniteIntrinsicJointResponse rule scale scalePositive depth test
        (clock depth) kind (markedGenerationConfiguration rule marks depth [] true, initial depth marks))
        atTop (𝓝 (limit marks)) := by
    filter_upwards [converges] with marks existsLimit
    simpa only [limit, dif_pos existsLimit] using existsLimit.choose_spec
  obtain ⟨measurable, annealed⟩ := finite_conditional_response_annealed
    (independentInnovationLaw rule p positive belowOne fixedPoint)
    (fun depth => Configuration (rule.generation depth).edges × Fin (rule.generation depth).vertices)
    (fun depth marks => (markedGenerationConfiguration rule marks depth [] true, initial depth marks))
    (fun depth => (markedGenerationConfiguration_measurable rule depth [] true).prodMk (initialMeasurable depth))
    (fun depth => actualFiniteIntrinsicJointResponse rule scale scalePositive depth test (clock depth) kind)
    test.bound (fun depth input => actualFiniteIntrinsicJointResponse_bound rule scale scalePositive depth test
      (clock depth) kind input) limit quenched
  exact ⟨limit, measurable, quenched, annealed⟩

end
end IGSIII34.Spectral
