import IGSIII34.Diffusion.UniformQuadraticIntegralsCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
  [Fintype Edge] [Nonempty Edge]

theorem finiteResolventFunctional_integral_completion
    (endpoint : Edge → Vertex × Vertex) (parameter scale : ℝ) (forcing potential : Vertex → ℝ) :
    finiteResolventFunctionalCompletion endpoint parameter scale forcing potential =
      parameter * (∫ vertex, potential vertex ^ 2 ∂degreeMeasure endpoint) + scale * energy endpoint potential -
        2 * (∫ vertex, forcing vertex * potential vertex ∂degreeMeasure endpoint) := by
  rw [degreeMeasure_integral, degreeMeasure_integral]
  unfold finiteResolventFunctionalCompletion
  simp only [mul_assoc]

/-- Passage through actual finite degree integrals preserves the complete
Dirichlet objective, including its exact energy normalization. -/
theorem finite_objective_tendsto_completion
    {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    [∀ depth, Fintype (Edges depth)] [∀ depth, Nonempty (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (limitMeasure : ProbabilityMeasure Space) (placement : ∀ depth, Vertices depth → Space)
    (weak : Tendsto (fun depth =>
      ProbabilityMeasure.map (⟨degreeMeasure (endpoint depth), degreeMeasure_probability_completion (endpoint depth)⟩ : ProbabilityMeasure (Vertices depth))
        (measurable_of_finite (placement depth)).aemeasurable) atTop (𝓝 limitMeasure))
    (values : ∀ depth, Vertices depth → ℝ) (target forcing : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex - target (placement depth vertex)| < tolerance)
    (parameter : ℝ) (scale : ℕ → ℝ) (limitEnergy : ℝ)
    (energyLimit : Tendsto (fun depth => scale depth * energy (endpoint depth) (values depth)) atTop (𝓝 limitEnergy)) :
    Tendsto (fun depth => finiteResolventFunctionalCompletion (endpoint depth) parameter (scale depth)
        (fun vertex => forcing (placement depth vertex)) (values depth)) atTop
      (𝓝 (parameter * (∫ point, target point ^ 2 ∂limitMeasure) + limitEnergy -
        2 * (∫ point, forcing point * target point ∂limitMeasure))) := by
  have integrals := uniform_finite_quadratic_integrals_completion Vertices
    (fun depth => ⟨degreeMeasure (endpoint depth), degreeMeasure_probability_completion (endpoint depth)⟩)
    limitMeasure placement weak values target forcing uniform
  have convergence := ((integrals.1.const_mul parameter).add energyLimit).sub (integrals.2.const_mul 2)
  simpa only [finiteResolventFunctional_integral_completion, ProbabilityMeasure.coe_mk] using convergence

/-- The real finite resolvent minimum passes to a limit comparison. Sharp
energy lower bounds can subsequently replace the original limiting energy. -/
theorem finite_resolvent_limit_comparison_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, DecidableEq (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, Fintype (Edges depth)] [∀ depth, Nonempty (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (parameter : ℝ) (scale : ℕ → ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : ∀ depth, 0 ≤ scale depth)
    (forcing tests : ∀ depth, Vertices depth → ℝ) (candidateObjective testObjective : ℝ)
    (candidateLimit : Tendsto (fun depth => finiteResolventFunctionalCompletion (endpoint depth) parameter (scale depth)
        (forcing depth) (finiteGraphResolvent (endpoint depth) (positiveDegree depth) parameter
          (2 * Fintype.card (Edges depth) * scale depth) parameterPositive (by have := scaleNonnegative depth; positivity) (forcing depth))) atTop (𝓝 candidateObjective))
    (testLimit : Tendsto (fun depth => finiteResolventFunctionalCompletion (endpoint depth) parameter (scale depth)
        (forcing depth) (tests depth)) atTop (𝓝 testObjective)) : candidateObjective ≤ testObjective := by
  exact le_of_tendsto_of_tendsto candidateLimit testLimit (Eventually.of_forall fun depth =>
    finiteGraphResolvent_minimizes_completion (endpoint depth) (positiveDegree depth)
      parameter (scale depth) parameterPositive (scaleNonnegative depth) (forcing depth) (tests depth))

end
end IGSIII34.Diffusion


