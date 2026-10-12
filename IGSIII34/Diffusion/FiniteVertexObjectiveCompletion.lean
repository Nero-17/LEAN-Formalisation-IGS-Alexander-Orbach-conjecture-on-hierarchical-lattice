import IGSIII34.Diffusion.FiniteVertexResolventCompletion
import IGSIII34.Diffusion.FiniteResolventMinimumCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]
  [Nonempty Vertex] [Nonempty Edge]

theorem finiteVertexResolvent_auxiliary_clock_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale) (forcing : Vertex → ℝ) :
    finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing =
      finiteGraphResolvent (finiteRegularizedEndpointCompletion endpoint)
        (finiteRegularized_degree_positive_completion endpoint) parameter
        (2 * Fintype.card (FiniteRegularizedEdgeCompletion endpoint) * (scale / 2))
        parameterPositive (by positivity) forcing := by
  have clock : (Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale =
      2 * Fintype.card (FiniteRegularizedEdgeCompletion endpoint) * (scale / 2) := by
    rw [finiteRegularized_card_completion]
    ring
  unfold finiteVertexResolventCompletion
  congr 1

def finiteVertexResolventFunctionalCompletion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) : ℝ :=
  parameter * (∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * potential vertex ^ 2) +
    scale * energy endpoint potential - 2 * ∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * forcing vertex * potential vertex

theorem finiteVertexResolventFunctional_auxiliary_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) :
    finiteVertexResolventFunctionalCompletion endpoint parameter scale forcing potential =
      finiteResolventFunctionalCompletion (finiteRegularizedEndpointCompletion endpoint)
        parameter (scale / 2) forcing potential := by
  unfold finiteVertexResolventFunctionalCompletion finiteResolventFunctionalCompletion
  simp only [finiteRegularized_degreeWeight_completion, finiteRegularized_energy_completion]
  ring

theorem finiteVertexResolvent_minimizes_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    finiteVertexResolventFunctionalCompletion endpoint parameter scale forcing
      (finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing) ≤
      finiteVertexResolventFunctionalCompletion endpoint parameter scale forcing test := by
  rw [finiteVertexResolventFunctional_auxiliary_completion,
    finiteVertexResolventFunctional_auxiliary_completion,
    finiteVertexResolvent_auxiliary_clock_completion]
  exact finiteGraphResolvent_minimizes_completion (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter (scale / 2)
    parameterPositive (by positivity) forcing test

theorem finiteVertexResolvent_scaled_energy_bound_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    scale * energy endpoint (finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing) ≤
      bound ^ 2 / parameter := by
  have auxiliary := finiteGraphResolvent_scaled_energy_bound (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter (scale / 2)
    parameterPositive (by positivity) forcing bound boundNonnegative forcingBound
  rw [← finiteVertexResolvent_auxiliary_clock_completion endpoint parameter scale parameterPositive scaleNonnegative forcing, finiteRegularized_energy_completion] at auxiliary
  convert auxiliary using 1 <;> ring

theorem finiteVertexResolvent_generator_bound_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |(Fintype.card Vertex : ℝ) * scale * laplacian endpoint
      (finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing) vertex| ≤ 2 * bound := by
  have auxiliary := finiteGraphResolvent_generator_bound (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter
    ((Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale) parameterPositive (by positivity) forcing bound forcingBound
  simpa only [finiteRegularized_natural_generator_completion, finiteVertexResolventCompletion] using auxiliary

end
end IGSIII34.Diffusion

