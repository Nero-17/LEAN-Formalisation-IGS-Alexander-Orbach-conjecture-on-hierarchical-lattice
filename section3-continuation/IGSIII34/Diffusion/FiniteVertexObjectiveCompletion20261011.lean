import IGSIII34.Diffusion.FiniteVertexResolventCompletion20261011
import IGSIII34.Diffusion.FiniteResolventMinimumCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]
  [Nonempty Vertex] [Nonempty Edge]

theorem finiteVertexResolvent_auxiliary_clock_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale) (forcing : Vertex → ℝ) :
    finiteVertexResolventCompletion20261011 endpoint parameter scale parameterPositive scaleNonnegative forcing =
      finiteGraphResolvent (finiteRegularizedEndpointCompletion20261011 endpoint)
        (finiteRegularized_degree_positive_completion20261011 endpoint) parameter
        (2 * Fintype.card (FiniteRegularizedEdgeCompletion20261011 endpoint) * (scale / 2))
        parameterPositive (by positivity) forcing := by
  have clock : (Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale =
      2 * Fintype.card (FiniteRegularizedEdgeCompletion20261011 endpoint) * (scale / 2) := by
    rw [finiteRegularized_card_completion20261011]
    ring
  unfold finiteVertexResolventCompletion20261011
  congr 1

def finiteVertexResolventFunctionalCompletion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) : ℝ :=
  parameter * (∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * potential vertex ^ 2) +
    scale * energy endpoint potential - 2 * ∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * forcing vertex * potential vertex

theorem finiteVertexResolventFunctional_auxiliary_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) :
    finiteVertexResolventFunctionalCompletion20261011 endpoint parameter scale forcing potential =
      finiteResolventFunctionalCompletion20261011 (finiteRegularizedEndpointCompletion20261011 endpoint)
        parameter (scale / 2) forcing potential := by
  unfold finiteVertexResolventFunctionalCompletion20261011 finiteResolventFunctionalCompletion20261011
  simp only [finiteRegularized_degreeWeight_completion20261011, finiteRegularized_energy_completion20261011]
  ring

theorem finiteVertexResolvent_minimizes_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    finiteVertexResolventFunctionalCompletion20261011 endpoint parameter scale forcing
      (finiteVertexResolventCompletion20261011 endpoint parameter scale parameterPositive scaleNonnegative forcing) ≤
      finiteVertexResolventFunctionalCompletion20261011 endpoint parameter scale forcing test := by
  rw [finiteVertexResolventFunctional_auxiliary_completion20261011,
    finiteVertexResolventFunctional_auxiliary_completion20261011,
    finiteVertexResolvent_auxiliary_clock_completion20261011]
  exact finiteGraphResolvent_minimizes_completion20261011 (finiteRegularizedEndpointCompletion20261011 endpoint)
    (finiteRegularized_degree_positive_completion20261011 endpoint) parameter (scale / 2)
    parameterPositive (by positivity) forcing test

theorem finiteVertexResolvent_scaled_energy_bound_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    scale * energy endpoint (finiteVertexResolventCompletion20261011 endpoint parameter scale parameterPositive scaleNonnegative forcing) ≤
      bound ^ 2 / parameter := by
  have auxiliary := finiteGraphResolvent_scaled_energy_bound (finiteRegularizedEndpointCompletion20261011 endpoint)
    (finiteRegularized_degree_positive_completion20261011 endpoint) parameter (scale / 2)
    parameterPositive (by positivity) forcing bound boundNonnegative forcingBound
  rw [← finiteVertexResolvent_auxiliary_clock_completion20261011 endpoint parameter scale parameterPositive scaleNonnegative forcing, finiteRegularized_energy_completion20261011] at auxiliary
  convert auxiliary using 1 <;> ring

theorem finiteVertexResolvent_generator_bound_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |(Fintype.card Vertex : ℝ) * scale * laplacian endpoint
      (finiteVertexResolventCompletion20261011 endpoint parameter scale parameterPositive scaleNonnegative forcing) vertex| ≤ 2 * bound := by
  have auxiliary := finiteGraphResolvent_generator_bound (finiteRegularizedEndpointCompletion20261011 endpoint)
    (finiteRegularized_degree_positive_completion20261011 endpoint) parameter
    ((Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale) parameterPositive (by positivity) forcing bound forcingBound
  simpa only [finiteRegularized_natural_generator_completion20261011, finiteVertexResolventCompletion20261011] using auxiliary

end
end IGSIII34.Diffusion

