import IGSIII34.Diffusion.FiniteVertexUniformizationCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

theorem finiteRegularized_card_completion (endpoint : Edge → Vertex × Vertex) :
    (Fintype.card (FiniteRegularizedEdgeCompletion endpoint) : ℝ) =
      (Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) := by
  have identity := degree_sum (finiteRegularizedEndpointCompletion endpoint)
  simp only [finiteRegularized_degree_completion, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at identity
  nlinarith

theorem finiteRegularized_degree_positive_completion [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    0 < degree (finiteRegularizedEndpointCompletion endpoint) vertex := by
  rw [finiteRegularized_degree_completion]
  positivity

theorem finiteRegularized_degreeWeight_completion [Nonempty Vertex] [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    degreeWeight (finiteRegularizedEndpointCompletion endpoint) vertex =
      1 / (Fintype.card Vertex : ℝ) := by
  unfold degreeWeight
  rw [finiteRegularized_degree_completion, finiteRegularized_card_completion]
  field_simp
  <;> ring

theorem finiteRegularized_generator_completion [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ) (vertex : Vertex) :
    rateOneGenerator (finiteRegularizedEndpointCompletion endpoint) potential vertex =
      laplacian endpoint potential vertex / (2 * Fintype.card Edge) := by
  unfold rateOneGenerator
  rw [finiteRegularized_degree_completion, finiteRegularized_laplacian_completion]
  field_simp
  <;> ring

theorem finiteRegularized_natural_generator_completion [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (scale : ℝ) (potential : Vertex → ℝ) (vertex : Vertex) :
    ((Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale) *
      rateOneGenerator (finiteRegularizedEndpointCompletion endpoint) potential vertex =
      (Fintype.card Vertex : ℝ) * scale * laplacian endpoint potential vertex := by
  rw [finiteRegularized_generator_completion]
  field_simp

variable [Nonempty Vertex] [Nonempty Edge]

def finiteVertexResolventCompletion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) : Vertex → ℝ :=
  finiteGraphResolvent (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter
    ((Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale) parameterPositive (by positivity) forcing

theorem finiteVertexResolvent_equation_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (vertex : Vertex) :
    parameter * finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing vertex -
      (Fintype.card Vertex : ℝ) * scale * laplacian endpoint
        (finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing) vertex = forcing vertex := by
  have equation := congrFun (finiteGraphResolvent_equation (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter
    ((Fintype.card Vertex : ℝ) * (2 * Fintype.card Edge) * scale) parameterPositive (by positivity) forcing) vertex
  rw [finiteGraphResolventOperator_apply _ (finiteRegularized_degree_positive_completion endpoint),
    finiteRegularized_natural_generator_completion] at equation
  exact equation

theorem finiteVertexResolvent_supremum_bound_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing : Vertex → ℝ) (bound : ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ bound) :
    ∀ vertex, |finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing vertex| ≤
      bound / parameter :=
  finiteGraphResolvent_supremum_bound (finiteRegularizedEndpointCompletion endpoint)
    (finiteRegularized_degree_positive_completion endpoint) parameter _ parameterPositive (by positivity) forcing bound forcingBound

theorem finiteVertexResolvent_variational_completion (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    parameter * (∑ vertex, (1 / (Fintype.card Vertex : ℝ)) *
      finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing vertex * test vertex) +
      scale * finiteMixedEnergyCompletion endpoint
        (finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing) test =
      ∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * forcing vertex * test vertex := by
  let potential := finiteVertexResolventCompletion endpoint parameter scale parameterPositive scaleNonnegative forcing
  have mixed : (∑ vertex, (1 / (Fintype.card Vertex : ℝ)) *
      (-((Fintype.card Vertex : ℝ) * scale) * laplacian endpoint potential vertex) * test vertex) =
      scale * finiteMixedEnergyCompletion endpoint potential test := by
    rw [← laplacian_mixed_energy_completion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vertex member
    field_simp
    <;> ring
  rw [← mixed, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro vertex member
  have equation := finiteVertexResolvent_equation_completion endpoint parameter scale parameterPositive scaleNonnegative forcing vertex
  change parameter * (1 / (Fintype.card Vertex : ℝ) * potential vertex * test vertex) +
    1 / (Fintype.card Vertex : ℝ) * (-((Fintype.card Vertex : ℝ) * scale) * laplacian endpoint potential vertex) * test vertex = _
  rw [← equation]
  ring

end
end IGSIII34.Diffusion
