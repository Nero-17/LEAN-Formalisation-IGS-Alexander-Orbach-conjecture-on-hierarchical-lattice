import IGSIII34.Diffusion.FiniteResolventCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def finiteMixedEnergyCompletion20261011 (endpoint : Edge → Vertex × Vertex) (first second : Vertex → ℝ) : ℝ :=
  ∑ edge, (first (endpoint edge).1 - first (endpoint edge).2) *
    (second (endpoint edge).1 - second (endpoint edge).2)

theorem laplacian_mixed_energy_completion20261011
    (endpoint : Edge → Vertex × Vertex) (potential test : Vertex → ℝ) :
    ∑ vertex, -laplacian endpoint potential vertex * test vertex =
      finiteMixedEnergyCompletion20261011 endpoint potential test := by
  classical
  simp only [laplacian, ← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold finiteMixedEnergyCompletion20261011
  apply Finset.sum_congr rfl
  intro edge _
  simp only [neg_add, add_mul, Finset.sum_add_distrib, neg_ite, neg_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem exact_degree_mixed_clock_completion20261011 [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (scale : ℝ) (potential test : Vertex → ℝ) :
    ∑ vertex, degreeWeight endpoint vertex *
      (-(2 * Fintype.card Edge * scale) * rateOneGenerator endpoint potential vertex) * test vertex =
      scale * finiteMixedEnergyCompletion20261011 endpoint potential test := by
  have cancellation (vertex : Vertex) : degreeWeight endpoint vertex *
      (-(2 * Fintype.card Edge * scale) * rateOneGenerator endpoint potential vertex) * test vertex =
      scale * (-laplacian endpoint potential vertex * test vertex) := by
    unfold degreeWeight rateOneGenerator
    field_simp [(positiveDegree vertex).ne']
    <;> ring
  simp_rw [cancellation]
  rw [← Finset.mul_sum, laplacian_mixed_energy_completion20261011]

/-- The true finite resolvent satisfies the full weak equation against
every vertex test, with the exact full-edge natural clock. -/
theorem finiteGraphResolvent_variational_completion20261011 [Nonempty Vertex] [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    parameter * (∑ vertex, degreeWeight endpoint vertex *
      finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale)
        parameterPositive (by positivity) forcing vertex * test vertex) +
      scale * finiteMixedEnergyCompletion20261011 endpoint
        (finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale)
          parameterPositive (by positivity) forcing) test =
      ∑ vertex, degreeWeight endpoint vertex * forcing vertex * test vertex := by
  let potential := finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale)
    parameterPositive (by positivity) forcing
  rw [← exact_degree_mixed_clock_completion20261011 endpoint positiveDegree scale potential test,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro vertex _
  have equationAt := congrFun (finiteGraphResolvent_equation endpoint positiveDegree parameter
    (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing) vertex
  rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equationAt
  rw [← equationAt]
  change parameter * (degreeWeight endpoint vertex * potential vertex * test vertex) +
    degreeWeight endpoint vertex * (-(2 * Fintype.card Edge * scale) * rateOneGenerator endpoint potential vertex) * test vertex =
    degreeWeight endpoint vertex * (parameter * potential vertex -
      (2 * Fintype.card Edge * scale) * rateOneGenerator endpoint potential vertex) * test vertex
  ring

end
end IGSIII34.Diffusion
