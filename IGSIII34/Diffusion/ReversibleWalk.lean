import IGSIII34.Diffusion.FiniteClocks

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def edgeMultiplicity (endpoint : Edge → Vertex × Vertex) (first last : Vertex) : ℝ :=
  ∑ edge, ((if endpoint edge = (first, last) then 1 else 0) +
    (if endpoint edge = (last, first) then 1 else 0))

def transitionKernel (endpoint : Edge → Vertex × Vertex) (first last : Vertex) : ℝ :=
  edgeMultiplicity endpoint first last / degree endpoint first

theorem edgeMultiplicity_symmetric (endpoint : Edge → Vertex × Vertex) (first last : Vertex) :
    edgeMultiplicity endpoint first last = edgeMultiplicity endpoint last first := by
  simp only [edgeMultiplicity, add_comm]

theorem edgeMultiplicity_sum (endpoint : Edge → Vertex × Vertex) (first : Vertex) :
    ∑ last, edgeMultiplicity endpoint first last = degree endpoint first := by
  classical
  unfold edgeMultiplicity degree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [Prod.ext_iff, Finset.sum_add_distrib]
  by_cases firstEndpoint : (endpoint edge).1 = first <;>
    by_cases lastEndpoint : (endpoint edge).2 = first <;>
    simp [firstEndpoint, lastEndpoint]

theorem transitionKernel_nonnegative (endpoint : Edge → Vertex × Vertex) (first last : Vertex) :
    0 ≤ transitionKernel endpoint first last := by
  apply div_nonneg _ (degree_nonnegative endpoint first)
  apply Finset.sum_nonneg
  intro edge _
  split_ifs <;> norm_num

theorem transitionKernel_sum (endpoint : Edge → Vertex × Vertex) (first : Vertex)
    (positive : 0 < degree endpoint first) :
    ∑ last, transitionKernel endpoint first last = 1 := by
  simp only [transitionKernel, ← Finset.sum_div, edgeMultiplicity_sum, div_self positive.ne']

theorem detailed_balance (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (first last : Vertex) :
    degreeWeight endpoint first * transitionKernel endpoint first last =
      degreeWeight endpoint last * transitionKernel endpoint last first := by
  unfold degreeWeight transitionKernel
  rw [edgeMultiplicity_symmetric endpoint first last]
  field_simp [(positiveDegree first).ne', (positiveDegree last).ne']

theorem degree_stationary (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (last : Vertex) :
    ∑ first, degreeWeight endpoint first * transitionKernel endpoint first last = degreeWeight endpoint last := by
  simp_rw [detailed_balance endpoint positiveDegree]
  rw [← Finset.mul_sum, transitionKernel_sum endpoint last (positiveDegree last), mul_one]

theorem kernel_laplacian (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (first : Vertex) :
    ∑ last, edgeMultiplicity endpoint first last * (potential last - potential first) =
      laplacian endpoint potential first := by
  classical
  unfold edgeMultiplicity laplacian
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [Prod.ext_iff, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  by_cases firstEndpoint : (endpoint edge).1 = first <;>
    by_cases lastEndpoint : (endpoint edge).2 = first <;>
    simp [firstEndpoint, lastEndpoint]

/-- The actual finite transition operator agrees with the incident-edge
average; consequently the clocks in `FiniteClocks` apply to this reversible
discrete walk rather than only to an abstract quadratic expression. -/
theorem transition_eq_kernel (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (first : Vertex) :
    transition endpoint potential first = ∑ last, transitionKernel endpoint first last * potential last := by
  have difference := kernel_laplacian endpoint potential first
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, edgeMultiplicity_sum] at difference
  unfold transition rateOneGenerator transitionKernel
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [← difference]
  field_simp [(positiveDegree first).ne']
  <;> ring

end
end IGSIII34.Diffusion
