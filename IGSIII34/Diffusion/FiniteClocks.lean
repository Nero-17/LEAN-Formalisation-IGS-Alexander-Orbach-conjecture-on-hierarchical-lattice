import Universality.Graph.DirichletEnergy
import IGSIII.Geometry.FiniteMassTransport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact finite graph clocks, with individually indexed edges. Parallel edges
are counted with their multiplicity. No stochastic process existence is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def degree (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℝ :=
  ∑ edge, ((if (endpoint edge).1 = vertex then 1 else 0) +
    (if (endpoint edge).2 = vertex then 1 else 0))

def laplacian (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (vertex : Vertex) : ℝ :=
  ∑ edge, ((if (endpoint edge).1 = vertex then potential (endpoint edge).2 - potential vertex else 0) +
    (if (endpoint edge).2 = vertex then potential (endpoint edge).1 - potential vertex else 0))

def energy (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ) : ℝ :=
  ∑ edge, (potential (endpoint edge).1 - potential (endpoint edge).2) ^ 2

def degreeWeight (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℝ :=
  degree endpoint vertex / (2 * Fintype.card Edge)

theorem degree_nonnegative (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    0 ≤ degree endpoint vertex := by
  apply Finset.sum_nonneg
  intro edge _
  split_ifs <;> norm_num

theorem degree_sum (endpoint : Edge → Vertex × Vertex) :
    ∑ vertex, degree endpoint vertex = 2 * (Fintype.card Edge : ℝ) := by
  classical
  unfold degree
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib]
  ring

theorem degreeWeight_nonnegative (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) :
    0 ≤ degreeWeight endpoint vertex :=
  div_nonneg (degree_nonnegative endpoint vertex) (by positivity)

theorem degreeWeight_sum (endpoint : Edge → Vertex × Vertex) [Nonempty Edge] :
    ∑ vertex, degreeWeight endpoint vertex = 1 := by
  unfold degreeWeight
  rw [← Finset.sum_div, degree_sum, div_self]
  positivity

theorem degreeWeight_test (endpoint : Edge → Vertex × Vertex) (test : Vertex → ℝ) :
    ∑ vertex, degreeWeight endpoint vertex * test vertex =
      (∑ edge, (test (endpoint edge).1 + test (endpoint edge).2)) /
        (2 * Fintype.card Edge) := by
  classical
  simp only [degreeWeight, degree, Finset.sum_div, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp [add_mul, Finset.sum_add_distrib]

theorem laplacian_energy (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ) :
    ∑ vertex, -laplacian endpoint potential vertex * potential vertex = energy endpoint potential := by
  classical
  simp only [laplacian, ← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold energy
  apply Finset.sum_congr rfl
  intro edge _
  simp only [neg_add, add_mul, Finset.sum_add_distrib, neg_ite, neg_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

def rateOneGenerator (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (vertex : Vertex) : ℝ := laplacian endpoint potential vertex / degree endpoint vertex

def transition (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (vertex : Vertex) : ℝ := potential vertex + rateOneGenerator endpoint potential vertex

theorem transition_sub_identity (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (vertex : Vertex) : transition endpoint potential vertex - potential vertex =
      rateOneGenerator endpoint potential vertex := by
  simp [transition]

theorem rateOne_energy (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (potential : Vertex → ℝ) :
    ∑ vertex, degreeWeight endpoint vertex * (-rateOneGenerator endpoint potential vertex) * potential vertex =
      energy endpoint potential / (2 * Fintype.card Edge) := by
  simp only [degreeWeight, rateOneGenerator]
  have cancellation (vertex : Vertex) :
      degree endpoint vertex / (2 * Fintype.card Edge) *
        -(laplacian endpoint potential vertex / degree endpoint vertex) * potential vertex =
      (-laplacian endpoint potential vertex * potential vertex) / (2 * Fintype.card Edge) := by
    field_simp [(positiveDegree vertex).ne']
  simp_rw [cancellation]
  rw [← Finset.sum_div, laplacian_energy]

theorem exact_degree_clock (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (scale : ℝ) (potential : Vertex → ℝ)
    [Nonempty Edge] :
    ∑ vertex, degreeWeight endpoint vertex *
      (-(2 * Fintype.card Edge * scale * rateOneGenerator endpoint potential vertex)) * potential vertex =
        scale * energy endpoint potential := by
  have factor : (∑ vertex, degreeWeight endpoint vertex *
      (-(2 * Fintype.card Edge * scale * rateOneGenerator endpoint potential vertex)) * potential vertex) =
      (2 * Fintype.card Edge * scale) *
        ∑ vertex, degreeWeight endpoint vertex * (-rateOneGenerator endpoint potential vertex) * potential vertex := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro vertex _
    ring
  rw [factor, rateOne_energy endpoint positiveDegree]
  field_simp

theorem exact_counting_clock (endpoint : Edge → Vertex × Vertex) [Nonempty Vertex]
    (scale : ℝ) (potential : Vertex → ℝ) :
    ∑ vertex, (1 / (Fintype.card Vertex : ℝ)) *
      (-((Fintype.card Vertex : ℝ) * scale * laplacian endpoint potential vertex)) * potential vertex =
        scale * energy endpoint potential := by
  have cancellation (vertex : Vertex) :
      (1 / (Fintype.card Vertex : ℝ)) *
        (-((Fintype.card Vertex : ℝ) * scale * laplacian endpoint potential vertex)) * potential vertex =
      scale * (-laplacian endpoint potential vertex * potential vertex) := by
    field_simp
    <;> ring
  simp_rw [cancellation]
  rw [← Finset.mul_sum, laplacian_energy]

end
end IGSIII34.Diffusion
