import IGSIII34.Diffusion.SpectralCorrectorGeneratorCompletion
import IGSIII34.Diffusion.UniformQuadraticIntegralsCompletion

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped _root_.Topology
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

/-- Recentring the true finite corrector generator yields the exact
perturbed Euler equation around the corrected potential itself. -/
theorem finite_resolvent_corrector_euler_equation_completion [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (acceleration : ℝ) (accelerationNonnegative : 0 ≤ acceleration)
    (eigenvalue : ℝ) (eigenfunction : Vertex → ℝ) (vertex : Vertex) :
    acceleration * rateOneGenerator endpoint
      (finiteGraphResolvent endpoint positiveDegree 1 acceleration (by norm_num) accelerationNonnegative
        (fun vertex => (1 + eigenvalue) * eigenfunction vertex)) vertex =
      -eigenvalue * finiteGraphResolvent endpoint positiveDegree 1 acceleration (by norm_num) accelerationNonnegative
        (fun vertex => (1 + eigenvalue) * eigenfunction vertex) vertex +
      (1 + eigenvalue) * (finiteGraphResolvent endpoint positiveDegree 1 acceleration (by norm_num) accelerationNonnegative
        (fun vertex => (1 + eigenvalue) * eigenfunction vertex) vertex - eigenfunction vertex) := by
  rw [finite_resolvent_corrector_generator_completion]
  ring

/-- The exact Euler forcing error vanishes uniformly whenever the genuine
finite correctors converge uniformly. -/
theorem uniform_corrector_euler_error_completion
    {Space : Type*} (Vertices : ℕ → Type*) (placement : ∀ depth, Vertices depth → Space)
    (eigenfunction : Space → ℝ) (eigenvalue : ℝ) (correctors : ∀ depth, Vertices depth → ℝ)
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |correctors depth vertex - eigenfunction (placement depth vertex)| < tolerance) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |(1 + eigenvalue) * (correctors depth vertex - eigenfunction (placement depth vertex))| < tolerance := by
  intro tolerance positive
  have factorPositive : 0 < |1 + eigenvalue| + 1 := by positivity
  filter_upwards [uniform (tolerance / (|1 + eigenvalue| + 1)) (by positivity)] with depth close
  intro vertex
  rw [abs_mul]
  have factorBound : |1 + eigenvalue| ≤ |1 + eigenvalue| + 1 := by linarith
  exact (mul_le_mul_of_nonneg_right factorBound (abs_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left (close vertex) factorPositive).trans_eq (mul_div_cancel₀ tolerance (ne_of_gt factorPositive)))

end
end IGSIII34.Diffusion
