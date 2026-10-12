import IGSIII34.Diffusion.FiniteResolventCompletion

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped _root_.Topology
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

/-- Exact spectral-core correctors use the genuine finite resolvent. Their
accelerated generator is the corrected potential minus its actual forcing. -/
theorem finite_resolvent_corrector_generator_completion [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (acceleration : ℝ) (accelerationNonnegative : 0 ≤ acceleration)
    (eigenvalue : ℝ) (eigenfunction : Vertex → ℝ) (vertex : Vertex) :
    acceleration * rateOneGenerator endpoint
      (finiteGraphResolvent endpoint positiveDegree 1 acceleration (by norm_num) accelerationNonnegative
        (fun vertex => (1 + eigenvalue) * eigenfunction vertex)) vertex =
      finiteGraphResolvent endpoint positiveDegree 1 acceleration (by norm_num) accelerationNonnegative
        (fun vertex => (1 + eigenvalue) * eigenfunction vertex) vertex - (1 + eigenvalue) * eigenfunction vertex := by
  have equation := congrFun (finiteGraphResolvent_equation endpoint positiveDegree 1 acceleration (by norm_num)
    accelerationNonnegative (fun vertex => (1 + eigenvalue) * eigenfunction vertex)) vertex
  rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equation
  linarith

/-- Uniform corrector convergence gives uniform generator convergence on
all original finite vertices; no limiting martingale or process is assumed. -/
theorem uniform_corrector_generator_completion
    {Space : Type*} (Vertices : ℕ → Type*) (placement : ∀ depth, Vertices depth → Space)
    (eigenfunction : Space → ℝ) (eigenvalue : ℝ)
    (correctors generators : ∀ depth, Vertices depth → ℝ)
    (equation : ∀ depth vertex, generators depth vertex = correctors depth vertex -
      (1 + eigenvalue) * eigenfunction (placement depth vertex))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |correctors depth vertex - eigenfunction (placement depth vertex)| < tolerance) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |generators depth vertex + eigenvalue * eigenfunction (placement depth vertex)| < tolerance := by
  intro tolerance positive
  filter_upwards [uniform tolerance positive] with depth close
  intro vertex
  rw [equation]
  have identity : correctors depth vertex - (1 + eigenvalue) * eigenfunction (placement depth vertex) +
      eigenvalue * eigenfunction (placement depth vertex) = correctors depth vertex - eigenfunction (placement depth vertex) := by ring
  rw [identity]
  exact close vertex

end
end IGSIII34.Diffusion
