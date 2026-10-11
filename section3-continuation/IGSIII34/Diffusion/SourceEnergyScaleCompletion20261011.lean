import IGSIII34.ResistanceLimit.SourceEnergy
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false

namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped BigOperators _root_.Topology

/-- A constant inverse resistance is exactly the clock-normalized original
unit-edge energy, including the full retained source component. -/
theorem sourceEnergy_constant_inverse_scale_completion20261011
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (scale : ℝ) (potential : Vertex → ℝ) :
    sourceComponentEnergy network (fun _ => scale⁻¹) potential =
      scale * sourceComponentEnergy network (fun _ => 1) potential := by
  classical
  unfold sourceComponentEnergy finiteEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases reachable : network.graph.Reachable network.source (network.endpoint edge).1
  · simp only [if_pos reachable, inv_inv, inv_one, one_mul]
  · simp only [if_neg reachable, zero_mul, mul_zero]

theorem convergent_nonnegative_uniform_upper_completion20261011
    (sequence : ℕ → ℝ) (limit : ℝ) (convergence : Tendsto sequence atTop (𝓝 limit)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, sequence index ≤ bound := by
  obtain ⟨bound, bounded⟩ := convergence.bddAbove_range
  refine ⟨max bound 0, le_max_right _ _, fun index => ?_⟩
  exact (bounded (Set.mem_range_self index)).trans (le_max_left _ _)

end
end IGSIII34.Diffusion
