import Universality.Graph.VolumeLimit
import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section

theorem Classical.generation_volume_uniform_bound {rule : Rule} (h : rule.Classical) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n, ((rule.generation n).vertices : ℝ) ≤ bound * (rule.edges : ℝ) ^ n := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast h.edges_gt_one
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast h.vertices_gt_two
  let coefficient : ℝ := ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)
  have hcoefficient : 0 < coefficient := div_pos (sub_pos.mpr hv) (sub_pos.mpr hm)
  refine ⟨(2 + coefficient) * rule.edges, by positivity, ?_⟩
  intro n
  rw [rule.generation_volume_formula n (by have := h.edges_gt_one; omega)]
  have hpower := one_le_pow₀ (n := n + 1) hm.le
  calc
    _ = 2 + coefficient * ((rule.edges : ℝ) ^ (n + 1) - 1) := by dsimp [coefficient]; ring
    _ ≤ (2 + coefficient) * (rule.edges : ℝ) ^ (n + 1) := by nlinarith
    _ = _ := by rw [pow_succ]; ring

end
end Universality.Rule
