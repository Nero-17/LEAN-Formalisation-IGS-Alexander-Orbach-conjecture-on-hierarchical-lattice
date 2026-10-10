import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 400000

/-- Uniform elementary volume bounds for the actual finite substitution
graphs; their internal vertex count alone already has the full edge scale. -/
theorem Classical.generation_volume_bounds {rule : Rule} (h : rule.Classical) (n : ℕ) :
    rule.edges ^ n ≤ Fintype.card (rule.generation n).network.InteriorVertex ∧
      (rule.generation n).vertices ≤ 2 * rule.vertices * rule.edges ^ n := by
  have hedges : 2 ≤ rule.edges := h.edges_gt_one
  have hvertices : 3 ≤ rule.vertices := h.vertices_gt_two
  have hgeometric : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), rule.edges ^ k) ≤ 2 * rule.edges ^ n := by
    intro depth
    induction depth with
    | zero => simp
    | succ depth ih =>
        rw [Finset.sum_range_succ]
        have hstep : 2 * rule.edges ^ depth ≤ rule.edges ^ (depth + 1) := by
          rw [pow_succ]
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (rule.edges ^ depth) hedges
        omega
  have hlast : rule.edges ^ n ≤ ∑ k ∈ Finset.range (n + 1), rule.edges ^ k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hpositive : 1 ≤ rule.edges ^ n := one_le_pow₀ (show 1 ≤ rule.edges by omega)
  have hinterior : Fintype.card (rule.generation n).network.InteriorVertex =
      (rule.vertices - 2) * ∑ k ∈ Finset.range (n + 1), rule.edges ^ k := by
    rw [(rule.generation n).network.card_interior_vertices, rule.generation_vertices]
    omega
  constructor
  · rw [hinterior]
    apply hlast.trans
    exact Nat.le_mul_of_pos_left _ (by omega)
  · rw [rule.generation_vertices]
    have hproduct := Nat.mul_le_mul_left (rule.vertices - 2) (hgeometric n)
    have hsplit : rule.vertices - 2 + 2 = rule.vertices := by omega
    nlinarith

end
end Universality.Rule
