import Universality.Graph.AncestralTowerIsometry
import Universality.Graph.FiniteVolume
import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem Classical.generation_vertices_gt_index {rule : Rule} (h : rule.Classical) (n : ℕ) :
    n < (rule.generation n).vertices := by
  have hsum : n + 1 ≤ ∑ k ∈ Finset.range (n + 1), rule.edges ^ k := by
    calc
      n + 1 = ∑ k ∈ Finset.range (n + 1), (1 : ℕ) := by simp
      _ ≤ ∑ k ∈ Finset.range (n + 1), rule.edges ^ k :=
        Finset.sum_le_sum (fun k _ => one_le_pow₀ (Nat.le_of_lt h.edges_gt_one))
  have hproduct := Nat.le_mul_of_pos_left
    (∑ k ∈ Finset.range (n + 1), rule.edges ^ k)
    (show 0 < rule.vertices - 2 by have := h.vertices_gt_two; omega)
  rw [rule.generation_vertices]
  omega

/-- Every physical ancestral tower has infinitely many actual vertices,
because each growing finite generation embeds injectively. -/
theorem Classical.ancestralTower_infinite_vertices {rule : Rule} (h : rule.Classical)
    (age : ℕ) (address : ℕ → Fin rule.edges) :
    Infinite (rule.ancestralTower age address).Vertex := by
  classical
  by_contra hnot
  letI : Finite (rule.ancestralTower age address).Vertex := not_infinite_iff_finite.mp hnot
  letI : Fintype (rule.ancestralTower age address).Vertex := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective
    ((rule.ancestralTower age address).vertex
      (Fintype.card (rule.ancestralTower age address).Vertex))
    ((rule.ancestralTower age address).vertex_injective _)
  simp only [Fintype.card_fin] at hcard
  have hgrowth := h.generation_vertices_gt_index
    (age + Fintype.card (rule.ancestralTower age address).Vertex)
  change (rule.generation (age + Fintype.card (rule.ancestralTower age address).Vertex)).vertices ≤
    Fintype.card (rule.ancestralTower age address).Vertex at hcard
  omega

theorem ancestralTower_countable_vertices (rule : Rule) (age : ℕ)
    (address : ℕ → Fin rule.edges) : Countable (rule.ancestralTower age address).Vertex := by
  unfold NetworkTower.Vertex
  infer_instance

end
end Universality.Rule
