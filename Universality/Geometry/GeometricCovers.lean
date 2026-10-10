import Universality.Geometry.GeometricNets

namespace Universality.Geometry
noncomputable section
open Set Filter Metric
open scoped Topology

theorem closure_union_subset_level_closedBalls_of_geometric_steps
    {Ambient : Type*} [MetricSpace Ambient]
    (Node : ℕ → Type*) [∀ depth, Finite (Node depth)]
    (inclusion : ∀ depth, Node depth → Ambient)
    (hnested : Monotone (fun depth => Set.range (inclusion depth)))
    (constant ratio : ℝ) (hconstant : 0 ≤ constant) (hratio : 0 ≤ ratio) (hratioOne : ratio < 1)
    (hstep : ∀ depth (point : Node (depth + 1)), ∃ previous : Node depth,
      dist (inclusion (depth + 1) point) (inclusion depth previous) ≤ constant * ratio ^ depth)
    (depth : ℕ) :
    closure (⋃ level, Set.range (inclusion level)) ⊆
      ⋃ vertex : Node depth, Metric.closedBall (inclusion depth vertex)
        (constant / (1 - ratio) * ratio ^ depth) := by
  have hdenominator : 0 < 1 - ratio := sub_pos.mpr hratioOne
  have hcoefficient : 0 ≤ constant / (1 - ratio) := div_nonneg hconstant hdenominator.le
  have approximate (first second : ℕ) (bound : first ≤ second) :
      ∀ point : Node second, ∃ old : Node first,
        dist (inclusion second point) (inclusion first old) ≤
          constant / (1 - ratio) * (ratio ^ first - ratio ^ second) := by
    induction second, bound using Nat.le_induction with
    | base =>
      intro point
      exact ⟨point, by simp⟩
    | succ second bound ih =>
      intro point
      obtain ⟨previous, hprevious⟩ := hstep second point
      obtain ⟨old, hold⟩ := ih previous
      refine ⟨old, ?_⟩
      calc
        dist (inclusion (second + 1) point) (inclusion first old) ≤
            dist (inclusion (second + 1) point) (inclusion second previous) +
              dist (inclusion second previous) (inclusion first old) := dist_triangle _ _ _
        _ ≤ constant * ratio ^ second +
            constant / (1 - ratio) * (ratio ^ first - ratio ^ second) := add_le_add hprevious hold
        _ = constant / (1 - ratio) * (ratio ^ first - ratio ^ (second + 1)) := by
          rw [pow_succ]
          field_simp [ne_of_gt hdenominator]
          ring
  apply closure_minimal ?_ (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall))
  intro point hpoint
  obtain ⟨level, vertex, rfl⟩ := Set.mem_iUnion.mp hpoint
  rcases le_total level depth with hle | hle
  · obtain ⟨old, hold⟩ := hnested hle (Set.mem_range_self vertex)
    refine Set.mem_iUnion.mpr ⟨old, ?_⟩
    rw [← hold]
    exact Metric.mem_closedBall_self (mul_nonneg hcoefficient (pow_nonneg hratio depth))
  · obtain ⟨old, hold⟩ := approximate depth level hle vertex
    exact Set.mem_iUnion.mpr ⟨old, hold.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (pow_nonneg hratio _)) hcoefficient)⟩

end
end Universality.Geometry

