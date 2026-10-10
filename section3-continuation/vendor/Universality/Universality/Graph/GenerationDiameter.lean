import Universality.Graph.SubstitutionRadius
import Universality.Graph.ClassicalSubstitution

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The distance to the source at every generation is bounded at the
terminal-distance scale, not at the generally larger edge-count scale. -/
theorem Classical.generation_source_distance_bound {rule : Rule} (h : rule.Classical)
    (bound : ℕ) (hbound : ∀ vertex,
      rule.network.fullGraph.dist rule.network.source vertex ≤ bound) :
    ∀ n vertex,
      (rule.generation n).network.fullGraph.dist
          (rule.generation n).network.source vertex + bound ≤
        2 * bound * rule.network.fullGraph.dist
          rule.network.source rule.network.target ^ n := by
  intro n
  induction n with
  | zero =>
      intro vertex
      change rule.network.fullGraph.dist rule.network.source vertex + bound ≤
        2 * bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ 0
      simp only [pow_zero, mul_one]
      have := hbound vertex
      omega
  | succ n ih =>
      intro vertex
      let previousBound := Finset.univ.sup (fun vertex =>
        (rule.generation n).network.fullGraph.dist (rule.generation n).network.source vertex)
      have hprevious : ∀ vertex,
          (rule.generation n).network.fullGraph.dist
            (rule.generation n).network.source vertex ≤ previousBound := by
        intro vertex
        exact Finset.le_sup (Finset.mem_univ vertex)
      have hpreviousBound : previousBound + bound ≤
          2 * bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n := by
        have hle : previousBound ≤
            2 * bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n - bound := by
          apply Finset.sup_le
          intro vertex _
          exact Nat.le_sub_of_add_le (ih vertex)
        have hexists := ih (rule.generation n).network.source
        omega
      have hstep := (rule.generation n).network.substitute_source_distance_bound rule.network
        (h.generation n).connected h.connected previousBound bound hprevious hbound vertex
      change (rule.generation (n + 1)).network.fullGraph.dist
        (rule.generation (n + 1)).network.source vertex ≤ _ at hstep
      have hscale := h.scale
      have hmul := Nat.mul_le_mul_right
        (rule.network.fullGraph.dist rule.network.source rule.network.target) hpreviousBound
      rw [pow_succ]
      nlinarith

/-- Uniform diameter bound for actual finite substitution graphs. -/
theorem Classical.generation_diameter_bound {rule : Rule} (h : rule.Classical) :
    ∃ bound : ℕ, 0 < bound ∧ ∀ n (u v : Fin (rule.generation n).vertices),
      (rule.generation n).network.fullGraph.dist u v ≤
        bound * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n := by
  let sourceBound := 1 + Finset.univ.sup
    (fun vertex => rule.network.fullGraph.dist rule.network.source vertex)
  have hsource : ∀ vertex, rule.network.fullGraph.dist rule.network.source vertex ≤ sourceBound := by
    intro vertex
    have := Finset.le_sup (s := Finset.univ)
      (f := fun vertex => rule.network.fullGraph.dist rule.network.source vertex)
      (Finset.mem_univ vertex)
    exact this.trans (Nat.le_add_left _ _)
  refine ⟨4 * sourceBound, by dsimp [sourceBound]; omega, ?_⟩
  intro n u v
  have hu := h.generation_source_distance_bound sourceBound hsource n u
  have hv := h.generation_source_distance_bound sourceBound hsource n v
  have htriangle := ((h.generation n).connected u).symm.dist_triangle_left v
  rw [SimpleGraph.dist_comm (u := u) (v := (rule.generation n).network.source)] at htriangle
  nlinarith

end
end Universality.Rule
