import Universality.Graph.ClassicalSubstitution
import Universality.Graph.DistanceCertificate
import Universality.Graph.GenerationReassociation

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- Every vertex of a shortest terminal walk has its prescribed distance
from the source. -/
theorem shortest_walk_source_distance
    (walk : R.fullGraph.Walk R.source R.target)
    (hlength : walk.length = R.fullGraph.dist R.source R.target)
    (index : ℕ) (hindex : index ≤ walk.length) :
    R.fullGraph.dist R.source (walk.getVert index) = index := by
  have hfirst := SimpleGraph.dist_le (walk.take index)
  have hsecond := SimpleGraph.dist_le (walk.drop index)
  rw [SimpleGraph.Walk.take_length, min_eq_left hindex] at hfirst
  rw [SimpleGraph.Walk.drop_length] at hsecond
  have htriangle := (show R.fullGraph.Reachable R.source (walk.getVert index) from
    ⟨walk.take index⟩).dist_triangle_left R.target
  omega

/-- There is an indexed edge across every consecutive pair of levels before
the terminal distance; its stored orientation can be either direction. -/
theorem exists_edge_at_source_distance
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (index : ℕ) (hindex : index < R.fullGraph.dist R.source R.target) :
    ∃ edge : Fin edges,
      (R.fullGraph.dist R.source (R.endpoint edge).1 = index ∧
        R.fullGraph.dist R.source (R.endpoint edge).2 = index + 1) ∨
      (R.fullGraph.dist R.source (R.endpoint edge).2 = index ∧
        R.fullGraph.dist R.source (R.endpoint edge).1 = index + 1) := by
  obtain ⟨walk, hlength⟩ := hconnected.exists_walk_length_eq_dist
  have hwalkIndex : index < walk.length := by omega
  have hfirst := R.shortest_walk_source_distance walk hlength index hwalkIndex.le
  have hsecond := R.shortest_walk_source_distance walk hlength (index + 1) (by omega)
  obtain ⟨_, edge, _, hedge | hedge⟩ := walk.adj_getVert_succ hwalkIndex
  · exact ⟨edge, Or.inl (by simpa only [hedge] using And.intro hfirst hsecond)⟩
  · exact ⟨edge, Or.inr (by simpa only [hedge] using And.intro hfirst hsecond)⟩

/-- Stored first endpoints of two geodesic edges have separation within a
fixed additive error of the chosen level. This avoids orientation assumptions. -/
theorem exists_separated_geodesic_edges
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (index : ℕ) (hindex : 2 ≤ index)
    (hterminal : index < R.fullGraph.dist R.source R.target) :
    ∃ first second : Fin edges, first ≠ second ∧
      index ≤ R.fullGraph.dist (R.endpoint first).1 (R.endpoint second).1 + 1 ∧
      R.fullGraph.dist (R.endpoint first).1 (R.endpoint second).1 ≤ index + 2 := by
  obtain ⟨first, hfirst⟩ := R.exists_edge_at_source_distance (hconnected _) 0 (by omega)
  obtain ⟨second, hsecond⟩ := R.exists_edge_at_source_distance (hconnected _) index hterminal
  have hfirstBound : R.fullGraph.dist R.source (R.endpoint first).1 ≤ 1 := by
    rcases hfirst with hfirst | hfirst <;> omega
  have hsecondLower : index ≤ R.fullGraph.dist R.source (R.endpoint second).1 := by
    rcases hsecond with hsecond | hsecond <;> omega
  have hsecondUpper : R.fullGraph.dist R.source (R.endpoint second).1 ≤ index + 1 := by
    rcases hsecond with hsecond | hsecond <;> omega
  have hforward := (hconnected (R.endpoint first).1).dist_triangle_left (R.endpoint second).1
  have hbackward := (hconnected (R.endpoint first).1).symm.dist_triangle_left (R.endpoint second).1
  rw [SimpleGraph.dist_comm (u := (R.endpoint first).1) (v := R.source)] at hbackward
  refine ⟨first, second, ?_, by omega, by omega⟩
  intro heq
  subst second
  omega

theorem exists_internal_edge_of_terminal_distance_gt_two
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hdistance : 2 < R.fullGraph.dist R.source R.target) :
    ∃ edge : Fin edges, (R.endpoint edge).1 ≠ R.source ∧
      (R.endpoint edge).1 ≠ R.target ∧ (R.endpoint edge).2 ≠ R.source ∧
      (R.endpoint edge).2 ≠ R.target := by
  obtain ⟨edge, hedge | hedge⟩ := R.exists_edge_at_source_distance hconnected 1 (by omega)
  all_goals
    refine ⟨edge, ?_, ?_, ?_, ?_⟩
    all_goals intro heq; simp only [heq, SimpleGraph.dist_self] at hedge; omega

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

/-- A fixed coarse generation with a common fine generation inside each edge
is a relabelling of the original finite graph at their combined depth. -/
def generationBlockDecomposition (rule : Rule) (coarse : ℕ) : (fine : ℕ) →
    (rule.generation (coarse + fine + 1)).network.NetworkEquivalence
      ((rule.generation coarse).network.substitute (rule.generation fine).network)
  | 0 => FiniteNetwork.NetworkEquivalence.refl _
  | fine + 1 =>
      ((generationBlockDecomposition rule coarse fine).substitute
        (FiniteNetwork.NetworkEquivalence.refl rule.network)).trans
        ((rule.generation coarse).network.substitutionAssociativity
          (rule.generation fine).network rule.network)

/-- Two substitution levels always contain an edge with both endpoints
strictly inside the enclosing cell. -/
theorem Classical.second_generation_internal_edge {rule : Rule} (h : rule.Classical) :
    ∃ edge : Fin (rule.generation 1).edges,
      ((rule.generation 1).network.endpoint edge).1 ≠ (rule.generation 1).network.source ∧
      ((rule.generation 1).network.endpoint edge).1 ≠ (rule.generation 1).network.target ∧
      ((rule.generation 1).network.endpoint edge).2 ≠ (rule.generation 1).network.source ∧
      ((rule.generation 1).network.endpoint edge).2 ≠ (rule.generation 1).network.target := by
  apply (rule.generation 1).network.exists_internal_edge_of_terminal_distance_gt_two
    ((h.generation 1).connected _)
  rw [rule.generation_terminal_distance (h.connected _) 1]
  have hscale := h.scale
  norm_num only [Nat.reduceAdd, pow_two]
  nlinarith

end
end Universality.Rule
