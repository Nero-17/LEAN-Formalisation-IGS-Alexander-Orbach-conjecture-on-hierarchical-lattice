import Universality.Examples.DiamondClassical
import Universality.Graph.CellIsometry
import Universality.Graph.CoarseDistance
import Universality.Graph.SubstitutionFullConnectivity
import Universality.Graph.GeodesicEdgeLevels
import Universality.Graph.GenerationReassociation
import Universality.Percolation.WindowNetworkEquivalence

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- If every oriented outer edge lies on a terminal geodesic and every
inner vertex lies on one, then every vertex of the actual substitution
lies on a terminal geodesic. -/
theorem substitute_terminal_distance_sum
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (houterVertex : ∀ vertex, R.fullGraph.dist R.source vertex + R.fullGraph.dist vertex R.target =
      R.fullGraph.dist R.source R.target)
    (houterEdge : ∀ edge, R.fullGraph.dist R.source (R.endpoint edge).1 + 1 +
      R.fullGraph.dist (R.endpoint edge).2 R.target = R.fullGraph.dist R.source R.target)
    (hinnerVertex : ∀ vertex, S.fullGraph.dist S.source vertex + S.fullGraph.dist vertex S.target =
      S.fullGraph.dist S.source S.target)
    (vertex : Fin (Fintype.card (R.SubstitutionVertex S))) :
    (R.substitute S).fullGraph.dist (R.substitute S).source vertex +
      (R.substitute S).fullGraph.dist vertex (R.substitute S).target =
      (R.substitute S).fullGraph.dist (R.substitute S).source (R.substitute S).target := by
  have hconnected (u v : Fin (Fintype.card (R.SubstitutionVertex S))) :
      (R.substitute S).fullGraph.Reachable u v :=
    (R.substitute_all_vertices_connected S houter hinner u).symm.trans
      (R.substitute_all_vertices_connected S houter hinner v)
  have hterminal := R.substitute_terminal_distance S (houter _) (hinner _)
  apply Nat.le_antisymm
  · rw [hterminal]
    obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
    cases vertex with
    | inl old =>
        change (R.substitute S).fullGraph.dist (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source))
            (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl old)) +
          (R.substitute S).fullGraph.dist (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl old))
            (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) ≤ _
        rw [R.substitute_coarse_distance S _ _ (houter old) (hinner _),
          R.substitute_coarse_distance S _ _ ((houter old).symm.trans (houter _)) (hinner _),
          ← Nat.add_mul, houterVertex]
    | inr pair =>
        rcases pair with ⟨edge, inside⟩
        have hsource : R.cellEmbedding S edge S.source = Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).1) := by
          change Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.source) = _
          rw [R.cellVertex_source]
        have htarget : R.cellEmbedding S edge S.target = Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).2) := by
          change Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.target) = _
          rw [R.cellVertex_target]
        have hinside : R.cellEmbedding S edge inside.val = Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, inside)) := by
          simp [cellEmbedding, cellVertex, inside.property.1, inside.property.2]
        have hleft := (hconnected (R.substitute S).source (R.cellEmbedding S edge S.source)).dist_triangle_left
          (R.cellEmbedding S edge inside.val)
        have hright := (hconnected (R.cellEmbedding S edge inside.val) (R.cellEmbedding S edge S.target)).dist_triangle_left
          (R.substitute S).target
        have hleftCell := R.substitute_cell_distance S hinner edge S.source inside.val
        change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge S.source)
          (R.cellEmbedding S edge inside.val) = S.fullGraph.dist S.source inside.val at hleftCell
        have hrightCell := R.substitute_cell_distance S hinner edge inside.val S.target
        change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge inside.val)
          (R.cellEmbedding S edge S.target) = S.fullGraph.dist inside.val S.target at hrightCell
        rw [hleftCell, hsource] at hleft
        rw [hrightCell, htarget] at hright
        change (R.substitute S).fullGraph.dist (R.substitute S).source (R.cellEmbedding S edge inside.val) ≤
          (R.substitute S).fullGraph.dist (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source))
            (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).1)) + S.fullGraph.dist S.source inside.val at hleft
        change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge inside.val) (R.substitute S).target ≤
          S.fullGraph.dist inside.val S.target +
          (R.substitute S).fullGraph.dist (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl (R.endpoint edge).2))
            (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) at hright
        rw [R.substitute_coarse_distance S _ _ (houter _) (hinner _)] at hleft
        rw [R.substitute_coarse_distance S _ _ ((houter _).symm.trans (houter _)) (hinner _)] at hright
        rw [hinside] at hleft hright
        have hlocal := hinnerVertex inside.val
        have hcoarse := congrArg (fun value => value * S.fullGraph.dist S.source S.target) (houterEdge edge)
        nlinarith
  · exact (hconnected (R.substitute S).source vertex).dist_triangle_left (R.substitute S).target

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem diamond_source_distance (vertex : Fin 4) :
    diamondNetwork.fullGraph.dist diamondNetwork.source vertex = ![0, 2, 1, 1] vertex := by
  fin_cases vertex
  · change diamondNetwork.fullGraph.dist 0 0 = 0; simp
  · exact diamond_terminal_distance
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)

theorem diamond_target_distance (vertex : Fin 4) :
    diamondNetwork.fullGraph.dist vertex diamondNetwork.target = ![2, 0, 1, 1] vertex := by
  fin_cases vertex
  · exact diamond_terminal_distance
  · change diamondNetwork.fullGraph.dist 1 1 = 0; simp
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)

theorem diamond_terminal_distance_sum (vertex : Fin 4) :
    diamondNetwork.fullGraph.dist diamondNetwork.source vertex +
      diamondNetwork.fullGraph.dist vertex diamondNetwork.target =
      diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target := by
  rw [diamond_source_distance, diamond_target_distance, diamond_terminal_distance]
  fin_cases vertex <;> decide

theorem diamond_edge_geodesic (edge : Fin 4) :
    diamondNetwork.fullGraph.dist diamondNetwork.source (diamondNetwork.endpoint edge).1 + 1 +
      diamondNetwork.fullGraph.dist (diamondNetwork.endpoint edge).2 diamondNetwork.target =
      diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target := by
  rw [diamond_source_distance, diamond_target_distance, diamond_terminal_distance]
  fin_cases edge <;> decide

/-- Every vertex of the actual finite diamond graph lies on an ambient
terminal geodesic, proved through the exact substitution equivalence. -/
theorem diamond_generation_terminal_distance_sum (n : ℕ)
    (vertex : Fin (diamondRule.generation n).vertices) :
    (diamondRule.generation n).network.fullGraph.dist (diamondRule.generation n).network.source vertex +
      (diamondRule.generation n).network.fullGraph.dist vertex (diamondRule.generation n).network.target =
      (diamondRule.generation n).network.fullGraph.dist
        (diamondRule.generation n).network.source (diamondRule.generation n).network.target := by
  induction n with
  | zero => exact diamond_terminal_distance_sum vertex
  | succ n ih =>
      let equivalence := diamondRule.generationTopDecomposition n
      have h := diamondNetwork.substitute_terminal_distance_sum (diamondRule.generation n).network
        diamondRule_classical.connected (diamondRule_classical.generation n).connected
        diamond_terminal_distance_sum diamond_edge_geodesic ih (equivalence.vertex vertex)
      have hsource := equivalence.fullGraph_distance (diamondRule_classical.generation (n + 1)).connected
        (diamondRule.generation (n + 1)).network.source vertex
      have htarget := equivalence.fullGraph_distance (diamondRule_classical.generation (n + 1)).connected
        vertex (diamondRule.generation (n + 1)).network.target
      have hterminal := equivalence.fullGraph_distance (diamondRule_classical.generation (n + 1)).connected
        (diamondRule.generation (n + 1)).network.source (diamondRule.generation (n + 1)).network.target
      rw [equivalence.source] at hsource
      rw [equivalence.target] at htarget
      rw [equivalence.source, equivalence.target] at hterminal
      exact ((congrArg₂ Nat.add hsource htarget).symm.trans h).trans hterminal

theorem diamond_generation_terminal_distance (n : ℕ) :
    (diamondRule.generation n).network.fullGraph.dist
      (diamondRule.generation n).network.source (diamondRule.generation n).network.target = 2 ^ (n + 1) := by
  rw [diamondRule.generation_terminal_distance (diamondRule_classical.connected _) n]
  exact congrArg (fun length => length ^ (n + 1)) diamond_terminal_distance

/-- The layer coordinate is the actual distance to the source. -/
theorem diamond_generation_layer (n : ℕ) (vertex : Fin (diamondRule.generation n).vertices) :
    (diamondRule.generation n).network.fullGraph.dist (diamondRule.generation n).network.source vertex ≤ 2 ^ (n + 1) ∧
      (diamondRule.generation n).network.fullGraph.dist vertex (diamondRule.generation n).network.target =
        2 ^ (n + 1) -
          (diamondRule.generation n).network.fullGraph.dist (diamondRule.generation n).network.source vertex := by
  have h := diamond_generation_terminal_distance_sum n vertex
  rw [diamond_generation_terminal_distance] at h
  omega

/-- The exact terminal scale bounds the diameter of each actual diamond
generation; the two terminals show this bound is attained. -/
theorem diamond_generation_diameter (n : ℕ) (first second : Fin (diamondRule.generation n).vertices) :
    (diamondRule.generation n).network.fullGraph.dist first second ≤ 2 ^ (n + 1) := by
  have hfirst := diamond_generation_terminal_distance_sum n first
  have hsecond := diamond_generation_terminal_distance_sum n second
  rw [diamond_generation_terminal_distance] at hfirst hsecond
  have hsource := ((diamondRule_classical.generation n).connected first).symm.dist_triangle_left second
  have htarget := (((diamondRule_classical.generation n).connected first).symm.trans
    ((diamondRule_classical.generation n).connected (diamondRule.generation n).network.target)).dist_triangle_left second
  rw [SimpleGraph.dist_comm (u := first) (v := (diamondRule.generation n).network.source)] at hsource
  rw [SimpleGraph.dist_comm (u := (diamondRule.generation n).network.target) (v := second)] at htarget
  omega

end
end Universality
