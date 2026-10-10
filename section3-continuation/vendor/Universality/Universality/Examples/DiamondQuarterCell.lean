import Universality.Examples.DiamondOppositeWitness

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (S : FiniteNetwork vertices edges)

def diamondQuarterEmbedding : Fin vertices ↪
    Fin (Fintype.card (diamondNetwork.SubstitutionVertex (diamondNetwork.substitute S))) :=
  (diamondNetwork.cellEmbedding S 1).trans
    (diamondNetwork.cellEmbedding (diamondNetwork.substitute S) 0)

/-- The fixed grandchild indexed by outer edge zero and inner edge one
lies between one quarter and one half of the actual main-cell scale. -/
theorem diamond_quarter_cell_geometry
    (hconnected : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (hlayers : ∀ vertex, S.fullGraph.dist S.source vertex + S.fullGraph.dist vertex S.target =
      S.fullGraph.dist S.source S.target)
    (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ S.fullGraph.dist S.source S.target)
    (hpositive : 0 < S.fullGraph.dist S.source S.target)
    (vertex : Fin vertices) :
    let main := diamondNetwork.substitute (diamondNetwork.substitute S)
    S.fullGraph.dist S.source S.target ≤ main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) ∧
      main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) ≤ 2 * S.fullGraph.dist S.source S.target ∧
      main.fullGraph.dist (diamondQuarterEmbedding S vertex) main.source + S.fullGraph.dist S.source S.target ≤
        4 * S.fullGraph.dist S.source S.target ∧
      main.fullGraph.dist (diamondQuarterEmbedding S vertex) main.target + S.fullGraph.dist S.source S.target ≤
        4 * S.fullGraph.dist S.source S.target ∧
      diamondBranch (diamondNetwork.substitute S) (diamondQuarterEmbedding S vertex) = false := by
  let inner := diamondNetwork.substitute S
  let main := diamondNetwork.substitute inner
  have hinnerConnected := diamondNetwork.substitute_all_vertices_connected S diamondRule_classical.connected hconnected
  have hinnerLayers := diamondNetwork.substitute_terminal_distance_sum S diamondRule_classical.connected hconnected
    diamond_terminal_distance_sum diamond_edge_geodesic hlayers
  have hmainLayers := diamondNetwork.substitute_terminal_distance_sum inner diamondRule_classical.connected hinnerConnected
    diamond_terminal_distance_sum diamond_edge_geodesic hinnerLayers
  have hinnerLength : inner.fullGraph.dist inner.source inner.target = 2 * S.fullGraph.dist S.source S.target := by
    rw [diamondNetwork.substitute_terminal_distance S (diamondRule_classical.connected _) (hconnected _), diamond_terminal_distance]
  have hmainLength : main.fullGraph.dist main.source main.target = 4 * S.fullGraph.dist S.source S.target := by
    rw [diamondNetwork.substitute_terminal_distance inner (diamondRule_classical.connected _) (hinnerConnected _),
      diamond_terminal_distance, hinnerLength]
    omega
  have hmainSource : diamondNetwork.cellEmbedding inner 0 inner.source = main.source := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex inner)
      (diamondNetwork.cellVertex inner 0 inner.source) = _
    rw [diamondNetwork.cellVertex_source]
    rfl
  have hinnerTarget : diamondNetwork.cellEmbedding S 1 S.target = inner.target := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 1 S.target) = _
    rw [diamondNetwork.cellVertex_target]
    rfl
  have hsourceDistance := diamondNetwork.substitute_cell_distance inner hinnerConnected 0
    inner.source (diamondNetwork.cellEmbedding S 1 vertex)
  change main.fullGraph.dist (diamondNetwork.cellEmbedding inner 0 inner.source)
      (diamondQuarterEmbedding S vertex) = inner.fullGraph.dist inner.source (diamondNetwork.cellEmbedding S 1 vertex) at hsourceDistance
  rw [hmainSource] at hsourceDistance
  have htargetDistance := diamondNetwork.substitute_cell_distance S hconnected 1 vertex S.target
  change inner.fullGraph.dist (diamondNetwork.cellEmbedding S 1 vertex)
    (diamondNetwork.cellEmbedding S 1 S.target) = S.fullGraph.dist vertex S.target at htargetDistance
  rw [hinnerTarget] at htargetDistance
  have hlocal := hinnerLayers (diamondNetwork.cellEmbedding S 1 vertex)
  rw [hinnerLength, htargetDistance] at hlocal
  have hlocalBound := hdiameter vertex S.target
  have hmain := hmainLayers (diamondQuarterEmbedding S vertex)
  rw [hmainLength] at hmain
  have hrootPositive : 0 < main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) := by dsimp only [main, inner] at *; omega
  have hrootBefore : main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) <
      main.fullGraph.dist main.source main.target := by dsimp only [main, inner] at *; omega
  have hnotSource : diamondQuarterEmbedding S vertex ≠ main.source := by
    intro heq
    rw [heq, SimpleGraph.dist_self] at hrootPositive
    omega
  have hnotTarget : diamondQuarterEmbedding S vertex ≠ main.target := by
    intro heq
    rw [heq] at hrootBefore
    omega
  have hbranch := diamondBranch_cell inner 0 (diamondNetwork.cellEmbedding S 1 vertex) hnotSource hnotTarget
  change diamondBranch inner (diamondQuarterEmbedding S vertex) = decide (2 ≤ (0 : Fin 4).val) at hbranch
  norm_num at hbranch
  change S.fullGraph.dist S.source S.target ≤ main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) ∧
    main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex) ≤ 2 * S.fullGraph.dist S.source S.target ∧
    main.fullGraph.dist (diamondQuarterEmbedding S vertex) main.source + S.fullGraph.dist S.source S.target ≤
      4 * S.fullGraph.dist S.source S.target ∧
    main.fullGraph.dist (diamondQuarterEmbedding S vertex) main.target + S.fullGraph.dist S.source S.target ≤
      4 * S.fullGraph.dist S.source S.target ∧ _
  rw [SimpleGraph.dist_comm (u := diamondQuarterEmbedding S vertex) (v := main.source)]
  exact ⟨by dsimp only [main, inner] at *; omega, by dsimp only [main, inner] at *; omega, by dsimp only [main, inner] at *; omega, by dsimp only [main, inner] at *; omega, hbranch⟩

end
end Universality


