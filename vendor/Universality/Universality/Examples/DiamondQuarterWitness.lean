import Universality.Examples.DiamondQuarterCell
import Universality.Percolation.DistanceWindowPairs

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (S : FiniteNetwork vertices edges)

theorem diamond_all_crossing_substitute_crosses
    (cells : Fin 4 → Configuration edges)
    (hcrossing : ∀ edge, S.crosses (cells edge) = true) :
    (diamondNetwork.substitute S).crosses (substitutionConfigurationEquiv cells) = true := by
  rw [diamondNetwork.substitute_crosses S]
  have hcoarse : S.coarseConfiguration cells = fun _ => true := funext hcrossing
  rw [hcoarse]
  exact (diamondNetwork.crosses_eq_true _).mpr (diamondRule_classical.connected _)

theorem diamond_quarter_source_reachable
    (cells : Fin 4 → Fin 4 → Configuration edges)
    (hcrossing : ∀ first second, S.crosses (cells first second) = true)
    (vertex : Fin vertices) (hvertex : (S.openGraph (cells 0 1)).Reachable S.source vertex) :
    ((diamondNetwork.substitute (diamondNetwork.substitute S)).openGraph
      (substitutionConfigurationEquiv (fun edge => substitutionConfigurationEquiv (cells edge)))).Reachable
      (diamondNetwork.substitute (diamondNetwork.substitute S)).source (diamondQuarterEmbedding S vertex) := by
  let inner := diamondNetwork.substitute S
  have hfirst := diamondNetwork.all_crossing_cells_join_sources S diamondRule_classical.connected
    (cells 0) (hcrossing 0) 0 1 S.source vertex (.refl _) hvertex
  have hinnerSource : diamondNetwork.cellEmbedding S 0 S.source = inner.source := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 0 S.source) = _
    rw [diamondNetwork.cellVertex_source]
    rfl
  rw [hinnerSource] at hfirst
  have hmainSource : diamondNetwork.cellEmbedding inner 0 inner.source =
      (diamondNetwork.substitute inner).source := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex inner) (diamondNetwork.cellVertex inner 0 inner.source) = _
    rw [diamondNetwork.cellVertex_source]
    rfl
  rw [← hmainSource]
  change ((diamondNetwork.substitute inner).openGraph _).Reachable
    (Fintype.equivFin (diamondNetwork.SubstitutionVertex inner) (diamondNetwork.cellVertex inner 0 inner.source))
    (Fintype.equivFin (diamondNetwork.SubstitutionVertex inner)
      (diamondNetwork.cellVertex inner 0 (diamondNetwork.cellEmbedding S 1 vertex)))
  rw [diamondNetwork.substitute_reachable_iff inner]
  exact hfirst.map (diamondNetwork.cellHom inner
    (fun edge => substitutionConfigurationEquiv (cells edge)) 0)

/-- Crossing of all sixteen actual grandchildren forces an opposite-branch
open vertex at exact main-cell distance from each selected quarter-cell root. -/
theorem diamond_quarter_distance_witness
    (hconnected : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (hlayers : ∀ vertex, S.fullGraph.dist S.source vertex + S.fullGraph.dist vertex S.target =
      S.fullGraph.dist S.source S.target)
    (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ S.fullGraph.dist S.source S.target)
    (hpositive : 0 < S.fullGraph.dist S.source S.target)
    (hgeodesic : ∀ configuration, S.crosses configuration = true →
      ∃ walk : (S.openGraph configuration).Walk S.source S.target,
        walk.length = S.fullGraph.dist S.source S.target)
    (cells : Fin 4 → Fin 4 → Configuration edges)
    (hcrossing : ∀ first second, S.crosses (cells first second) = true)
    (vertex : Fin vertices) :
    let main := diamondNetwork.substitute (diamondNetwork.substitute S)
    ∃ witness, (main.openGraph
      (substitutionConfigurationEquiv (fun edge => substitutionConfigurationEquiv (cells edge)))).Reachable
      main.source witness ∧ main.fullGraph.dist (diamondQuarterEmbedding S vertex) witness =
        4 * S.fullGraph.dist S.source S.target := by
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
  have hchildGeodesic (edge : Fin 4) := diamondNetwork.substitute_open_geodesic S
    (diamondRule_classical.connected _) (hconnected _) diamond_open_geodesic hgeodesic
    (substitutionConfigurationEquiv (cells edge)) (diamond_all_crossing_substitute_crosses S (cells edge) (hcrossing edge))
  obtain ⟨first, hfirst⟩ := hchildGeodesic 2
  obtain ⟨second, hsecond⟩ := hchildGeodesic 3
  obtain ⟨hlower, hupper, _, _, hbranch⟩ := diamond_quarter_cell_geometry S hconnected hlayers hdiameter hpositive vertex
  obtain ⟨witness, hreach, hwbranch, hwlayer⟩ := diamond_right_branch_has_every_layer inner hinnerConnected
    (fun edge => substitutionConfigurationEquiv (cells edge)) first second hfirst hsecond
    (4 * S.fullGraph.dist S.source S.target - main.fullGraph.dist main.source (diamondQuarterEmbedding S vertex))
    (by dsimp only [main, inner] at *; omega) (by dsimp only [main, inner] at *; omega)
  refine ⟨witness, hreach, ?_⟩
  have hdistance := diamond_substitution_branch_distance inner hinnerConnected
    (diamondQuarterEmbedding S vertex) witness (by rw [hbranch, hwbranch]; decide)
  have hrootLayers := hmainLayers (diamondQuarterEmbedding S vertex)
  have hwitnessLayers := hmainLayers witness
  rw [hmainLength] at hrootLayers hwitnessLayers
  rw [hdistance]
  dsimp only [main, inner] at *
  omega

end
end Universality


