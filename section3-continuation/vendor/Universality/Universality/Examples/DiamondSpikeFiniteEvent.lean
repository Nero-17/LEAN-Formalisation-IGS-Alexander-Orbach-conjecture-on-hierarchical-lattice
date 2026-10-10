import Universality.Examples.DiamondQuarterWitness
import Universality.Examples.DoubleClosedAttachments
import Universality.Percolation.IsolatedCellPointCount

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges vertices edges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork vertices edges)

/-- A fixed two-generation status event yields actual exact-radius mass.
Its hypotheses refer only to the sixteen grandchild crossing indicators
inside each outer cell, and to already proved geometry of the inner graph. -/
theorem diamond_spike_finite_event
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hconnected : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (hlayers : ∀ vertex, S.fullGraph.dist S.source vertex + S.fullGraph.dist vertex S.target =
      S.fullGraph.dist S.source S.target)
    (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ S.fullGraph.dist S.source S.target)
    (hpositive : 0 < S.fullGraph.dist S.source S.target)
    (hgeodesic : ∀ configuration, S.crosses configuration = true →
      ∃ walk : (S.openGraph configuration).Walk S.source S.target,
        walk.length = S.fullGraph.dist S.source S.target)
    (mainEdge : Fin outerEdges)
    (hfirstSource : (R.endpoint mainEdge).1 ≠ R.source)
    (hfirstTarget : (R.endpoint mainEdge).1 ≠ R.target)
    (hsecondSource : (R.endpoint mainEdge).2 ≠ R.source)
    (hsecondTarget : (R.endpoint mainEdge).2 ≠ R.target)
    (cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges)
    (hmain : ∀ first second, S.crosses (cells mainEdge first second) = true)
    (hother : ∀ edge, edge ≠ mainEdge → ∀ first second, S.crosses (cells edge first second) = false) :
    S.internalSelectedMass true false (cells mainEdge 0 1) ≤
      (R.substitute (diamondNetwork.substitute (diamondNetwork.substitute S))).internalRadiusPointRootCount
        (substitutionConfigurationEquiv (fun edge => substitutionConfigurationEquiv
          (fun first => substitutionConfigurationEquiv (cells edge first))))
        (4 * S.fullGraph.dist S.source S.target) := by
  classical
  let inner := diamondNetwork.substitute S
  let main := diamondNetwork.substitute inner
  let configurations (edge : Fin outerEdges) : Configuration (4 * (4 * edges)) :=
    substitutionConfigurationEquiv (fun first => substitutionConfigurationEquiv (cells edge first))
  have hinnerConnected := diamondNetwork.substitute_all_vertices_connected S diamondRule_classical.connected hconnected
  have hmainConnected := diamondNetwork.substitute_all_vertices_connected inner diamondRule_classical.connected hinnerConnected
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
  have hmainDiameter (u v) : main.fullGraph.dist u v ≤ 4 * S.fullGraph.dist S.source S.target := by
    have hu := hmainLayers u
    have hv := hmainLayers v
    rw [hmainLength] at hu hv
    have hs := (hmainConnected u).symm.dist_triangle_left v
    have ht := ((hmainConnected u).symm.trans (hmainConnected main.target)).dist_triangle_left v
    rw [SimpleGraph.dist_comm (u := u) (v := main.source)] at hs
    rw [SimpleGraph.dist_comm (u := main.target) (v := v)] at ht
    dsimp only [main, inner] at *
    omega
  have hcoarse : main.coarseConfiguration configurations = onlyOpen mainEdge := by
    funext edge
    change main.crosses (configurations edge) = onlyOpen mainEdge edge
    by_cases hedge : edge = mainEdge
    · subst edge
      rw [show onlyOpen mainEdge mainEdge = true by simp [onlyOpen]]
      exact diamond_all_crossing_substitute_crosses inner _
        (fun first => diamond_all_crossing_substitute_crosses S _ (hmain first))
    · have hinnerClosed (first : Fin 4) : inner.crosses (substitutionConfigurationEquiv (cells edge first)) = false := by
        rw [diamondNetwork.substitute_crosses S]
        rw [show S.coarseConfiguration (cells edge first) = (fun _ => false) from funext (hother edge hedge first)]
        exact diamondNetwork.crosses_all_closed
      change (diamondNetwork.substitute inner).crosses (substitutionConfigurationEquiv _) = _
      rw [diamondNetwork.substitute_crosses inner]
      rw [show inner.coarseConfiguration (fun first => substitutionConfigurationEquiv (cells edge first)) =
        (fun _ => false) from funext hinnerClosed]
      simp [diamondNetwork.crosses_all_closed, onlyOpen, hedge]
  let quarter : S.InteriorVertex ↪ Fin (Fintype.card (diamondNetwork.SubstitutionVertex inner)) :=
    (⟨Subtype.val, Subtype.val_injective⟩ : S.InteriorVertex ↪ Fin vertices).trans
      (diamondQuarterEmbedding S)
  let selected := (S.internalSourceVertices (cells mainEdge 0 1)).map quarter
  have hbound := R.internalRadiusPointRootCount_ge_isolated_cell main houter hmainConnected configurations mainEdge
    hcoarse hfirstSource hfirstTarget hsecondSource hsecondTarget
    (4 * S.fullGraph.dist S.source S.target) (S.fullGraph.dist S.source S.target) hmainDiameter
    (fun edge hedge vertex => diamond_double_closed_terminal_bound S hconnected _ hdiameter
      (cells edge) (hother edge hedge) vertex) selected
    (by
      intro root hroot
      obtain ⟨vertex, hvertex, rfl⟩ := Finset.mem_map.mp hroot
      have hreach : (S.openGraph (cells mainEdge 0 1)).Reachable S.source vertex.val := by
        simpa only [internalSourceVertices, Finset.mem_filter, Finset.mem_univ, true_and,
          SimpleGraph.reachableDecide_eq_true] using hvertex
      obtain ⟨_, _, hs, ht, _⟩ := diamond_quarter_cell_geometry S hconnected hlayers hdiameter hpositive vertex.val
      exact ⟨diamond_quarter_source_reachable S (cells mainEdge) hmain vertex.val hreach, hs, ht⟩)
    (by
      intro root hroot
      obtain ⟨vertex, _, rfl⟩ := Finset.mem_map.mp hroot
      exact diamond_quarter_distance_witness S hconnected hlayers hdiameter hpositive hgeodesic
        (cells mainEdge) hmain vertex.val)
  have hcard : selected.card = S.internalSelectedMass true false (cells mainEdge 0 1) := by
    dsimp only [selected]
    rw [Finset.card_map, S.internalSourceVertices_card]
  rw [hcard] at hbound
  exact hbound

end
end Universality



