import IGSIII4.SpectralDensity.ActualFamily20261012
import Universality.Graph.IncidentDegree
import Universality.Graph.TerminalEdgeConnectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

/-- Exactly the short first edge and the first exterior edge meet the source. -/
theorem source_incident_edges20261012 (blocks paths interior : ℕ) :
    (network blocks paths interior).sourceIncidentEdges =
      {Fintype.equivFin (Edge blocks paths interior) (.inl 0),
       Fintype.equivFin (Edge blocks paths interior) (.inl 2)} := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := (Fintype.equivFin (Edge blocks paths interior)).surjective edge
  simp only [sourceIncidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    network, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq,
    Finset.mem_insert, Finset.mem_singleton]
  rcases edge with edge | ⟨block, path, position⟩
  · fin_cases edge <;> simp [endpoint, source, midpoint, target]
  · simp only [endpoint, pathVertex]
    split_ifs <;> simp [source]

theorem source_incident_edges_card20261012 (blocks paths interior : ℕ) :
    (network blocks paths interior).sourceIncidentEdges.card = 2 := by
  classical
  rw [source_incident_edges20261012]
  have distinct : Fintype.equivFin (Edge blocks paths interior) (Sum.inl 0) ≠
      Fintype.equivFin (Edge blocks paths interior) (Sum.inl 2) := by
    intro equal
    have same := (Fintype.equivFin (Edge blocks paths interior)).injective equal
    simpa using same
  simp [distinct]

theorem source_degree20261012 (blocks paths interior : ℕ) :
    (network blocks paths interior).fullGraph.degree (network blocks paths interior).source = 2 := by
  rw [← (network blocks paths interior).sourceIncidentEdges_card_eq_degree (simple blocks paths interior)]
  exact source_incident_edges_card20261012 blocks paths interior

theorem target_degree20261012 (blocks paths interior : ℕ) :
    (network blocks paths interior).fullGraph.degree (network blocks paths interior).target = 2 := by
  classical
  have neighbors : (graph blocks paths interior (fun _ => true)).neighborFinset
      (target blocks paths interior) =
      {midpoint blocks paths interior, Sum.inr (Sum.inl (Fin.last blocks))} := by
    ext vertex
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, edge, _, forward | backward⟩
      all_goals rcases edge with edge | ⟨block, path, position⟩
      · fin_cases edge <;> simp_all [endpoint, source, midpoint, target]
      · have impossible := congrArg Prod.fst forward
        simp only [endpoint, pathVertex] at impossible
        split_ifs at impossible <;> simp_all [target]
      · fin_cases edge <;> simp_all [endpoint, source, midpoint, target]
      · have impossible := congrArg Prod.snd backward
        simp only [endpoint, pathVertex] at impossible
        split_ifs at impossible <;> simp_all [target]
    · rintro (rfl | rfl)
      · simpa [endpoint] using
          (graph_edge blocks paths interior (fun _ => true) (.inl 1) rfl).symm
      · simpa [endpoint] using
          (graph_edge blocks paths interior (fun _ => true) (.inl 3) rfl).symm
  have degree := (graphIso blocks paths interior (fun _ => true)).degree_eq
    (target blocks paths interior)
  change (network blocks paths interior).fullGraph.degree (network blocks paths interior).target =
    (graph blocks paths interior (fun _ => true)).degree (target blocks paths interior) at degree
  rw [degree, ← SimpleGraph.card_neighborFinset_eq_degree, neighbors]
  simp [midpoint]

/-- The minimum separating edge cut is exactly two: every singleton deletion
survives, and deleting the two source-incident edges separates the terminals. -/
theorem terminal_mincut20261012 (blocks paths interior : ℕ) (pathsPositive : 0 < paths) :
    (network blocks paths interior).terminalEdgeConnectivity = 2 := by
  classical
  have lower : 2 ≤ (network blocks paths interior).terminalEdgeConnectivity :=
    ((network blocks paths interior).terminalEdgeConnectivity_at_least_two_iff
      (network_connected blocks paths interior pathsPositive _)).mpr
      (one_edge_deletion_survives blocks paths interior pathsPositive)
  have cut : (network blocks paths interior).IsTerminalCut
      (network blocks paths interior).sourceIncidentEdges := by
    apply Bool.eq_false_iff.mpr
    intro crossing
    obtain ⟨edge, incident, opened⟩ :=
      (network blocks paths interior).exists_open_source_incident_edge
        (fun edge => decide (edge ∉ (network blocks paths interior).sourceIncidentEdges)) crossing
    simpa [incident] using opened
  have upper := (network blocks paths interior).terminalEdgeConnectivity_le
    (network blocks paths interior).sourceIncidentEdges cut
  rw [source_incident_edges_card20261012] at upper
  exact Nat.le_antisymm upper lower

/-- The actual finite Appendix C rule has all four advertised terminal
parameters equal to two, at every admissible family index. -/
theorem appendixRule_terminal_parameters20261012 (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length) :
    (appendixRule base length).network.fullGraph.dist
      (appendixRule base length).network.source (appendixRule base length).network.target = 2 ∧
    (appendixRule base length).network.fullGraph.degree (appendixRule base length).network.source = 2 ∧
    (appendixRule base length).network.fullGraph.degree (appendixRule base length).network.target = 2 ∧
    (appendixRule base length).network.terminalEdgeConnectivity = 2 := by
  have pathsPositive : 0 < ⌈(length : ℝ) * (4 / 3 : ℝ) ^ length⌉₊ := by
    apply Nat.ceil_pos.mpr
    exact mul_pos (by exact_mod_cast (show 0 < length by omega)) (pow_pos (by norm_num) _)
  exact ⟨terminal_distance _ _ _, source_degree20261012 _ _ _,
    target_degree20261012 _ _ _, terminal_mincut20261012 _ _ _ pathsPositive⟩

end
end IGSIII4.SpectralDensity.ActualFamily
