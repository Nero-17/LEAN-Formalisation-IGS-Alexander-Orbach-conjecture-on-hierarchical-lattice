import IGSIII4.SpectralDensity.ActualPathMassCut
import Universality.Percolation.FirstMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem active_vertex_terminal_reachable {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (state : LiveState) (vertex : Vertex blocks paths interior)
    (active : (network blocks paths interior).active state
      (fun edge => configuration ((Fintype.equivFin _).symm edge)) (Fintype.equivFin _ vertex) = true) :
    (graph blocks paths interior configuration).Reachable (source blocks paths interior) vertex ∨
      (graph blocks paths interior configuration).Reachable (target blocks paths interior) vertex := by
  simp only [FiniteNetwork.active, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true] at active
  rcases active with first | ⟨_, second⟩
  · exact Or.inl (by simpa [network, graphIso] using first.map (graphIso blocks paths interior configuration).symm.toHom)
  · exact Or.inr (by simpa [network, graphIso] using second.map (graphIso blocks paths interior configuration).symm.toHom)

theorem retained_path_edge_end_event {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (state : LiveState)
    (block : Fin blocks) (path : Fin paths) (edge : Fin (interior + 2))
    (retained : (network blocks paths interior).childState state
      (fun edge => configuration ((Fintype.equivFin _).symm edge))
        (Fintype.equivFin _ (.inr (block, path, edge))) ≠ none) :
    EdgeEndEvent blocks paths interior configuration block path edge := by
  have activeEndpoint :
      (network blocks paths interior).active state
        (fun edge => configuration ((Fintype.equivFin _).symm edge))
        (Fintype.equivFin _ (endpoint blocks paths interior (.inr (block, path, edge))).1) = true ∨
      (network blocks paths interior).active state
        (fun edge => configuration ((Fintype.equivFin _).symm edge))
        (Fintype.equivFin _ (endpoint blocks paths interior (.inr (block, path, edge))).2) = true := by
    simp only [childState, network, Equiv.symm_apply_apply] at retained
    cases first : (network blocks paths interior).active state
      (fun edge => configuration ((Fintype.equivFin _).symm edge))
      (Fintype.equivFin _ (endpoint blocks paths interior (.inr (block, path, edge))).1) <;>
      cases second : (network blocks paths interior).active state
        (fun edge => configuration ((Fintype.equivFin _).symm edge))
        (Fintype.equivFin _ (endpoint blocks paths interior (.inr (block, path, edge))).2) <;>
        simp_all only [network, Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or, if_false, ne_eq, not_true_eq_false,
          Bool.false_eq_true, or_self, or_false, or_true, true_or]
  rcases activeEndpoint with first | second
  · rcases active_vertex_terminal_reachable configuration state _ first with sourceReach | targetReach
    · exact terminal_reachable_endpoint_implies_end_event configuration 0 block path edge (Or.inl sourceReach)
    · exact terminal_reachable_endpoint_implies_end_event configuration 2 block path edge (Or.inl targetReach)
  · rcases active_vertex_terminal_reachable configuration state _ second with sourceReach | targetReach
    · exact terminal_reachable_endpoint_implies_end_event configuration 0 block path edge (Or.inr sourceReach)
    · exact terminal_reachable_endpoint_implies_end_event configuration 2 block path edge (Or.inr targetReach)

theorem liveResponse_path_end_upper (blocks paths interior : ℕ) (state : LiveState)
    (configuration : Edge blocks paths interior → Bool) :
    (network blocks paths interior).liveResponse state
      (fun edge => configuration ((Fintype.equivFin _).symm edge)) (fun _ => 1) ≤
      4 + ∑ block : Fin blocks, ∑ path : Fin paths, ∑ edge : Fin (interior + 2),
        if EdgeEndEvent blocks paths interior configuration block path edge then (1 : ℝ) else 0 := by
  classical
  unfold liveResponse
  rw [← (Fintype.equivFin (Edge blocks paths interior)).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have outerBound : (∑ outer : Fin 4, match (network blocks paths interior).childState state
      (fun edge => configuration ((Fintype.equivFin _).symm edge)) (Fintype.equivFin _ (.inl outer)) with
      | none => (0 : ℝ) | some _ => 1) ≤ 4 := by
    calc
      _ ≤ ∑ _ : Fin 4, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro outer _
        cases (network blocks paths interior).childState state
          (fun edge => configuration ((Fintype.equivFin _).symm edge)) (Fintype.equivFin _ (.inl outer)) <;> norm_num
      _ = _ := by simp
  apply add_le_add outerBound
  apply Finset.sum_le_sum
  intro block _
  apply Finset.sum_le_sum
  intro path _
  apply Finset.sum_le_sum
  intro edge _
  cases retained : (network blocks paths interior).childState state
      (fun edge => configuration ((Fintype.equivFin _).symm edge))
      (Fintype.equivFin _ (.inr (block, path, edge))) with
  | none => split_ifs <;> norm_num
  | some child =>
    have event := retained_path_edge_end_event configuration state block path edge (by rw [retained]; simp)
    simp [event]

end
end IGSIII4.SpectralDensity.ActualFamily
