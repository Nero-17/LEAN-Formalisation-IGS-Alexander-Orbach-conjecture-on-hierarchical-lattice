import IGSIII.Mass.FourStateMassLimit
import Universality.Graph.CanonicalPivotal

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

theorem orientedMassMatrix_pos_of_witness (network : FiniteNetwork vertices edges)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : network.reliability p = p) (parent child : MassLiveState)
    (configuration : Configuration edges) (edge : Fin edges)
    (crossing : network.crosses configuration = (parent.erase == .connected))
    (label : network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge = child.oriented) :
    0 < network.orientedMassMatrix p parent child := by
  have weight_positive : 0 < network.conditionalCellWeight p (parent.erase == .connected) configuration := by
    unfold conditionalCellWeight
    rw [crossing]
    simp only [if_pos rfl]
    apply div_pos (bernoulliWeight_pos positive below_one configuration)
    split_ifs <;> rw [fixed_point] <;> linarith
  have count_positive : 0 < network.orientedLiveCount parent.sourceSelected parent.targetSelected configuration child.oriented := by
    apply lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    unfold orientedLiveCount
    calc
      (1 : ℝ) = if network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge = child.oriented then 1 else 0 := by rw [if_pos label]
      _ ≤ _ := Finset.single_le_sum
        (f := fun other : Fin edges => if network.orientedChildState parent.sourceSelected parent.targetSelected configuration other = child.oriented then (1 : ℝ) else 0)
        (fun other _ => by split_ifs <;> norm_num) (Finset.mem_univ edge)
  apply lt_of_lt_of_le (mul_pos weight_positive count_positive)
  unfold orientedMassMatrix
  apply Finset.single_le_sum _ (Finset.mem_univ configuration)
  intro configuration _
  apply mul_nonneg (network.conditionalCellWeight_nonneg positive.le below_one.le _ _)
  unfold orientedLiveCount
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem orientedChildState_allClosed_both_sourceOnly (network : FiniteNetwork vertices edges)
    (edge : Fin edges)
    (first_terminal : (network.endpoint edge).1 = network.source ∨ (network.endpoint edge).1 = network.target)
    (second_source : (network.endpoint edge).2 ≠ network.source)
    (second_target : (network.endpoint edge).2 ≠ network.target) :
    network.orientedChildState true true (fun _ => false) edge = .sourceOnly := by
  rcases first_terminal with first_terminal | first_terminal <;>
    simp [orientedChildState, selectedActive, network.reachableDecide_all_closed,
      orientedStateOf, first_terminal, Ne.symm second_source, Ne.symm second_target]

theorem orientedChildState_allClosed_both_targetOnly (network : FiniteNetwork vertices edges)
    (edge : Fin edges)
    (second_terminal : (network.endpoint edge).2 = network.source ∨ (network.endpoint edge).2 = network.target)
    (first_source : (network.endpoint edge).1 ≠ network.source)
    (first_target : (network.endpoint edge).1 ≠ network.target) :
    network.orientedChildState true true (fun _ => false) edge = .targetOnly := by
  rcases second_terminal with second_terminal | second_terminal <;>
    simp [orientedChildState, selectedActive, network.reachableDecide_all_closed,
      orientedStateOf, second_terminal, Ne.symm first_source, Ne.symm first_target]

/-- Closing a pivotal terminal-incident edge exposes the opposite orientation
under the one-terminal mask, on a genuine noncrossing configuration. -/
theorem pivotal_target_first_source_mask (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (edge : Fin edges)
    (pivotal : network.pivotal configuration edge = true)
    (first_target : (network.endpoint edge).1 = network.target) :
    network.crosses (Function.update configuration edge false) = false ∧
      network.orientedChildState true false (Function.update configuration edge false) edge = .targetOnly := by
  have disconnected : network.crosses (Function.update configuration edge false) = false := by
    simpa only [FiniteNetwork.pivotal, Bool.and_eq_true, Bool.not_eq_true'] using
      (show network.crosses (Function.update configuration edge true) = true ∧
        network.crosses (Function.update configuration edge false) = false from by
          simpa only [FiniteNetwork.pivotal, Bool.and_eq_true, Bool.not_eq_true'] using pivotal).2
  have pivotal_closed : network.pivotal (Function.update configuration edge false) edge = true := by
    simpa only [network.pivotal_update] using pivotal
  have no_crossing : ¬(network.openGraph (Function.update configuration edge false)).Reachable network.source network.target := by
    intro connected
    have crossing := (network.crosses_eq_true _).mpr connected
    rw [disconnected] at crossing
    contradiction
  have bridge := (network.pivotal_of_disconnected_iff _ edge disconnected).mp pivotal_closed
  have source_second : (network.openGraph (Function.update configuration edge false)).Reachable network.source
      (network.endpoint edge).2 := by
    rcases bridge with bridge | bridge
    · exact (no_crossing (first_target ▸ bridge.1)).elim
    · exact bridge.1
  refine ⟨disconnected, ?_⟩
  have first_inactive : (network.openGraph (Function.update configuration edge false)).reachableDecide network.source
      (network.endpoint edge).1 = false := by
    rw [first_target]
    exact Bool.eq_false_iff.mpr (fun reachable => no_crossing
      (((network.openGraph (Function.update configuration edge false)).reachableDecide_eq_true _ _).mp reachable))
  have second_active := ((network.openGraph (Function.update configuration edge false)).reachableDecide_eq_true _ _).mpr source_second
  simp [orientedChildState, selectedActive, orientedStateOf, first_inactive, second_active]

theorem pivotal_source_second_target_mask (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (edge : Fin edges)
    (pivotal : network.pivotal configuration edge = true)
    (second_source : (network.endpoint edge).2 = network.source) :
    network.crosses (Function.update configuration edge false) = false ∧
      network.orientedChildState false true (Function.update configuration edge false) edge = .sourceOnly := by
  have disconnected : network.crosses (Function.update configuration edge false) = false := by
    simpa only [FiniteNetwork.pivotal, Bool.and_eq_true, Bool.not_eq_true'] using
      (show network.crosses (Function.update configuration edge true) = true ∧
        network.crosses (Function.update configuration edge false) = false from by
          simpa only [FiniteNetwork.pivotal, Bool.and_eq_true, Bool.not_eq_true'] using pivotal).2
  have pivotal_closed : network.pivotal (Function.update configuration edge false) edge = true := by
    simpa only [network.pivotal_update] using pivotal
  have no_crossing : ¬(network.openGraph (Function.update configuration edge false)).Reachable network.target network.source := by
    intro connected
    have crossing := (network.crosses_eq_true _).mpr connected.symm
    rw [disconnected] at crossing
    contradiction
  have bridge := (network.pivotal_of_disconnected_iff _ edge disconnected).mp pivotal_closed
  have target_first : (network.openGraph (Function.update configuration edge false)).Reachable network.target
      (network.endpoint edge).1 := by
    rcases bridge with bridge | bridge
    · exact (no_crossing (second_source ▸ bridge.2)).elim
    · exact bridge.2
  refine ⟨disconnected, ?_⟩
  have second_inactive : (network.openGraph (Function.update configuration edge false)).reachableDecide network.target
      (network.endpoint edge).2 = false := by
    rw [second_source]
    exact Bool.eq_false_iff.mpr (fun reachable => no_crossing
      (((network.openGraph (Function.update configuration edge false)).reachableDecide_eq_true _ _).mp reachable))
  have first_active := ((network.openGraph (Function.update configuration edge false)).reachableDecide_eq_true _ _).mpr target_first
  simp [orientedChildState, selectedActive, orientedStateOf, second_inactive, first_active]

end Universality.FiniteNetwork
