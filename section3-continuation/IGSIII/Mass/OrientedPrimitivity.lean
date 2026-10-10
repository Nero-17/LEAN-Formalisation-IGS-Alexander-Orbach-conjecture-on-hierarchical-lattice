import IGSIII.Mass.OrientedTransitions

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Universality

open Matrix FiniteNetwork

/-- Four transitions suffice once B reaches both one-arm orientations either
directly or through one further one-arm transition. -/
theorem four_state_fourth_power_pos (offspring : Matrix MassLiveState MassLiveState ℝ)
    (nonnegative : ∀ parent child, 0 ≤ offspring parent child)
    (connected_column : ∀ parent, 0 < offspring parent .connected)
    (connected_both : 0 < offspring .connected .both)
    (one_arm_accessible :
      (0 < offspring .both .sourceOnly ∧ 0 < offspring .both .targetOnly) ∨
      (0 < offspring .both .sourceOnly ∧ 0 < offspring .sourceOnly .targetOnly) ∨
      (0 < offspring .both .targetOnly ∧ 0 < offspring .targetOnly .sourceOnly)) :
    ∀ parent child, 0 < (offspring ^ 4) parent child := by
  intro parent child
  cases child with
  | connected =>
    exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .connected .connected
      (connected_column parent) (connected_column .connected) (connected_column .connected) (connected_column .connected)
  | both =>
    exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .connected .both
      (connected_column parent) (connected_column .connected) (connected_column .connected) connected_both
  | sourceOnly =>
    rcases one_arm_accessible with both | source | target
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .both .sourceOnly
        (connected_column parent) (connected_column .connected) connected_both both.1
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .both .sourceOnly
        (connected_column parent) (connected_column .connected) connected_both source.1
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .both .targetOnly .sourceOnly
        (connected_column parent) connected_both target.1 target.2
  | targetOnly =>
    rcases one_arm_accessible with both | source | target
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .both .targetOnly
        (connected_column parent) (connected_column .connected) connected_both both.2
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .both .sourceOnly .targetOnly
        (connected_column parent) connected_both source.1 source.2
    · exact matrix_power_four_pos_of_path offspring nonnegative parent .connected .connected .both .targetOnly
        (connected_column parent) (connected_column .connected) connected_both target.1

end Universality

namespace Universality.Rule

open FiniteNetwork Matrix

/-- The orientation bridge is obtained from actual configurations: all-closed
at B, and a closed pivotal terminal edge for the missing orientation. -/
theorem Classical.oriented_one_arm_accessible {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    (0 < rule.network.orientedMassMatrix p .both .sourceOnly ∧
      0 < rule.network.orientedMassMatrix p .both .targetOnly) ∨
    (0 < rule.network.orientedMassMatrix p .both .sourceOnly ∧
      0 < rule.network.orientedMassMatrix p .sourceOnly .targetOnly) ∨
    (0 < rule.network.orientedMassMatrix p .both .targetOnly ∧
      0 < rule.network.orientedMassMatrix p .targetOnly .sourceOnly) := by
  obtain ⟨source_edge, source_incident⟩ := rule.network.exists_source_incident_edge (classicalRule.connected _)
  obtain ⟨source_first_not_target, source_second_not_target⟩ := rule.network.incident_endpoints_ne_target
    source_edge source_incident classicalRule.scale
  have reverse_connected : rule.network.reverse.fullGraph.Reachable rule.network.reverse.source rule.network.reverse.target :=
    (classicalRule.connected rule.network.target).symm
  obtain ⟨target_edge, target_incident⟩ := rule.network.reverse.exists_source_incident_edge reverse_connected
  have reverse_scale : 1 < rule.network.reverse.fullGraph.dist rule.network.reverse.source rule.network.reverse.target := by
    change 1 < rule.network.fullGraph.dist rule.network.target rule.network.source
    rw [SimpleGraph.dist_comm]
    exact classicalRule.scale
  obtain ⟨target_first_not_source, target_second_not_source⟩ := rule.network.reverse.incident_endpoints_ne_target
    target_edge target_incident reverse_scale
  change (rule.network.endpoint target_edge).1 = rule.network.target ∨
    (rule.network.endpoint target_edge).2 = rule.network.target at target_incident
  change (rule.network.endpoint target_edge).1 ≠ rule.network.source at target_first_not_source
  change (rule.network.endpoint target_edge).2 ≠ rule.network.source at target_second_not_source
  have source_forward (first_source : (rule.network.endpoint source_edge).1 = rule.network.source) :
      0 < rule.network.orientedMassMatrix p .both .sourceOnly := by
    apply rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .both .sourceOnly
      (fun _ => false) source_edge (rule.network.crosses_all_closed)
    apply rule.network.orientedChildState_allClosed_both_sourceOnly source_edge (Or.inl first_source)
    · intro second_source
      exact rule.network.loopless source_edge (first_source.trans second_source.symm)
    · exact source_second_not_target
  have source_backward (second_source : (rule.network.endpoint source_edge).2 = rule.network.source) :
      0 < rule.network.orientedMassMatrix p .both .targetOnly := by
    apply rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .both .targetOnly
      (fun _ => false) source_edge (rule.network.crosses_all_closed)
    apply rule.network.orientedChildState_allClosed_both_targetOnly source_edge (Or.inl second_source)
    · intro first_source
      exact rule.network.loopless source_edge (first_source.trans second_source.symm)
    · exact source_first_not_target
  have target_forward (first_target : (rule.network.endpoint target_edge).1 = rule.network.target) :
      0 < rule.network.orientedMassMatrix p .both .sourceOnly := by
    apply rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .both .sourceOnly
      (fun _ => false) target_edge (rule.network.crosses_all_closed)
    apply rule.network.orientedChildState_allClosed_both_sourceOnly target_edge (Or.inr first_target)
    · exact target_second_not_source
    · intro second_target
      exact rule.network.loopless target_edge (first_target.trans second_target.symm)
  have target_backward (second_target : (rule.network.endpoint target_edge).2 = rule.network.target) :
      0 < rule.network.orientedMassMatrix p .both .targetOnly := by
    apply rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .both .targetOnly
      (fun _ => false) target_edge (rule.network.crosses_all_closed)
    apply rule.network.orientedChildState_allClosed_both_targetOnly target_edge (Or.inr second_target)
    · exact target_first_not_source
    · intro first_target
      exact rule.network.loopless target_edge (first_target.trans second_target.symm)
  have source_to_target (first_target : (rule.network.endpoint target_edge).1 = rule.network.target) :
      0 < rule.network.orientedMassMatrix p .sourceOnly .targetOnly := by
    obtain ⟨walk, simple_path, edge_on_path⟩ := classicalRule.canonical target_edge
    obtain ⟨configuration, pivotal⟩ := rule.network.exists_pivotal_of_path classicalRule.simple
      target_edge walk simple_path edge_on_path
    obtain ⟨disconnected, child⟩ := rule.network.pivotal_target_first_source_mask configuration target_edge pivotal first_target
    exact rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .sourceOnly .targetOnly
      (Function.update configuration target_edge false) target_edge disconnected child
  have target_to_source (second_source : (rule.network.endpoint source_edge).2 = rule.network.source) :
      0 < rule.network.orientedMassMatrix p .targetOnly .sourceOnly := by
    obtain ⟨walk, simple_path, edge_on_path⟩ := classicalRule.canonical source_edge
    obtain ⟨configuration, pivotal⟩ := rule.network.exists_pivotal_of_path classicalRule.simple
      source_edge walk simple_path edge_on_path
    obtain ⟨disconnected, child⟩ := rule.network.pivotal_source_second_target_mask configuration source_edge pivotal second_source
    exact rule.network.orientedMassMatrix_pos_of_witness p positive below_one fixed_point .targetOnly .sourceOnly
      (Function.update configuration source_edge false) source_edge disconnected child
  rcases source_incident with source_incident | source_incident
  · rcases target_incident with target_incident | target_incident
    · exact Or.inr (Or.inl ⟨source_forward source_incident, source_to_target target_incident⟩)
    · exact Or.inl ⟨source_forward source_incident, target_backward target_incident⟩
  · rcases target_incident with target_incident | target_incident
    · exact Or.inl ⟨target_forward target_incident, source_backward source_incident⟩
    · exact Or.inr (Or.inr ⟨source_backward source_incident, target_to_source source_incident⟩)

/-- An explicit primitivity exponent for the actual four-type offspring
matrix. The orientation bridge uses classical canonicality. -/
theorem Classical.orientedMassMatrix_fourth_power_pos {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1) (fixed_point : rule.network.reliability p = p) :
    ∀ parent child, 0 < (rule.network.orientedMassMatrix p ^ 4) parent child := by
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have connected_three := (rule.network.massPlaneBlock_pos_of_geometry positive below_one
    (classicalRule.connected _) classicalRule.scale classicalRule.cut).2
  have connected_column (parent : MassLiveState) : 0 < rule.network.orientedMassMatrix p parent .connected := by
    have equality := congrFun (rule.network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap
      (fun state => if state = .connected then 1 else 0)) parent
    simp [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState, MassLiveState.erase] at equality
    rw [equality]
    exact connected_three parent.erase
  have connected_both : 0 < rule.network.orientedMassMatrix p .connected .both := by
    obtain ⟨edge, child⟩ := rule.network.exists_closed_edge_both_endpoints_active
      (classicalRule.connected _) classicalRule.cut
    have three_positive := (rule.network.massMatrix_pos_iff positive below_one .connected .both).mpr
      ⟨onlyClosed edge, edge, classicalRule.cut edge, child⟩
    have equality := congrFun (rule.network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap
      (fun state => if state = .both then 1 else 0)) .connected
    simp [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState, MassLiveState.erase] at equality
    rwa [equality]
  exact four_state_fourth_power_pos _ (rule.network.orientedMassMatrix_nonnegative p positive.le below_one.le)
    connected_column connected_both (classicalRule.oriented_one_arm_accessible p positive below_one fixed_point)

end Universality.Rule
