import IGSIII.Mass.OrientedVectorLimit

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

theorem orientedLeftLift_erase (offspring : Matrix MassLiveState MassLiveState ℝ)
    (radius : ℝ) (left : LiveState → ℝ) :
    orientedLeftLift offspring radius left .connected = left .connected ∧
    orientedLeftLift offspring radius left .both = left .both ∧
    orientedLeftLift offspring radius left .sourceOnly +
      orientedLeftLift offspring radius left .targetOnly = left .single := by
  refine ⟨rfl, rfl, ?_⟩
  simp [orientedLeftLift]

theorem orientedLeftLift_dotProduct (offspring : Matrix MassLiveState MassLiveState ℝ)
    (radius : ℝ) (left right : LiveState → ℝ) :
    orientedLeftLift offspring radius left ⬝ᵥ (fun state => right state.erase) = left ⬝ᵥ right := by
  simp only [dotProduct, sum_massLiveState, sum_liveState, orientedLeftLift, MassLiveState.erase]
  ring

/-- The explicit oriented limit vector is the left Perron eigenvector of the
genuine four-type offspring matrix, with precisely the original normalization. -/
theorem orientedLeftLift_eigenvector (network : FiniteNetwork vertices edges) (p radius : ℝ)
    (symmetry : network.NetworkSymmetry)
    (source_swap : symmetry.vertex network.source = network.target)
    (target_swap : symmetry.vertex network.target = network.source)
    (left : LiveState → ℝ) (eigenvector : left ᵥ* network.massMatrix p = radius • left)
    (denominator_nonzero : radius - (network.orientedMassMatrix p .sourceOnly .sourceOnly -
      network.orientedMassMatrix p .targetOnly .sourceOnly) ≠ 0) :
    orientedLeftLift (network.orientedMassMatrix p) radius left ᵥ* network.orientedMassMatrix p =
      radius • orientedLeftLift (network.orientedMassMatrix p) radius left := by
  have connected_columns (parent : MassLiveState) :
      network.orientedMassMatrix p parent .connected = network.massMatrix p parent.erase .connected := by
    have equality := congrFun (network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap
      (fun state => if state = .connected then 1 else 0)) parent
    simpa [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState, MassLiveState.erase] using equality
  have both_columns (parent : MassLiveState) :
      network.orientedMassMatrix p parent .both = network.massMatrix p parent.erase .both := by
    have equality := congrFun (network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap
      (fun state => if state = .both then 1 else 0)) parent
    simpa [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState, MassLiveState.erase] using equality
  have single_columns (parent : MassLiveState) :
      network.orientedMassMatrix p parent .sourceOnly + network.orientedMassMatrix p parent .targetOnly =
        network.massMatrix p parent.erase .single := by
    have equality := congrFun (network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap
      (fun state => if state = .single then 1 else 0)) parent
    simpa [Matrix.mulVec, dotProduct, sum_massLiveState, sum_liveState, MassLiveState.erase] using equality
  have three_state (child : LiveState) := congrFun eigenvector child
  simp only [Matrix.vecMul, dotProduct, sum_liveState, Pi.smul_apply, smul_eq_mul] at three_state
  have source_equation :
      orientedLeftLift (network.orientedMassMatrix p) radius left .connected * network.orientedMassMatrix p .connected .sourceOnly +
      orientedLeftLift (network.orientedMassMatrix p) radius left .both * network.orientedMassMatrix p .both .sourceOnly +
      orientedLeftLift (network.orientedMassMatrix p) radius left .sourceOnly * network.orientedMassMatrix p .sourceOnly .sourceOnly +
      orientedLeftLift (network.orientedMassMatrix p) radius left .targetOnly * network.orientedMassMatrix p .targetOnly .sourceOnly =
        radius * orientedLeftLift (network.orientedMassMatrix p) radius left .sourceOnly := by
    simp only [orientedLeftLift]
    field_simp [denominator_nonzero]
    ring
  ext child
  simp only [Matrix.vecMul, dotProduct, sum_massLiveState, Pi.smul_apply, smul_eq_mul]
  cases child with
  | connected =>
    simp only [connected_columns, MassLiveState.erase, orientedLeftLift]
    nlinarith [three_state .connected]
  | both =>
    simp only [both_columns, MassLiveState.erase, orientedLeftLift]
    nlinarith [three_state .both]
  | sourceOnly => exact source_equation
  | targetOnly =>
    have collapsed := (orientedLeftLift_erase (network.orientedMassMatrix p) radius left).2.2
    have column_connected := single_columns .connected
    have column_both := single_columns .both
    have column_source := single_columns .sourceOnly
    have column_target := single_columns .targetOnly
    simp only [MassLiveState.erase] at column_connected column_both column_source column_target
    rw [show orientedLeftLift (network.orientedMassMatrix p) radius left .targetOnly = left .single -
      orientedLeftLift (network.orientedMassMatrix p) radius left .sourceOnly from by linarith [collapsed]] at source_equation ⊢
    simp only [show orientedLeftLift (network.orientedMassMatrix p) radius left .connected = left .connected from rfl,
      show orientedLeftLift (network.orientedMassMatrix p) radius left .both = left .both from rfl] at source_equation ⊢
    rw [show network.orientedMassMatrix p .connected .targetOnly =
      network.massMatrix p .connected .single - network.orientedMassMatrix p .connected .sourceOnly by linarith,
      show network.orientedMassMatrix p .both .targetOnly =
      network.massMatrix p .both .single - network.orientedMassMatrix p .both .sourceOnly by linarith,
      show network.orientedMassMatrix p .sourceOnly .targetOnly =
      network.massMatrix p .single .single - network.orientedMassMatrix p .sourceOnly .sourceOnly by linarith,
      show network.orientedMassMatrix p .targetOnly .targetOnly =
      network.massMatrix p .single .single - network.orientedMassMatrix p .targetOnly .sourceOnly by linarith]
    nlinarith [three_state .single]

end Universality.FiniteNetwork
