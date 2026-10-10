import Universality.Percolation.MassEquivalence

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable (equivalence : R.NetworkEquivalence S)

theorem conditioning (state : LiveState) (configuration : Configuration eR) :
    S.conditioning state (equivalence.configuration configuration) = R.conditioning state configuration := by
  cases state <;> simp only [FiniteNetwork.conditioning, equivalence.crosses]

theorem active (state : LiveState) (configuration : Configuration eR) (vertex : Fin vR) :
    S.active state (equivalence.configuration configuration) (equivalence.vertex vertex) =
      R.active state configuration vertex := by
  simpa only [FiniteNetwork.active, FiniteNetwork.selectedActive, Bool.true_and] using
    equivalence.selectedActive true (state == .both) configuration vertex

theorem childState (state : LiveState) (configuration : Configuration eR) (edge : Fin eR) :
    S.childState state (equivalence.configuration configuration) (equivalence.edge edge) =
      R.childState state configuration edge := by
  unfold FiniteNetwork.childState
  rw [equivalence.endpoint]
  dsimp only
  rw [equivalence.active, equivalence.active]
  simp only [NetworkEquivalence.configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

theorem liveCount (parent child : LiveState) (configuration : Configuration eR) :
    S.liveCount parent child (equivalence.configuration configuration) =
      R.liveCount parent child configuration := by
  unfold FiniteNetwork.liveCount
  have hleft := Finset.natCast_card_filter (R := ℕ) (fun edge => S.childState parent (equivalence.configuration configuration) edge = some child) Finset.univ
  have hright := Finset.natCast_card_filter (R := ℕ) (fun edge => R.childState parent configuration edge = some child) Finset.univ
  simp only [Nat.cast_id] at hleft hright
  rw [hleft, hright]
  rw [← equivalence.edge.sum_comp]
  simp only [equivalence.childState]

include equivalence in
theorem conditioningProbability (p : ℝ) (state : LiveState) :
    S.conditioningProbability p state = R.conditioningProbability p state := by
  unfold FiniteNetwork.conditioningProbability
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.conditioning, equivalence.bernoulliWeight]

include equivalence in
theorem massMatrix (p : ℝ) : S.massMatrix p = R.massMatrix p := by
  ext parent child
  unfold FiniteNetwork.massMatrix
  rw [equivalence.conditioningProbability, ← equivalence.configuration.sum_comp]
  simp only [equivalence.conditioning, equivalence.bernoulliWeight, equivalence.liveCount]

end
end Universality.FiniteNetwork.NetworkEquivalence
