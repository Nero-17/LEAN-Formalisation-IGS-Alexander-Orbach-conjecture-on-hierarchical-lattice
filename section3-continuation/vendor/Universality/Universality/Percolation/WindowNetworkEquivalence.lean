import Universality.Percolation.DistanceWindowPairs
import Universality.Graph.NetworkEquivalence

namespace Universality.FiniteNetwork.NetworkEquivalence
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
variable (equivalence : R.NetworkEquivalence S)
include equivalence

theorem fullGraph_distance (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (first second : Fin vR) :
    S.fullGraph.dist (equivalence.vertex first) (equivalence.vertex second) =
      R.fullGraph.dist first second :=
  graph_iso_distance_of_reachable (equivalence.openGraphIso (fun _ => true))
    ((hconnected first).symm.trans (hconnected second))

theorem distanceWindowPairs_card (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (lower upper : ℝ) :
    (S.distanceWindowPairs lower upper).card = (R.distanceWindowPairs lower upper).card := by
  classical
  simp only [FiniteNetwork.distanceWindowPairs, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (Equiv.prodCongr equivalence.vertex equivalence.vertex).sum_comp]
  apply Finset.sum_congr rfl
  intro pair _
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  rw [equivalence.fullGraph_distance hconnected]

theorem connectedDistanceWindowPairs_card
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Configuration eR) (lower upper : ℝ) :
    (S.connectedDistanceWindowPairs (equivalence.configuration configuration) lower upper).card =
      (R.connectedDistanceWindowPairs configuration lower upper).card := by
  classical
  simp only [FiniteNetwork.connectedDistanceWindowPairs, FiniteNetwork.distanceWindowPairs,
    Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← (Equiv.prodCongr equivalence.vertex equivalence.vertex).sum_comp]
  apply Finset.sum_congr rfl
  intro pair _
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hreach : (S.openGraph (equivalence.configuration configuration)).Reachable
      (equivalence.vertex pair.1) (equivalence.vertex pair.2) ↔
      (R.openGraph configuration).Reachable pair.1 pair.2 :=
    (equivalence.openGraphIso configuration).reachable_iff
  simp only [equivalence.fullGraph_distance hconnected, hreach]

/-- Averaging over the actual Bernoulli law and an actual deterministic
distance window is invariant under network relabelling. -/
theorem averagedWindowConnectivity
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (p lower upper : ℝ) :
    S.averagedWindowConnectivity p lower upper = R.averagedWindowConnectivity p lower upper := by
  unfold FiniteNetwork.averagedWindowConnectivity
  rw [equivalence.distanceWindowPairs_card hconnected, ← equivalence.configuration.sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro configuration _
  rw [equivalence.bernoulliWeight, equivalence.connectedDistanceWindowPairs_card hconnected]

end
end Universality.FiniteNetwork.NetworkEquivalence
