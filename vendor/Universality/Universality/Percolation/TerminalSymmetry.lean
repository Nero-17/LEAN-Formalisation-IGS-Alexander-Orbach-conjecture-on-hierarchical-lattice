import Universality.Graph.NetworkSymmetry

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def reverse : FiniteNetwork vertices edges where
  endpoint := R.endpoint
  source := R.target
  target := R.source
  terminals_distinct := R.terminals_distinct.symm
  loopless := R.loopless

theorem reverse_endpoint (e : Fin edges) : R.reverse.endpoint e = R.endpoint e := rfl

theorem crosses_reverse (ω : Configuration edges) : R.reverse.crosses ω = R.crosses ω := by
  apply Bool.eq_iff_iff.mpr
  rw [crosses_eq_true, crosses_eq_true]
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

theorem conditioning_reverse (σ : LiveState) (ω : Configuration edges) :
    R.reverse.conditioning σ ω = R.conditioning σ ω := by
  cases σ <;> simp only [conditioning, crosses_reverse]

theorem conditioningProbability_reverse (p : ℝ) (σ : LiveState) :
    R.reverse.conditioningProbability p σ = R.conditioningProbability p σ := by
  simp only [conditioningProbability, conditioning_reverse]

namespace NetworkSymmetry
variable {R} (s : R.NetworkSymmetry)
variable (hs : s.vertex R.source = R.target) (ht : s.vertex R.target = R.source)

theorem reachableDecide_configuration (ω : Configuration edges) (u v : Fin vertices) :
    (R.openGraph (s.configurationEquiv ω)).reachableDecide (s.vertex u) (s.vertex v) =
      (R.openGraph ω).reachableDecide u v := by
  apply Bool.eq_iff_iff.mpr
  rw [SimpleGraph.reachableDecide_eq_true, SimpleGraph.reachableDecide_eq_true]
  exact s.reachable_configuration_iff ω u v

include hs ht

theorem active_configuration_reverse (σ : LiveState) (ω : Configuration edges)
    (v : Fin vertices) :
    R.active σ (s.configurationEquiv ω) (s.vertex v) = R.reverse.active σ ω v := by
  have hsource := s.reachableDecide_configuration ω R.target v
  have htarget := s.reachableDecide_configuration ω R.source v
  rw [ht] at hsource
  rw [hs] at htarget
  unfold active
  rw [hsource, htarget]
  rfl

theorem conditioning_configuration_reverse (σ : LiveState) (ω : Configuration edges) :
    R.conditioning σ (s.configurationEquiv ω) = R.reverse.conditioning σ ω := by
  cases σ <;> simp only [conditioning,
    s.crosses_configuration_of_terminal_swap hs ht, crosses_reverse]

theorem childState_configuration_reverse (σ : LiveState) (ω : Configuration edges)
    (e : Fin edges) :
    R.childState σ (s.configurationEquiv ω) (s.edge e) = R.reverse.childState σ ω e := by
  rcases s.endpoint e with h | h
  · simp only [childState, reverse_endpoint, h, s.active_configuration_reverse hs ht,
      configuration_apply, Equiv.symm_apply_apply]
    rfl
  · simp only [childState, reverse_endpoint, h, s.active_configuration_reverse hs ht,
      configuration_apply, Equiv.symm_apply_apply, Bool.and_comm, Bool.or_comm]
    rfl

theorem liveCount_configuration_reverse (σ τ : LiveState) (ω : Configuration edges) :
    R.liveCount σ τ (s.configurationEquiv ω) = R.reverse.liveCount σ τ ω := by
  classical
  unfold liveCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← s.edge.sum_comp (fun e =>
    if R.childState σ (s.configurationEquiv ω) e = some τ then (1 : ℕ) else 0)]
  simp only [s.childState_configuration_reverse hs ht]

theorem massMatrix_reverse (p : ℝ) : R.reverse.massMatrix p = R.massMatrix p := by
  classical
  ext σ τ
  simp only [massMatrix, conditioningProbability_reverse]
  congr 1
  symm
  rw [← s.configurationEquiv.sum_comp (fun ω =>
    if R.conditioning σ ω then bernoulliWeight p ω * R.liveCount σ τ ω else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [s.conditioning_configuration_reverse hs ht,
    s.bernoulliWeight_configuration, s.liveCount_configuration_reverse hs ht]

end NetworkSymmetry
end
end Universality.FiniteNetwork
