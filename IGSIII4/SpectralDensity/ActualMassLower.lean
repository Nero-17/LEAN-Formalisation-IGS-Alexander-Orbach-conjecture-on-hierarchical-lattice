import IGSIII4.SpectralDensity.EdgeAssociation
import Universality.Percolation.LocalMassResponse

/-! A lower bound on the actual connected offspring entry from retained
first edges of an increasing subevent of terminal crossing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity
noncomputable section
open Universality Universality.FiniteNetwork
attribute [local instance] Classical.propDecidable

theorem connected_mass_lower_of_increasing_subcrossing
    {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (critical : network.reliability probability = probability)
    (selectedEdges : Finset (Fin edges)) (event : Configuration edges → Prop)
    (subcrossing : ∀ configuration, event configuration → network.crosses configuration = true)
    (increasing : ∀ edge ∈ selectedEdges, ∀ rest : RemainingConfiguration edge,
      event (insertEdge edge false rest) → event (insertEdge edge true rest))
    (retained : ∀ configuration, event configuration → ∀ edge ∈ selectedEdges,
      configuration edge = true → network.childState .connected configuration edge = some .connected) :
    (selectedEdges.card : ℝ) *
      expectation probability (fun configuration => if event configuration then 1 else 0) ≤
      network.massMatrix probability .connected .connected := by
  classical
  have pointwise (configuration : Configuration edges) :
      (∑ edge ∈ selectedEdges, if configuration edge = true ∧ event configuration then (1 : ℝ) else 0) ≤
        if network.crosses configuration then
          (network.liveCount .connected .connected configuration : ℝ) else 0 := by
    by_cases occurs : event configuration
    · rw [subcrossing configuration occurs]
      simp only [↓reduceIte]
      calc
        _ ≤ ∑ edge ∈ selectedEdges,
            if network.childState .connected configuration edge = some .connected then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro edge member
          by_cases opened : configuration edge = true
          · simp [opened, occurs, retained configuration occurs edge member opened]
          · by_cases child : network.childState .connected configuration edge = some .connected
            <;> simp [opened, child]
        _ ≤ ∑ edge : Fin edges,
            if network.childState .connected configuration edge = some .connected then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro edge _ _
          split_ifs <;> norm_num
        _ = _ := by
          simp only [liveCount, Finset.card_eq_sum_ones, Nat.cast_sum,
            Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    · simp only [occurs, and_false, if_false, Finset.sum_const_zero]
      split_ifs <;> positivity
  have numeratorLower :
      (selectedEdges.card : ℝ) * probability *
        expectation probability (fun configuration => if event configuration then 1 else 0) ≤
      ∑ configuration : Configuration edges,
        if network.crosses configuration then
          bernoulliWeight probability configuration *
            (network.liveCount .connected .connected configuration : ℝ) else 0 := by
    calc
      _ = ∑ edge ∈ selectedEdges, probability *
          expectation probability (fun configuration => if event configuration then 1 else 0) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ edge ∈ selectedEdges,
          expectation probability (fun configuration =>
            if configuration edge = true ∧ event configuration then 1 else 0) := by
        apply Finset.sum_le_sum
        intro edge member
        exact bernoulli_open_event_positive_association event probability positive.le belowOne.le
          edge (increasing edge member)
      _ = ∑ configuration : Configuration edges,
          bernoulliWeight probability configuration *
            (∑ edge ∈ selectedEdges, if configuration edge = true ∧ event configuration then 1 else 0) := by
        unfold expectation
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro configuration _
        exact (Finset.mul_sum ..).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro configuration _
        have bound := mul_le_mul_of_nonneg_left (pointwise configuration)
          (bernoulliWeight_nonneg positive.le belowOne.le configuration)
        simpa only [mul_ite, mul_zero] using bound
  unfold massMatrix
  rw [network.conditioningProbability_connected, critical]
  change _ ≤ (∑ configuration : Configuration edges,
    if network.crosses configuration then bernoulliWeight probability configuration *
      (network.liveCount .connected .connected configuration : ℝ) else 0) / probability
  apply (le_div_iff₀ positive).mpr
  nlinarith [numeratorLower]

end
end IGSIII4.SpectralDensity
