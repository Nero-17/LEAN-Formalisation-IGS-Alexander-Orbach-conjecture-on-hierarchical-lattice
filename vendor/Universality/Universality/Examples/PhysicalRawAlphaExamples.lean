import Universality.Percolation.PhysicalClusterNumberResponses
import Universality.Examples.DiamondRawAlpha
import Universality.Examples.CentralWheatstoneRawAlpha
import Universality.Examples.WheatstoneTwoSidedPowerBounds

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Rule Set Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

local instance : Nonempty diamondRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [diamondRule.network.card_interior_vertices]
  have := diamondRule_classical.vertices_gt_two
  omega

local instance : NeZero diamondRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt diamondRule_classical.edges_gt_one)⟩

local instance : Nonempty centralWheatstoneRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [centralWheatstoneRule.network.card_interior_vertices]
  have := centralWheatstoneRule_classical.vertices_gt_two
  omega

local instance : NeZero centralWheatstoneRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt centralWheatstoneRule_classical.edges_gt_one)⟩

local instance : Nonempty wheatstoneRule.network.InteriorVertex := by
  apply Fintype.card_pos_iff.mp
  rw [wheatstoneRule.network.card_interior_vertices]
  have := wheatstoneRule_classical.vertices_gt_two
  omega

local instance : NeZero wheatstoneRule.edges :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt wheatstoneRule_classical.edges_gt_one)⟩

theorem diamond_physical_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] diamondCriticalProbability,
        iteratedDeriv 3 (diamondRule.physicalClusterNumberDensity diamondRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (diamondRule.physicalClusterNumberDensity diamondRule_classical.edges_gt_one) p| /
        Real.log |p - diamondCriticalProbability|) (𝓝[<] diamondCriticalProbability) (𝓝 (-1))) ∧
    ((∀ᶠ p in 𝓝[>] diamondCriticalProbability,
        iteratedDeriv 3 (diamondRule.physicalClusterNumberDensity diamondRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (diamondRule.physicalClusterNumberDensity diamondRule_classical.edges_gt_one) p| /
        Real.log |p - diamondCriticalProbability|) (𝓝[>] diamondCriticalProbability) (𝓝 (-1))) := by
  obtain ⟨hp, hp'⟩ := diamond_critical_probability_bounds
  exact two_sided_raw_alpha_of_eventuallyEq _ _ _ _
    (diamondRule.physicalClusterNumberDensity_eventually_eq diamondRule_classical.edges_gt_one
      diamondRule_classical.vertices_gt_two diamondCriticalProbability hp hp')
    diamond_cluster_number_raw_alpha

theorem centralWheatstone_physical_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] (1 / 2 : ℝ), iteratedDeriv 3
        (centralWheatstoneRule.physicalClusterNumberDensity centralWheatstoneRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (centralWheatstoneRule.physicalClusterNumberDensity centralWheatstoneRule_classical.edges_gt_one) p| /
        Real.log |p - 1 / 2|) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (-2))) ∧
    ((∀ᶠ p in 𝓝[>] (1 / 2 : ℝ), iteratedDeriv 3
        (centralWheatstoneRule.physicalClusterNumberDensity centralWheatstoneRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (centralWheatstoneRule.physicalClusterNumberDensity centralWheatstoneRule_classical.edges_gt_one) p| /
        Real.log |p - 1 / 2|) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (-2))) := by
  exact two_sided_raw_alpha_of_eventuallyEq _ _ _ _
    (centralWheatstoneRule.physicalClusterNumberDensity_eventually_eq centralWheatstoneRule_classical.edges_gt_one
      centralWheatstoneRule_classical.vertices_gt_two (1/2) (by norm_num) (by norm_num))
    centralWheatstone_cluster_number_raw_alpha

theorem wheatstone_physical_cluster_number_raw_alpha :
    ((∀ᶠ p in 𝓝[<] (1 / 2 : ℝ), iteratedDeriv 3
        (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p| /
        Real.log |p - 1 / 2|) (𝓝[<] (1 / 2 : ℝ)) (𝓝 (2 - Real.log 5 / Real.log (13 / 8)))) ∧
    ((∀ᶠ p in 𝓝[>] (1 / 2 : ℝ), iteratedDeriv 3
        (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3
          (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p| /
        Real.log |p - 1 / 2|) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (2 - Real.log 5 / Real.log (13 / 8)))) := by
  exact two_sided_raw_alpha_of_eventuallyEq _ _ _ _
    (wheatstoneRule.physicalClusterNumberDensity_eventually_eq wheatstoneRule_classical.edges_gt_one
      wheatstoneRule_classical.vertices_gt_two (1/2) (by norm_num) (by norm_num))
    wheatstone_cluster_number_raw_alpha

theorem wheatstone_physical_third_response_two_sided_power_bounds :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 → p ≠ 1/2 →
      lower * |p - 1/2| ^ (Real.log 5 / Real.log (13/8) - 3) ≤
        |iteratedDeriv 3 (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p| ∧
      |iteratedDeriv 3 (wheatstoneRule.physicalClusterNumberDensity wheatstoneRule_classical.edges_gt_one) p| ≤
        upper * |p - 1/2| ^ (Real.log 5 / Real.log (13/8) - 3) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := wheatstone_third_response_two_sided_power_bounds
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro p hp hpneq
  rw [wheatstoneRule.physicalClusterNumberDensity_iteratedDeriv_eq wheatstoneRule_classical.edges_gt_one
    wheatstoneRule_classical.vertices_gt_two p hp.1 hp.2 3]
  exact hbounds p hp hpneq

end
end Universality
