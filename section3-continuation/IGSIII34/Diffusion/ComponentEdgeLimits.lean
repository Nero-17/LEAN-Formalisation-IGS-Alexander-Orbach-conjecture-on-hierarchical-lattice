import IGSIII34.Diffusion.OrientedRewardComparison
import IGSIII34.Diffusion.RewardTransportConvergence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

/-- Actual edge limits are coupled to the established vertex limits at all
addresses and all masks. The same positive reward ratio applies throughout. -/
theorem marked_joint_oriented_reward_limits {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (ratio : ℝ) (limit : List (Fin rule.edges) → OrientedState →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)),
      0 < ratio ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address parent, 0 ≤ limit address parent marks ∧
          (parent = .connected → 0 < limit address parent marks) ∧
          Tendsto (fun depth => markedOrientedVertexMass rule marks depth address parent /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
            atTop (𝓝 (limit address parent marks)) ∧
          Tendsto (fun depth => markedOrientedEdgeMass rule marks depth address parent /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
            atTop (𝓝 (ratio * limit address parent marks)) := by
  obtain ⟨ratio, ratioPositive, comparisons⟩ := marked_oriented_reward_comparison classicalRule
    p positive belowOne fixedPoint
  obtain ⟨limit, _, _, limits⟩ := marked_oriented_vertex_limits classicalRule p positive belowOne fixedPoint
  refine ⟨ratio, limit, ratioPositive, ?_⟩
  filter_upwards [comparisons, limits] with marks comparisons limits
  intro address parent
  refine ⟨(limits address parent).1, (limits address parent).2.2,
    (limits address parent).2.1, ?_⟩
  have result := (comparisons address parent).add ((limits address parent).2.1.const_mul ratio)
  simp only [zero_add] at result
  convert result using 1
  ext depth
  ring

def markedComponentEdgeMass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges × Bool)) : ℝ :=
  markedOrientedEdgeMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address)

theorem shifted_normalized_reward (count : ℕ → ℝ) (growth limit : ℝ) (growthNonzero : growth ≠ 0)
    (convergence : Tendsto (fun depth => count depth / growth ^ depth) atTop (𝓝 limit)) (age : ℕ) :
    Tendsto (fun depth => count (depth + age) / growth ^ depth) atTop (𝓝 (limit * growth ^ age)) := by
  convert (convergence.comp (tendsto_add_atTop_nat age)).mul_const (growth ^ age) using 1
  ext depth
  simp only [Function.comp_apply, pow_add]
  field_simp [growthNonzero]

/-- The exact inherited-component edge proportions and the first-birth
vertex proportions converge to the *same existing Section 2 probability
cylinders*, simultaneously over every component address. -/
theorem actual_component_joint_edge_vertex_weights {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          Tendsto (fun depth => markedComponentVertexMass rule marks depth address /
            markedComponentVertexMass rule marks (depth + address.length) []) atTop (𝓝 (weight address marks)) ∧
          Tendsto (fun depth => markedComponentEdgeMass rule marks depth address /
            markedComponentEdgeMass rule marks (depth + address.length) []) atTop (𝓝 (weight address marks))) ∧
        ∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) marks = 1 := by
  obtain ⟨weight, weightProperties⟩ := actual_component_cylinder_probability_weights classicalRule
    p positive belowOne fixedPoint
  obtain ⟨ratio, limit, ratioPositive, limits⟩ := marked_joint_oriented_reward_limits classicalRule
    p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨weight, ?_⟩
  filter_upwards [weightProperties, limits] with marks properties limits
  refine ⟨properties.1, ?_, properties.2.2⟩
  intro address
  have vertexRatio := (properties.2.1 address).2.2.1
  change Tendsto (fun depth => markedComponentVertexMass rule marks depth address /
    markedComponentVertexMass rule marks (depth + address.length) []) atTop (𝓝 (weight address marks)) at vertexRatio
  refine ⟨(properties.2.1 address).1, vertexRatio, ?_⟩
  have rootPositive := (limits [] .connected).2.1 rfl
  have denominatorPositive : 0 < limit [] .connected marks *
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length :=
    mul_pos rootPositive (pow_pos radiusPositive _)
  have rootVertex := shifted_normalized_reward _ _ _ radiusPositive.ne' (limits [] .connected).2.2.1 address.length
  have rootEdge := shifted_normalized_reward _ _ _ radiusPositive.ne' (limits [] .connected).2.2.2 address.length
  have normalizedVertexRatio := normalized_reward_ratio _ _ _ _ _ radiusPositive.ne' denominatorPositive.ne'
    (limits (componentEdgeAddress address) (retainedComponentState rule marks address)).2.2.1 rootVertex
  change Tendsto (fun depth => markedComponentVertexMass rule marks depth address /
    markedComponentVertexMass rule marks (depth + address.length) []) atTop
    (𝓝 (limit (componentEdgeAddress address) (retainedComponentState rule marks address) marks /
      (limit [] .connected marks * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length)))
    at normalizedVertexRatio
  have equality := tendsto_nhds_unique vertexRatio normalizedVertexRatio
  rw [equality]
  apply reward_constant_cancels _ _ _ ratio _ _ radiusPositive.ne' ratioPositive denominatorPositive
  · exact (limits (componentEdgeAddress address) (retainedComponentState rule marks address)).2.2.2
  · convert rootEdge using 1
    · rfl
    · congr 1
      ring

end
end IGSIII34.Diffusion
