import IGSIII.Geometry.ActualComponentOwnershipMetric
import IGSIII.Geometry.FullComponentMassApproximation
import IGSIII.Geometry.MarkedGromovHausdorffProkhorov
import IGSIII.Geometry.ActualClusterGromovHausdorff
import IGSIII.Chemical.SmallBall.MarkedSkeletonDistortion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open MeasureTheory Filter
open scoped BigOperators Topology

theorem actualFiniteCluster_markedGHP_of_component_radius_bounds
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale)
    (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
    (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < limitLength depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened fine, start ≤ address.length →
      (markedTerminalComponentRadius rule marks fine address opened : ℝ) / scale ^ (fine + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (massGrowth : Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ) (weightNonnegative : ∀ address, 0 ≤ weight address)
    (countConvergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent scale scalePositive limitLength nonnegative positive childConvergence)
    (projectionConvergence : Tendsto (fun age => levyProkhorovEDist
      (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent scale scalePositive
        limitLength nonnegative positive childConvergence age (path (age + 1))))
      (boundary.map realization)) atTop (𝓝 0)) :
    MarkedGHPConverges
      (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth)
      (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive)
      (boundary.map realization)
      (actualFiniteClusterTerminal rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive)
      (actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
        coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive
        limitLength nonnegative positive childConvergence) := by
  classical
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classicalRule.connected _)
  let fallback : ∀ age, Fin (age + 1) → (Fin rule.edges × Bool) := fun _ _ => (edge, true)
  letI : ∀ age, Nonempty (RetainedSkeletonVertex (rule.generation age).network
      (markedGenerationConfiguration rule marks age [] true)) := fun age =>
    ⟨⟨(rule.generation age).network.source, SimpleGraph.Reachable.refl _⟩⟩
  have levelSum := probability_boundary_weights_sum weight weightNonnegative boundary atoms
  have meshConvergence : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1))
  apply markedGHPConverges_of_finite_anchor_projections
    (markIndex := fun age => retainedTerminalVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) age)
    (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth)
    (fun age => RetainedSkeletonVertex (rule.generation age).network (markedGenerationConfiguration rule marks age [] true))
    (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive)
    (boundary.map realization)
    (actualFiniteClusterTerminal rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive)
    (actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive
      limitLength nonnegative positive childConvergence)
    (fun age fine => retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive age (fine + (age + 1)) (by omega))
    (actualChemicalVertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive limitLength nonnegative positive childConvergence)
    (fun age fine point => actualComponentRetainedAnchor rule marks crossing age
      (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) (fallback age) point))
    (fun _ _ => measurable_of_finite _)
    (fun age fine => (actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1) : Set _))
    (fun age => boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent scale scalePositive
      limitLength nonnegative positive childConvergence age (path (age + 1))))
    (fun age => coefficient * eta ^ (age + 1)) (fun age => mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))
    meshConvergence start
  · intro age beyond
    exact Filter.Eventually.of_forall (fun fine => actualFiniteCluster_near_birth_skeleton rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive marks (fun _ => rfl)
      eta coefficient start etaNonnegative coefficientNonnegative radiusBound age (fine + (age + 1)) (by omega) (by omega))
  · intro age beyond
    exact actualChemicalSpace_near_birth_skeleton rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive limitLength nonnegative positive
      childConvergence marks (fun _ => rfl) eta coefficient start etaNonnegative coefficientNonnegative radiusBound age (by omega)
  · intro age bridge bridgePositive
    have distortion := (tendsto_add_atTop_nat (age + 1)).eventually
      (actualFiniteCluster_marked_skeleton_distortion rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
        scale scalePositive limitLength nonnegative positive childConvergence age (show 0 < 2 * bridge by positivity))
    filter_upwards [distortion] with fine distortion
    obtain ⟨bound, comparison, _⟩ := distortion
    exact fun left right => (comparison left right).le
  · intro age beyond
    exact Filter.Eventually.of_forall (fun fine => Filter.Eventually.of_forall (fun point nonfrontier =>
      actualComponentVertexOwnership_mesh_bound rule marks crossing coherent scale scalePositive eta coefficient start radiusBound
        fine age (by omega) (fallback age) point nonfrontier))
  · intro age
    exact actual_component_vertex_frontier_mass_tendsto_zero rule marks crossing scale scalePositive massGrowth (age + 1)
  · intro age
    have convergence := full_component_empirical_projection_tendsto_zero rule marks crossing massGrowth weight weightNonnegative
      countConvergence levelSum boundary atoms (age + 1) (fallback age)
      (actualComponentWordPoint rule classicalRule marks crossing coherent scale scalePositive limitLength nonnegative positive childConvergence age)
    convert convergence using 1
    funext fine
    congr 1
    rw [← actualComponentVertexOwnership_law rule marks crossing scale scalePositive fine (age + 1) (fallback age),
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    congr 1
    funext point
    exact (actualComponentWordPoint_eq_retained_anchor rule classicalRule marks crossing coherent scale scalePositive
      limitLength nonnegative positive childConvergence age _).symm
  · exact projectionConvergence
  · intro age
    exact Filter.Eventually.of_forall (fun fine => retainedFiniteVertexEmbedding_terminal rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive age (fine + (age + 1)) (by omega))
  · intro age side
    exact (actualChemicalTerminal_eq_vertex rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) scale scalePositive
      limitLength nonnegative positive childConvergence age side).symm

end
end IGSIII.Geometry
