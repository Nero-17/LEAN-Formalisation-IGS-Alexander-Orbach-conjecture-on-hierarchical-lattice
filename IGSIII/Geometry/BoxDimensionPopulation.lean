import IGSIII.Geometry.BoxDimensionCovering
import IGSIII.Mass.CylinderMassLimits
import Universality.Percolation.InternalClusterMass

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Matrix MeasureTheory Filter
open scoped Topology BigOperators

/-- A connected actual retained skeleton consists of its internal retained
vertices and its two distinct planting vertices. -/
theorem retainedSkeletonVertex_card_connected {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crossing : network.crosses configuration = true) :
    Nat.card (RetainedSkeletonVertex network configuration) =
      network.internalStateMass .connected configuration + 2 := by
  classical
  letI := Fintype.ofFinite (RetainedSkeletonVertex network configuration)
  have count := network.sum_selectedActive_both configuration
  have active : ∀ point, network.selectedActive true true configuration point =
      (network.openGraph configuration).reachableDecide network.source point := by
    intro point
    rw [network.selectedActive_connected configuration crossing]
    simp only [selectedActive, Bool.true_and, Bool.false_and, Bool.or_false]
  simp_rw [active] at count
  rw [RetainedSkeletonVertex, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simpa only [SimpleGraph.reachableDecide_eq_true, internalStateMass,
    OrientedState.sourceSelected, OrientedState.targetSelected] using count

/-- Actual retained birth-skeleton cardinalities have the mass Perron
exponent on the same innovation sample, at every address. -/
theorem actual_retained_skeleton_population_bound {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive below_one fixed_point,
      ∀ address, ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ depth,
        (Nat.card (RetainedSkeletonVertex (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address true)) : ℝ) ≤
          coefficient * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth := by
  obtain ⟨limit, _, _, convergence⟩ := marked_oriented_vertex_limits classicalRule p positive below_one fixed_point
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  filter_upwards [convergence, independentInnovationLaw_crosses rule p positive below_one fixed_point] with
    marks convergence crossing
  intro address
  obtain ⟨bound, bounded⟩ := (convergence address .connected).2.1.bddAbove_range
  refine ⟨max 1 bound + 2, by positivity, ?_⟩
  intro depth
  have internal_bound : markedOrientedVertexMass rule marks depth address .connected ≤
      max 1 bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth := by
    apply (div_le_iff₀ (pow_pos (zero_lt_one.trans radius_gt_one) _)).mp
    exact (bounded (Set.mem_range_self depth)).trans (le_max_right _ _)
  rw [retainedSkeletonVertex_card_connected _ _
    (markedGenerationConfiguration_crosses rule marks crossing depth address true), Nat.cast_add, Nat.cast_ofNat]
  change markedOrientedVertexMass rule marks depth address .connected + 2 ≤ _
  have power_large := one_le_pow₀ radius_gt_one.le (n := depth)
  nlinarith

end
end IGSIII.Geometry
