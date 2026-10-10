import IGSIII.Geometry.FiniteMassTransport
import IGSIII.Mass.ComponentEmpiricalLaw

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped BigOperators Topology

/-- At each fixed actual cylinder level, the projected finite counting law
converges to the corresponding marginal of the same boundary law. -/
theorem component_empirical_projection_tendsto_zero
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (nonnegative : ∀ address, 0 ≤ weight address) (root_one : weight [] = 1)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (level_sum : ∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) = 1)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (anchor : (Fin age → (Fin rule.edges × Bool)) → Space) :
    Tendsto (fun fine => levyProkhorovEDist
      ((componentEmpiricalWordLaw rule marks crossing fine age fallback).map anchor)
      (boundary.map (fun path => anchor (path age)))) atTop (𝓝 0) := by
  have marginal : boundary.map (fun path => path age) =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => weight (List.ofFn word))
        (fun word => nonnegative _) (level_sum age)).toMeasure := by
    apply Measure.ext_of_singleton
    intro word
    rw [Measure.map_apply (measurable_pi_apply age) (measurableSet_singleton word),
      finiteWeightPMF_singleton]
    exact atoms age word
  have projection_identity : boundary.map (fun path => anchor (path age)) =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => weight (List.ofFn word))
        (fun word => nonnegative _) (level_sum age)).toMeasure.map anchor := by
    rw [← marginal, Measure.map_map (measurable_of_finite anchor) (measurable_pi_apply age)]
    rfl
  rw [projection_identity]
  exact levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero
    (fun fine word => componentEmpiricalWordWeight rule marks fine age fallback word)
    (fun word => weight (List.ofFn word))
    (fun fine word => componentEmpiricalWordWeight_nonnegative rule marks fine age fallback word)
    (fun word => nonnegative _)
    (fun fine => componentEmpiricalWordWeight_sum rule marks crossing fine age fallback)
    (level_sum age)
    (fun word => componentEmpiricalWordWeight_tendsto rule marks crossing weight root_one convergence level_sum age fallback word)
    anchor (measurable_of_finite anchor)

end
end IGSIII.Geometry
