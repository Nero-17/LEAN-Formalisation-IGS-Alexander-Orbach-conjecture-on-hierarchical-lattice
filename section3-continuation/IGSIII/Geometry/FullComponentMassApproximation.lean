import IGSIII.Geometry.FiniteMassTransport
import IGSIII.Geometry.ActualFullComponentOwnership

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped BigOperators Topology

theorem probability_boundary_weights_sum
    {Alphabet : Type*} [Fintype Alphabet] [MeasurableSpace Alphabet] [MeasurableSingletonClass Alphabet]
    (weight : List Alphabet → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (boundary : Measure (Π depth, Fin depth → Alphabet)) [IsProbabilityMeasure boundary]
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    (age : ℕ) : ∑ word : Fin age → Alphabet, weight (List.ofFn word) = 1 := by
  classical
  have partition := sum_measure_preimage_singleton (μ := boundary) (f := fun path => path age) Finset.univ
    (fun word _ => (measurable_pi_apply age) (measurableSet_singleton word))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at partition
  change (∑ word : Fin age → Alphabet, boundary {path | path age = word}) = 1 at partition
  simp_rw [atoms] at partition
  have realPartition := congrArg ENNReal.toReal partition
  rw [ENNReal.toReal_sum (fun word _ => ENNReal.ofReal_ne_top)] at realPartition
  simpa only [ENNReal.toReal_ofReal (nonnegative _), ENNReal.toReal_one] using realPartition

theorem full_component_empirical_projection_tendsto_zero
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop)
    (weight : List (Fin rule.edges × Bool) → ℝ) (nonnegative : ∀ address, 0 ≤ weight address)
    (convergence : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)))
    (level_sum : ∀ age, ∑ word : Fin age → (Fin rule.edges × Bool), weight (List.ofFn word) = 1)
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (atoms : ∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word)))
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (age : ℕ) (fallback : Fin age → (Fin rule.edges × Bool))
    (anchor : (Fin age → (Fin rule.edges × Bool)) → Space) :
    Tendsto (fun fine => levyProkhorovEDist
      ((fullComponentEmpiricalWordLaw rule marks crossing fine age fallback).map anchor)
      (boundary.map (fun path => anchor (path age)))) atTop (𝓝 0) := by
  have marginal : boundary.map (fun path => path age) =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => weight (List.ofFn word))
        (fun word => nonnegative _) (level_sum age)).toMeasure := by
    apply Measure.ext_of_singleton
    intro word
    rw [Measure.map_apply (measurable_pi_apply age) (measurableSet_singleton word), finiteWeightPMF_singleton]
    exact atoms age word
  have projection_identity : boundary.map (fun path => anchor (path age)) =
      (finiteWeightPMF (fun word : Fin age → (Fin rule.edges × Bool) => weight (List.ofFn word))
        (fun word => nonnegative _) (level_sum age)).toMeasure.map anchor := by
    rw [← marginal, Measure.map_map (measurable_of_finite anchor) (measurable_pi_apply age)]
    rfl
  rw [projection_identity]
  exact levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero
    (fun fine word => fullComponentEmpiricalWordWeight rule marks fine age fallback word)
    (fun word => weight (List.ofFn word))
    (fun fine word => fullComponentEmpiricalWordWeight_nonnegative rule marks fine age fallback word)
    (fun word => nonnegative _)
    (fun fine => fullComponentEmpiricalWordWeight_sum rule marks crossing fine age fallback)
    (level_sum age)
    (fun word => fullComponentEmpiricalWordWeight_tendsto rule marks growth weight convergence age fallback word)
    anchor (measurable_of_finite anchor)

theorem actual_component_vertex_frontier_mass_tendsto_zero
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (scale : ℝ) (scalePositive : 0 < scale)
    (growth : Tendsto (fun depth => markedComponentVertexMass rule marks depth []) atTop atTop)
    (age : ℕ) :
    Tendsto (fun fine => actualFiniteClusterMeasure rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + age)
        (actualComponentVertexFrontier rule marks crossing scale scalePositive fine age)) atTop (𝓝 0) := by
  simp_rw [actualComponentVertexFrontier_mass]
  have ratio := ratio_add_constants_tendsto (fun _ => (0 : ℝ))
    (fun fine => markedComponentVertexMass rule marks (fine + age) []) 0
    (componentFrontierVertexMass rule marks age [] + 2) 2
    (growth.comp (tendsto_add_atTop_nat age)) (by simp)
  simp only [zero_add] at ratio
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ratio

end
end IGSIII.Geometry
