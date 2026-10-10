import IGSIII34.ResistanceLimit.ElectricalPersistence
import IGSIII34.ResistanceLimit.ElectricalNets
import IGSIII.Geometry.ActualBirthSkeletonPersistence

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped _root_.Topology

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (pairConvergence : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  Tendsto (persistentNormalizedResistance rule configuration scale depth first last) atTop
    (𝓝 (pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (configurationIdentity : ∀ depth, configuration depth = stationaryConfiguration rule marks depth)

include configurationIdentity scalePositive pairConvergence in
theorem electricalVertex_near_birth_skeleton
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      markedElectricalRadius rule marks depth descendant state /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (age depth : ℕ) (bound : age ≤ depth) (beyond : start ≤ age + 1)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    ∃ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      dist (electricalVertex rule configuration coherent resistance positive compatible depth vertex)
        (electricalVertex rule configuration coherent resistance positive compatible age anchor) ≤ coefficient * eta ^ (age + 1) := by
  classical
  by_contra noAnchor
  have allFar : ∀ anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age),
      coefficient * eta ^ (age + 1) <
        dist (electricalVertex rule configuration coherent resistance positive compatible depth vertex)
          (electricalVertex rule configuration coherent resistance positive compatible age anchor) := by
    intro anchor
    exact lt_of_not_ge (fun close => noAnchor ⟨anchor, close⟩)
  have eventuallyFar (anchor : RetainedSkeletonVertex (rule.generation age).network (configuration age)) :
      ∀ᶠ host in atTop, coefficient * eta ^ (age + 1) <
        persistentNormalizedResistance rule configuration scale depth vertex.val
          (persistentVertexEmbedding rule age depth bound anchor.val) host := by
    have convergence := pairConvergence depth vertex.val
      (retainedPersistentVertexEmbedding rule configuration coherent age depth bound anchor).val
      (vertex.property.symm.trans (retainedPersistentVertexEmbedding rule configuration coherent age depth bound anchor).property)
    have limitIdentity :
        dist (electricalVertex rule configuration coherent resistance positive compatible depth vertex)
          (electricalVertex rule configuration coherent resistance positive compatible age anchor) =
        pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth)
          vertex.val (persistentVertexEmbedding rule age depth bound anchor.val) := by
      rw [electricalVertex_persistent rule configuration coherent resistance positive compatible age depth bound anchor,
        electricalVertex_distance]
      rfl
    simp only [retainedPersistentVertexEmbedding_val] at convergence
    rw [← limitIdentity] at convergence
    exact (tendsto_order.mp convergence).1 _ (allFar anchor)
  obtain ⟨host, hostLarge, allFarHost⟩ :=
    ((eventually_ge_atTop depth).and (Filter.eventually_all.mpr eventuallyFar)).exists
  have retainedHost := (retainedPersistentVertexEmbedding rule configuration coherent depth host hostLarge vertex).property
  have actualReachable : ((rule.generation host).network.openGraph
      (markedGenerationConfiguration rule marks host [] true)).Reachable
        (plantedVertex (rule.generation host).network true)
        (persistentVertexEmbedding rule depth host hostLarge vertex.val) := by
    simpa only [configurationIdentity host, stationaryConfiguration, retainedPersistentVertexEmbedding_val,
      plantedVertex, Bool.true_eq, if_true] using retainedHost
  obtain ⟨fineAnchor, membership, fineRetained, close⟩ :=
    finite_skeleton_is_electrical_net_of_radius_bounds rule marks scale eta coefficient start
      scalePositive etaNonnegative coefficientNonnegative radiusBounds host age [] true true
      (persistentVertexEmbedding rule depth host hostLarge vertex.val) (by simpa using beyond) actualReachable
  rw [finiteSkeletonVertices_eq_persistent_image rule age host (bound.trans hostLarge)] at membership
  obtain ⟨anchor, _, anchorIdentity⟩ := Finset.mem_map.mp membership
  have retainedAnchor : ((rule.generation age).network.openGraph (configuration age)).Reachable
      (rule.generation age).network.source anchor := by
    apply (persistentVertexEmbedding_reachable_iff rule configuration coherent age host (bound.trans hostLarge) _ _).mp
    change ((rule.generation host).network.openGraph (configuration host)).Reachable
      (persistentVertexEmbedding rule age host (bound.trans hostLarge)
        (plantedVertex (rule.generation age).network true)) _
    rw [persistentVertexEmbedding_planted, anchorIdentity]
    simpa only [configurationIdentity host, stationaryConfiguration] using fineRetained
  have far := allFarHost ⟨anchor, retainedAnchor⟩
  simp only [persistentNormalizedResistance, dif_pos hostLarge, persistentVertexEmbedding_trans] at far
  rw [anchorIdentity] at far
  have closeActual :
      pairResistance (network (rule.generation host).network (configuration host)) (fun _ => 1)
        (persistentVertexEmbedding rule depth host hostLarge vertex.val) fineAnchor /
          scale ^ (host + 1) ≤ coefficient * eta ^ (age + 1) := by
    have anchorRetainedActual : ((rule.generation host).network.openGraph (configuration host)).Reachable
        (rule.generation host).network.source fineAnchor := by
      simpa only [configurationIdentity host, stationaryConfiguration, plantedVertex, Bool.true_eq, if_true] using fineRetained
    have symmetric := pairResistance_comm (network (rule.generation host).network (configuration host))
      (fun _ => 1) (fun _ => zero_lt_one) (first := fineAnchor)
      (last := persistentVertexEmbedding rule depth host hostLarge vertex.val)
      (by simpa only [graph_eq_openGraph, retainedPersistentVertexEmbedding_val]
        using anchorRetainedActual.symm.trans retainedHost)
    rw [← symmetric]
    change pairResistance (network (rule.generation host).network (stationaryConfiguration rule marks host))
      (fun _ => 1) fineAnchor (persistentVertexEmbedding rule depth host hostLarge vertex.val) /
        scale ^ (host + 1 + ([] : List (Fin rule.edges)).length) ≤
          coefficient * eta ^ (([] : List (Fin rule.edges)).length + age + 1) at close
    have configurationTransport := congrArg (fun state : Configuration (rule.generation host).edges =>
      pairResistance (network (rule.generation host).network state) (fun _ => 1) fineAnchor
        (persistentVertexEmbedding rule depth host hostLarge vertex.val) / scale ^ (host + 1) ≤
          coefficient * eta ^ (age + 1)) (configurationIdentity host)
    apply configurationTransport.mpr
    simpa only [List.length_nil, Nat.add_zero, Nat.zero_add] using close
  exact (not_lt_of_ge closeActual) far

include configurationIdentity scalePositive pairConvergence in
theorem electricalSpace_compact_of_radius_bounds
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      markedElectricalRadius rule marks depth descendant state /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length) :
    CompactSpace (ElectricalSpace rule configuration coherent resistance positive compatible) := by
  classical
  have vanishing : Tendsto (fun age : ℕ => coefficient * eta ^ (age + 1)) atTop (𝓝 0) := by
    have powers := (tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul powers
  have bounded : TotallyBounded (⋃ depth, Set.range
      (electricalVertex rule configuration coherent resistance positive compatible depth)) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon epsilonPositive
    obtain ⟨age, ageLarge, small⟩ :=
      ((eventually_ge_atTop start).and ((tendsto_order.mp vanishing).2 epsilon epsilonPositive)).exists
    refine ⟨Set.range (electricalVertex rule configuration coherent resistance positive compatible age), Set.finite_range _, ?_⟩
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    rcases le_total age depth with bound | bound
    · obtain ⟨anchor, close⟩ := electricalVertex_near_birth_skeleton rule configuration coherent resistance positive compatible
        scale scalePositive pairConvergence marks configurationIdentity eta coefficient start etaNonnegative coefficientNonnegative
        radiusBounds age depth bound (by omega) vertex
      exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨⟨anchor, rfl⟩, close.trans_lt small⟩⟩
    · refine Set.mem_iUnion.mpr ⟨electricalVertex rule configuration coherent resistance positive compatible age
        (retainedPersistentVertexEmbedding rule configuration coherent depth age bound vertex),
        Set.mem_iUnion.mpr ⟨⟨_, rfl⟩, ?_⟩⟩
      rw [← electricalVertex_persistent rule configuration coherent resistance positive compatible depth age bound vertex]
      exact Metric.mem_ball_self epsilonPositive
  have compact := bounded.closure.isCompact_of_isClosed isClosed_closure
  rw [(electricalVertex_dense rule configuration coherent resistance positive compatible).closure_eq] at compact
  exact isCompact_univ_iff.mp compact

end
end IGSIII34.ResistanceLimit
