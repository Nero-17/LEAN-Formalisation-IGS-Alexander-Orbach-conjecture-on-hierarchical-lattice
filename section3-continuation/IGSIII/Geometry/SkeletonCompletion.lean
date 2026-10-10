import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Compact completion from finite skeleton nets

This is the deterministic compactness argument needed for `thm:full-ghp`.
The hypotheses are finite nets and a mesh tending to zero, rather than an
assumed compact realization. The actual chemical skeleton and its random mesh
must still be supplied by the other parts of the construction.
-/

set_option autoImplicit false

namespace IGSIII.Geometry

open Set Filter Metric
open scoped Topology

variable {Skeleton : Type*} [MetricSpace Skeleton]

theorem totallyBounded_of_finite_nets
    (nets : ℕ → Finset Skeleton) (mesh : ℕ → ℝ)
    (vanishing : Tendsto mesh atTop (𝓝 0))
    (approximation : ∀ depth point, ∃ anchor ∈ nets depth,
      dist point anchor ≤ mesh depth) :
    TotallyBounded (Set.univ : Set Skeleton) := by
  apply Metric.totallyBounded_iff.mpr
  intro epsilon positive
  obtain ⟨depth, small⟩ := eventually_atTop.mp ((tendsto_order.mp vanishing).2 epsilon positive)
  refine ⟨(nets depth : Set Skeleton), (nets depth).finite_toSet, ?_⟩
  intro point _
  obtain ⟨anchor, membership, close⟩ := approximation depth point
  exact Set.mem_iUnion.mpr ⟨anchor, Set.mem_iUnion.mpr ⟨membership,
    close.trans_lt (small depth le_rfl)⟩⟩

theorem compact_completion_of_finite_nets
    (nets : ℕ → Finset Skeleton) (mesh : ℕ → ℝ)
    (vanishing : Tendsto mesh atTop (𝓝 0))
    (approximation : ∀ depth point, ∃ anchor ∈ nets depth,
      dist point anchor ≤ mesh depth) :
    CompactSpace (UniformSpace.Completion Skeleton) := by
  have bounded := totallyBounded_of_finite_nets nets mesh vanishing approximation
  have imageBounded : TotallyBounded
      (Set.range (fun point : Skeleton => (point : UniformSpace.Completion Skeleton))) := by
    simpa using bounded.image (UniformSpace.Completion.uniformContinuous_coe Skeleton)
  have closureRange : closure
      (Set.range (fun point : Skeleton => (point : UniformSpace.Completion Skeleton))) = Set.univ :=
    UniformSpace.Completion.denseRange_coe.closure_range
  refine ⟨?_⟩
  rw [← closureRange]
  exact imageBounded.closure.isCompact_of_isClosed isClosed_closure

/-- Passing to the completion preserves every finite skeleton distance. -/
theorem completion_distance_eq (first second : Skeleton) :
    dist (first : UniformSpace.Completion Skeleton) (second : UniformSpace.Completion Skeleton) =
      dist first second :=
  UniformSpace.Completion.coe_isometry.dist_eq first second

end IGSIII.Geometry
