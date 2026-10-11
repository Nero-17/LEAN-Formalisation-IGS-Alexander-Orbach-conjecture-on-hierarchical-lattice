import IGSIII34.Topology.CompletionInverseDistance

set_option autoImplicit false
namespace IGSIII34.Topology
open UniformSpace Set
open scoped NNReal
noncomputable section

/-- The completed image is exactly the closure of the original embedded
skeleton, so a known closed physical cell can be identified on its dense set. -/
theorem completion_range_eq_closure_skeleton_image
    {Skeleton Target : Type*} [MetricSpace Skeleton] [MetricSpace Target]
    (mapping : Completion Skeleton → Target) (uniform : UniformContinuous mapping)
    (constant : ℝ≥0)
    (bound : ∀ first last : Skeleton,
      dist first last ≤ constant * dist (mapping first) (mapping last)) :
    range mapping = closure (range (fun point : Skeleton => mapping point)) := by
  have closed : IsClosed (range mapping) :=
    (completion_antilipschitz_of_skeleton_bound mapping uniform.continuous constant bound).isClosed_range uniform
  apply Subset.antisymm
  · rintro _ ⟨point, rfl⟩
    refine Completion.induction_on point (isClosed_closure.preimage uniform.continuous) ?_
    intro point
    exact subset_closure ⟨point, rfl⟩
  · apply closure_minimal _ closed
    rintro _ ⟨point, rfl⟩
    exact ⟨point, rfl⟩

end
end IGSIII34.Topology
