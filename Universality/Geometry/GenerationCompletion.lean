import Universality.Geometry.ScaledGenerationMetric
import Universality.Geometry.IsometricSequence

/-! The actual classical generation graph metrics have a compatible complete
metric realisation with dense persistent vertices. This theorem constructs the
space; it does not assume a geometric realisation or its dimension. -/

namespace Universality.Rule
noncomputable section

/-- A complete ambient space is built from the rescaled graph metrics. The
inclusions preserve their exact distances, respect old vertices, and have
dense union. Compactness and Hausdorff dimension are separate conclusions. -/
theorem Classical.exists_complete_generation_metric {rule : Rule} (h : rule.Classical) :
    ∃ (Ambient : Type) (metric : MetricSpace Ambient),
      letI := metric
      CompleteSpace Ambient ∧
      ∃ inclusion : (depth : ℕ) → Fin (rule.generation depth).vertices → Ambient,
        (∀ depth first second,
          dist (inclusion depth first) (inclusion depth second) =
            scaledGenerationDistance rule depth first second) ∧
        (∀ depth vertex, inclusion depth vertex =
          inclusion (depth + 1) (rule.generationOldVertex depth vertex)) ∧
        Dense (⋃ depth, Set.range (inclusion depth)) := by
  let Node := fun depth => Fin (rule.generation depth).vertices
  letI (depth : ℕ) : MetricSpace (Node depth) := scaledGenerationMetricSpace h depth
  let transition := Geometry.IsometricSequence.transition Node rule.generationOldVertex
  letI := Geometry.IsometricSequence.limitMetricSpace Node rule.generationOldVertex
    (fun depth => h.generationOldVertex_isometry depth)
  let Skeleton := DirectLimit Node transition
  let inclusion (depth : ℕ) (point : Node depth) : UniformSpace.Completion Skeleton :=
    ((⟦⟨depth, point⟩⟧ : Skeleton) : UniformSpace.Completion Skeleton)
  refine ⟨UniformSpace.Completion Skeleton, inferInstance, inferInstance, inclusion, ?_, ?_, ?_⟩
  · intro depth first second
    exact (Geometry.IsometricSequence.completion_inclusion_isometry Node
      rule.generationOldVertex (fun depth => h.generationOldVertex_isometry depth) depth).dist_eq
        first second
  · intro depth point
    apply congrArg (fun vertex : Skeleton => (vertex : UniformSpace.Completion Skeleton))
    have hcoarse := DirectLimit.mk_apply (f := transition) depth (depth + 1) point (Nat.le_succ depth)
    simpa only [transition, Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk, Nat.leRecOn_succ'] using hcoarse.symm
  · apply (UniformSpace.Completion.denseRange_coe (α := Skeleton)).mono
    rintro _ ⟨point, rfl⟩
    obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk transition point
    exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

end
end Universality.Rule

