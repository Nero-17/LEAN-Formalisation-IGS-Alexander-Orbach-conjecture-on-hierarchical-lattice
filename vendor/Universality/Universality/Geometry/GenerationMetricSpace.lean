import Universality.Geometry.GenerationHausdorffUpperBound

/-! A named version of the actual rescaled generation completion. Its metric,
compactness and dense finite-generation inclusions are proved, not fields
postulated as a geometric realisation. -/
namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The directed union of persistent generation vertices. The classical-rule
proof remains a type index so its actual graph metric is unambiguous. -/
def GenerationMetricSkeleton {rule : Rule} (_h : rule.Classical) : Type :=
  DirectLimit (fun depth => Fin (rule.generation depth).vertices)
    (Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
      rule.generationOldVertex)

instance generationMetricSkeletonMetricSpace {rule : Rule} (h : rule.Classical) :
    MetricSpace (GenerationMetricSkeleton h) := by
  letI (depth : ℕ) := scaledGenerationMetricSpace h depth
  exact Geometry.IsometricSequence.limitMetricSpace
    (fun depth => Fin (rule.generation depth).vertices) rule.generationOldVertex
    (fun depth => h.generationOldVertex_isometry depth)

/-- The actual complete metric limit of a classical substitution rule. -/
def GenerationMetricSpace {rule : Rule} (h : rule.Classical) : Type :=
  UniformSpace.Completion (GenerationMetricSkeleton h)

instance generationMetricSpaceMetricSpace {rule : Rule} (h : rule.Classical) :
    MetricSpace (GenerationMetricSpace h) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion (GenerationMetricSkeleton h)))

instance generationMetricSpaceCompleteSpace {rule : Rule} (h : rule.Classical) :
    CompleteSpace (GenerationMetricSpace h) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (GenerationMetricSkeleton h)))

def generationMetricVertex {rule : Rule} (h : rule.Classical) (depth : ℕ)
    (vertex : Fin (rule.generation depth).vertices) : GenerationMetricSpace h :=
  UniformSpace.Completion.coe' (α := GenerationMetricSkeleton h) ⟦⟨depth, vertex⟩⟧

instance generationMetricSpaceNonempty {rule : Rule} (h : rule.Classical) :
    Nonempty (GenerationMetricSpace h) :=
  ⟨generationMetricVertex h 0 rule.network.source⟩

theorem generationMetricVertex_distance {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (first second : Fin (rule.generation depth).vertices) :
    dist (generationMetricVertex h depth first) (generationMetricVertex h depth second) =
      scaledGenerationDistance rule depth first second := by
  letI (depth : ℕ) := scaledGenerationMetricSpace h depth
  exact (Geometry.IsometricSequence.completion_inclusion_isometry
    (fun depth => Fin (rule.generation depth).vertices)
    rule.generationOldVertex (fun depth => h.generationOldVertex_isometry depth) depth).dist_eq first second

theorem generationMetricVertex_old {rule : Rule} (h : rule.Classical)
    (depth : ℕ) (vertex : Fin (rule.generation depth).vertices) :
    generationMetricVertex h depth vertex =
      generationMetricVertex h (depth + 1) (rule.generationOldVertex depth vertex) := by
  apply congrArg (fun point : GenerationMetricSkeleton h =>
    (point : UniformSpace.Completion (GenerationMetricSkeleton h)))
  have hcoarse := DirectLimit.mk_apply
    (f := Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
      rule.generationOldVertex) depth (depth + 1) vertex (Nat.le_succ depth)
  simpa only [Geometry.IsometricSequence.transition, Function.Embedding.coeFn_mk,
    Nat.leRecOn_succ'] using hcoarse.symm

theorem generationMetricVertex_dense {rule : Rule} (h : rule.Classical) :
    Dense (⋃ depth, Set.range (generationMetricVertex h depth)) := by
  apply (UniformSpace.Completion.denseRange_coe (α := GenerationMetricSkeleton h)).mono
  rintro _ ⟨point, rfl⟩
  obtain ⟨depth, vertex, rfl⟩ := DirectLimit.exists_eq_mk
    (Geometry.IsometricSequence.transition (fun depth => Fin (rule.generation depth).vertices)
      rule.generationOldVertex) point
  exact Set.mem_iUnion.mpr ⟨depth, ⟨vertex, rfl⟩⟩

instance generationMetricSpaceCompactSpace {rule : Rule} (h : rule.Classical) :
    CompactSpace (GenerationMetricSpace h) := by
  let radius := Finset.univ.sup (fun vertex =>
    rule.network.fullGraph.dist rule.network.source vertex)
  have hradius (vertex) : rule.network.fullGraph.dist rule.network.source vertex ≤ radius :=
    Finset.le_sup (Finset.mem_univ vertex)
  let ratio : ℝ := (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)⁻¹
  let constant : ℝ := (radius : ℝ) /
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ 2
  have hratio : 0 ≤ ratio := inv_nonneg.mpr h.scale_real_pos.le
  have hratioOne : ratio < 1 :=
    (inv_lt_one₀ h.scale_real_pos).mpr (by exact_mod_cast h.scale)
  have hconstant : 0 ≤ constant := by dsimp [constant]; positivity
  have hnested : Monotone (fun depth => Set.range (generationMetricVertex h depth)) := by
    apply monotone_nat_of_le_succ
    intro depth point hpoint
    obtain ⟨vertex, rfl⟩ := hpoint
    exact ⟨rule.generationOldVertex depth vertex, (generationMetricVertex_old h depth vertex).symm⟩
  have hstep (depth) (point : Fin (rule.generation (depth + 1)).vertices) :
      ∃ previous : Fin (rule.generation depth).vertices,
        dist (generationMetricVertex h (depth + 1) point) (generationMetricVertex h depth previous) ≤
          constant * ratio ^ depth := by
    obtain ⟨previous, hprevious⟩ := h.generation_vertex_near_old radius hradius depth point
    refine ⟨previous, ?_⟩
    calc
      dist (generationMetricVertex h (depth + 1) point) (generationMetricVertex h depth previous) =
          scaledGenerationDistance rule (depth + 1) (rule.generationOldVertex depth previous) point := by
            rw [generationMetricVertex_old h depth previous, dist_comm, generationMetricVertex_distance]
      _ ≤ (radius : ℝ) /
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 2) := hprevious
      _ = constant * ratio ^ depth := by
        simp [constant, ratio, pow_add, div_eq_mul_inv, mul_comm, mul_left_comm]
  have hbounded := Geometry.totallyBounded_union_of_geometric_steps
    (fun depth => Fin (rule.generation depth).vertices) (generationMetricVertex h) hnested
    constant ratio hconstant hratio hratioOne hstep
  have hcompact := hbounded.closure.isCompact_of_isClosed isClosed_closure
  rw [(generationMetricVertex_dense h).closure_eq] at hcompact
  exact isCompact_univ_iff.mp hcompact

theorem generationMetricSpace_dimH_le {rule : Rule} (h : rule.Classical) :
    dimH (Set.univ : Set (GenerationMetricSpace h)) ≤ ENNReal.ofReal
      (Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) :=
  h.dimH_le_of_generation_realisation (generationMetricVertex h)
    (generationMetricVertex_distance h) (generationMetricVertex_old h) (generationMetricVertex_dense h)

end
end Universality.Rule

