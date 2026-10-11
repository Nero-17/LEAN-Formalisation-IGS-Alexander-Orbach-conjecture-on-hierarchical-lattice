import IGSIII34.Topology.CommonTargetMetricAmalgamationCompletion20261011
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5800000
namespace IGSIII34.Topology
noncomputable section
open Metric Set Filter
open scoped _root_.Topology
universe u
attribute [local instance] CommonTargetGluingStageCompletion20261011.metric

variable {Target : Type u} [MetricSpace Target] [Nonempty Target]
  (Extensions : ℕ → Type u) [∀ index, MetricSpace (Extensions index)]
  (targetEmbedding : ∀ index, Target → Extensions index)
  (targetIsometry : ∀ index, Isometry (targetEmbedding index))

def commonTargetPreEmbeddingCompletion20261011 : Target →
    CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry :=
  Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) 0

def commonExtensionPreEmbeddingCompletion20261011 (index : ℕ) : Extensions index →
    CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry :=
  Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (index+1) ∘
    Metric.toGlueR
      (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index)

theorem commonTargetGluingStage_pre_cases_completion20261011 (level : ℕ)
    (point : (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry level).Space) :
    (∃ target, Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) level point =
      commonTargetPreEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target) ∨
    (∃ index extension, Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) level point =
      commonExtensionPreEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index extension) := by
  induction level with
  | zero => exact Or.inl ⟨point, rfl⟩
  | succ level induction =>
    refine Quotient.inductionOn point ?_
    intro representative
    rcases representative with previous | extension
    · change (∃ target, Metric.toInductiveLimit
        (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (level+1)
        (Metric.toGlueL
          (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry level).isometry
          (targetIsometry level) previous) = _) ∨ _
      have compatibility := congrFun (Metric.toInductiveLimit_commute
        (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) level) previous
      simp only [Function.comp_apply] at compatibility
      have compatibility' : Metric.toInductiveLimit
          (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (level+1)
          (Metric.toGlueL
            (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry level).isometry
            (targetIsometry level) previous) =
          Metric.toInductiveLimit
            (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) level previous := by
        convert compatibility using 1 <;> rfl
      rcases induction previous with ⟨target, equality⟩ | ⟨index, extension, equality⟩
      · exact Or.inl ⟨target, compatibility'.trans equality⟩
      · exact Or.inr ⟨index, extension, compatibility'.trans equality⟩
    · exact Or.inr ⟨level, extension, rfl⟩

/-- Every point of the inductive metric union comes from the target or
one of the given extensions; the gluing introduces no additional points. -/
theorem commonTargetMetricPreSpace_cases_completion20261011
    (point : CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry) :
    (∃ target, point = commonTargetPreEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target) ∨
    (∃ index extension, point = commonExtensionPreEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index extension) := by
  refine Quotient.inductionOn point ?_
  rintro ⟨level, representative⟩
  exact commonTargetGluingStage_pre_cases_completion20261011 Extensions targetEmbedding targetIsometry level representative

/-- If compact extensions approach their shared compact target, their
single complete metric amalgam is compact as well. Thus it is a complete
separable common realization, with all original embeddings isometric. -/
theorem commonTargetMetricAmbient_compact_completion20261011
    [CompactSpace Target] [∀ index, CompactSpace (Extensions index)]
    (radii : ℕ → ℝ) (radiiVanish : Tendsto radii atTop (𝓝 0))
    (extensionClose : ∀ (index : ℕ) (point : Extensions index),
      ∃ target, dist point (targetEmbedding index target) ≤ radii index) :
    CompactSpace (CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry) := by
  have bounded : TotallyBounded (Set.range (UniformSpace.Completion.coe' :
      CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry →
      CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry)) := by
    apply Metric.totallyBounded_iff.mpr
    intro tolerance positive
    obtain ⟨cutoff, tailSmall⟩ := eventually_atTop.mp
      (radiiVanish.eventually (gt_mem_nhds (by positivity : (0:ℝ) < tolerance/2)))
    let finitePart : Set (CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry) :=
      Set.range (commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry) ∪
      ⋃ index : Fin cutoff, Set.range (commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index.val)
    have prefixCompact : IsCompact finitePart :=
      (isCompact_range (commonTargetAmbientEmbedding_isometry_completion20261011 Extensions targetEmbedding targetIsometry).continuous).union
        (isCompact_iUnion (fun index : Fin cutoff =>
          isCompact_range (commonExtensionAmbientEmbedding_isometry_completion20261011 Extensions targetEmbedding targetIsometry index.val).continuous))
    obtain ⟨centers, finiteCenters, cover⟩ := Metric.totallyBounded_iff.mp prefixCompact.totallyBounded
      (tolerance/2) (by positivity)
    have promote (point) (membership : point ∈ finitePart) : point ∈ ⋃ center ∈ centers, Metric.ball center tolerance := by
      obtain ⟨center, member⟩ := Set.mem_iUnion.mp (cover membership)
      obtain ⟨belongs, close⟩ := Set.mem_iUnion.mp member
      exact Set.mem_iUnion.mpr ⟨center, Set.mem_iUnion.mpr ⟨belongs,
        (Metric.mem_ball.mp close).trans (half_lt_self positive)⟩⟩
    refine ⟨centers, finiteCenters, ?_⟩
    rintro _ ⟨point, rfl⟩
    rcases commonTargetMetricPreSpace_cases_completion20261011 Extensions targetEmbedding targetIsometry point with
      ⟨target, equality⟩ | ⟨index, extension, equality⟩
    · rw [equality]
      have membership : commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target ∈ finitePart :=
        Or.inl ⟨target, rfl⟩
      exact promote _ membership
    · rw [equality]
      by_cases early : index < cutoff
      · have membership : commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index extension ∈ finitePart :=
          Or.inr (Set.mem_iUnion.mpr ⟨⟨index, early⟩, ⟨extension, rfl⟩⟩)
        exact promote _ membership
      · obtain ⟨target, closeTarget⟩ := extensionClose index extension
        have membership : commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target ∈ finitePart :=
          Or.inl ⟨target, rfl⟩
        obtain ⟨center, belongs⟩ := Set.mem_iUnion.mp (cover membership)
        obtain ⟨centerMembership, closeCenter⟩ := Set.mem_iUnion.mp belongs
        refine Set.mem_iUnion.mpr ⟨center, Set.mem_iUnion.mpr ⟨centerMembership, ?_⟩⟩
        have close : dist
            (commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index extension)
            (commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target) < tolerance/2 := by
          rw [commonExtensionAmbientEmbedding_target_distance_completion20261011]
          exact closeTarget.trans_lt (tailSmall index (by omega))
        exact (dist_triangle _ _ _).trans_lt (add_lt_add close closeCenter) |>.trans_eq (by ring)
  have compact := bounded.closure.isCompact_of_isClosed isClosed_closure
  rw [UniformSpace.Completion.denseRange_coe.closure_range] at compact
  exact isCompact_univ_iff.mp compact

end
end IGSIII34.Topology
