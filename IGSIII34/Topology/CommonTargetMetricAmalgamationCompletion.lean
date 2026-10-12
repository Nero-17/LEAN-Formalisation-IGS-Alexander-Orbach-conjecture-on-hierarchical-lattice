import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5400000
namespace IGSIII34.Topology
noncomputable section
open Metric Set

universe u

structure CommonTargetGluingStageCompletion (Target : Type u) [MetricSpace Target] where
  Space : Type u
  metric : MetricSpace Space
  embedding : Target → Space
  isometry : Isometry embedding

attribute [local instance] CommonTargetGluingStageCompletion.metric

variable {Target : Type u} [MetricSpace Target] [Nonempty Target]
  (Extensions : ℕ → Type u) [∀ index, MetricSpace (Extensions index)]
  (targetEmbedding : ∀ index, Target → Extensions index)
  (targetIsometry : ∀ index, Isometry (targetEmbedding index))

/-- Successively glue each extension along the same isometric copy of
the target, preserving every metric already constructed. -/
def commonTargetGluingStageCompletion (index : ℕ) :
    CommonTargetGluingStageCompletion Target :=
  Nat.recOn index
    { Space := Target, metric := inferInstance, embedding := id, isometry := isometry_id }
    (fun index stage =>
      { Space := GlueSpace stage.isometry (targetIsometry index)
        metric := inferInstance
        embedding := toGlueR stage.isometry (targetIsometry index) ∘ targetEmbedding index
        isometry := (toGlueR_isometry stage.isometry (targetIsometry index)).comp (targetIsometry index) })

def commonTargetGluingStepCompletion (index : ℕ) :
    (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).Space →
      (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry (index+1)).Space :=
  toGlueL (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
    (targetIsometry index)

theorem commonTargetGluingStep_isometry_completion (index : ℕ) :
    Isometry (commonTargetGluingStepCompletion Extensions targetEmbedding targetIsometry index) :=
  toGlueL_isometry _ _

def CommonTargetMetricPreSpaceCompletion :=
  Metric.InductiveLimit (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry)

instance commonTargetMetricPreSpaceMetricCompletion : MetricSpace
    (CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (MetricSpace (Metric.InductiveLimit
    (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry)))

def CommonTargetMetricAmbientCompletion :=
  UniformSpace.Completion (CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry)

instance commonTargetMetricAmbientMetricCompletion : MetricSpace
    (CommonTargetMetricAmbientCompletion Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion
    (CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry)))

instance commonTargetMetricAmbientCompleteCompletion : CompleteSpace
    (CommonTargetMetricAmbientCompletion Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion
    (CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry)))

def commonTargetAmbientEmbeddingCompletion : Target →
    CommonTargetMetricAmbientCompletion Extensions targetEmbedding targetIsometry :=
  fun point => UniformSpace.Completion.coe' (Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) 0 point :
      CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry)

def commonExtensionAmbientEmbeddingCompletion (index : ℕ) : Extensions index →
    CommonTargetMetricAmbientCompletion Extensions targetEmbedding targetIsometry :=
  fun point => UniformSpace.Completion.coe' (Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) (index+1)
    (Metric.toGlueR
      (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index) point) :
      CommonTargetMetricPreSpaceCompletion Extensions targetEmbedding targetIsometry)

theorem commonTargetAmbientEmbedding_isometry_completion :
    Isometry (commonTargetAmbientEmbeddingCompletion Extensions targetEmbedding targetIsometry) :=
  UniformSpace.Completion.coe_isometry.comp
    (Metric.toInductiveLimit_isometry
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) 0)

theorem commonExtensionAmbientEmbedding_isometry_completion (index : ℕ) :
    Isometry (commonExtensionAmbientEmbeddingCompletion Extensions targetEmbedding targetIsometry index) :=
  UniformSpace.Completion.coe_isometry.comp
    ((Metric.toInductiveLimit_isometry
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) (index+1)).comp
      (Metric.toGlueR_isometry
        (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
        (targetIsometry index)))

theorem commonTargetGluingStage_inductive_identity_completion (index : ℕ) (point : Target) :
    Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) index
      ((commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).embedding point) =
    Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) 0 point := by
  induction index with
  | zero => rfl
  | succ index induction =>
    change Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) (index+1)
      (Metric.toGlueR
        (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
        (targetIsometry index) (targetEmbedding index point)) = _
    have commutation := congrFun (Metric.toGlue_commute
      (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index)) point
    simp only [Function.comp_apply] at commutation
    rw [← commutation]
    have inclusion := congrFun (Metric.toInductiveLimit_commute
      (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) index)
      ((commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).embedding point)
    exact inclusion.trans induction

/-- The single complete ambient space retains the exact cross-distance
from every given extension to its original target copy. In particular,
any previously proved projection-displacement bound survives gluing. -/
theorem commonExtensionAmbientEmbedding_target_distance_completion
    (index : ℕ) (point : Extensions index) (target : Target) :
    dist (commonExtensionAmbientEmbeddingCompletion Extensions targetEmbedding targetIsometry index point)
      (commonTargetAmbientEmbeddingCompletion Extensions targetEmbedding targetIsometry target) =
      dist point (targetEmbedding index target) := by
  unfold commonExtensionAmbientEmbeddingCompletion commonTargetAmbientEmbeddingCompletion
  rw [UniformSpace.Completion.coe_isometry.dist_eq,
    ← commonTargetGluingStage_inductive_identity_completion Extensions targetEmbedding targetIsometry (index+1) target]
  rw [(Metric.toInductiveLimit_isometry
    (commonTargetGluingStep_isometry_completion Extensions targetEmbedding targetIsometry) (index+1)).dist_eq]
  change dist (Metric.toGlueR
    (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
    (targetIsometry index) point)
    (Metric.toGlueR
      (commonTargetGluingStageCompletion Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index) (targetEmbedding index target)) = _
  exact (Metric.toGlueR_isometry _ _).dist_eq _ _

end
end IGSIII34.Topology
