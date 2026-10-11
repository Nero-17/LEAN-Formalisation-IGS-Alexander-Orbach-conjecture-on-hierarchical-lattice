import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5400000
namespace IGSIII34.Topology
noncomputable section
open Metric Set

universe u

structure CommonTargetGluingStageCompletion20261011 (Target : Type u) [MetricSpace Target] where
  Space : Type u
  metric : MetricSpace Space
  embedding : Target → Space
  isometry : Isometry embedding

attribute [local instance] CommonTargetGluingStageCompletion20261011.metric

variable {Target : Type u} [MetricSpace Target] [Nonempty Target]
  (Extensions : ℕ → Type u) [∀ index, MetricSpace (Extensions index)]
  (targetEmbedding : ∀ index, Target → Extensions index)
  (targetIsometry : ∀ index, Isometry (targetEmbedding index))

/-- Successively glue each extension along the same isometric copy of
the target, preserving every metric already constructed. -/
def commonTargetGluingStageCompletion20261011 (index : ℕ) :
    CommonTargetGluingStageCompletion20261011 Target :=
  Nat.recOn index
    { Space := Target, metric := inferInstance, embedding := id, isometry := isometry_id }
    (fun index stage =>
      { Space := GlueSpace stage.isometry (targetIsometry index)
        metric := inferInstance
        embedding := toGlueR stage.isometry (targetIsometry index) ∘ targetEmbedding index
        isometry := (toGlueR_isometry stage.isometry (targetIsometry index)).comp (targetIsometry index) })

def commonTargetGluingStepCompletion20261011 (index : ℕ) :
    (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).Space →
      (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry (index+1)).Space :=
  toGlueL (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
    (targetIsometry index)

theorem commonTargetGluingStep_isometry_completion20261011 (index : ℕ) :
    Isometry (commonTargetGluingStepCompletion20261011 Extensions targetEmbedding targetIsometry index) :=
  toGlueL_isometry _ _

def CommonTargetMetricPreSpaceCompletion20261011 :=
  Metric.InductiveLimit (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry)

instance commonTargetMetricPreSpaceMetricCompletion20261011 : MetricSpace
    (CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (MetricSpace (Metric.InductiveLimit
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry)))

def CommonTargetMetricAmbientCompletion20261011 :=
  UniformSpace.Completion (CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry)

instance commonTargetMetricAmbientMetricCompletion20261011 : MetricSpace
    (CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion
    (CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry)))

instance commonTargetMetricAmbientCompleteCompletion20261011 : CompleteSpace
    (CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion
    (CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry)))

def commonTargetAmbientEmbeddingCompletion20261011 : Target →
    CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry :=
  fun point => UniformSpace.Completion.coe' (Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) 0 point :
      CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry)

def commonExtensionAmbientEmbeddingCompletion20261011 (index : ℕ) : Extensions index →
    CommonTargetMetricAmbientCompletion20261011 Extensions targetEmbedding targetIsometry :=
  fun point => UniformSpace.Completion.coe' (Metric.toInductiveLimit
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (index+1)
    (Metric.toGlueR
      (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index) point) :
      CommonTargetMetricPreSpaceCompletion20261011 Extensions targetEmbedding targetIsometry)

theorem commonTargetAmbientEmbedding_isometry_completion20261011 :
    Isometry (commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry) :=
  UniformSpace.Completion.coe_isometry.comp
    (Metric.toInductiveLimit_isometry
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) 0)

theorem commonExtensionAmbientEmbedding_isometry_completion20261011 (index : ℕ) :
    Isometry (commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index) :=
  UniformSpace.Completion.coe_isometry.comp
    ((Metric.toInductiveLimit_isometry
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (index+1)).comp
      (Metric.toGlueR_isometry
        (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
        (targetIsometry index)))

theorem commonTargetGluingStage_inductive_identity_completion20261011 (index : ℕ) (point : Target) :
    Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) index
      ((commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).embedding point) =
    Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) 0 point := by
  induction index with
  | zero => rfl
  | succ index induction =>
    change Metric.toInductiveLimit
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (index+1)
      (Metric.toGlueR
        (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
        (targetIsometry index) (targetEmbedding index point)) = _
    have commutation := congrFun (Metric.toGlue_commute
      (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index)) point
    simp only [Function.comp_apply] at commutation
    rw [← commutation]
    have inclusion := congrFun (Metric.toInductiveLimit_commute
      (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) index)
      ((commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).embedding point)
    exact inclusion.trans induction

/-- The single complete ambient space retains the exact cross-distance
from every given extension to its original target copy. In particular,
any previously proved projection-displacement bound survives gluing. -/
theorem commonExtensionAmbientEmbedding_target_distance_completion20261011
    (index : ℕ) (point : Extensions index) (target : Target) :
    dist (commonExtensionAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry index point)
      (commonTargetAmbientEmbeddingCompletion20261011 Extensions targetEmbedding targetIsometry target) =
      dist point (targetEmbedding index target) := by
  unfold commonExtensionAmbientEmbeddingCompletion20261011 commonTargetAmbientEmbeddingCompletion20261011
  rw [UniformSpace.Completion.coe_isometry.dist_eq,
    ← commonTargetGluingStage_inductive_identity_completion20261011 Extensions targetEmbedding targetIsometry (index+1) target]
  rw [(Metric.toInductiveLimit_isometry
    (commonTargetGluingStep_isometry_completion20261011 Extensions targetEmbedding targetIsometry) (index+1)).dist_eq]
  change dist (Metric.toGlueR
    (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
    (targetIsometry index) point)
    (Metric.toGlueR
      (commonTargetGluingStageCompletion20261011 Extensions targetEmbedding targetIsometry index).isometry
      (targetIsometry index) (targetEmbedding index target)) = _
  exact (Metric.toGlueR_isometry _ _).dist_eq _ _

end
end IGSIII34.Topology
