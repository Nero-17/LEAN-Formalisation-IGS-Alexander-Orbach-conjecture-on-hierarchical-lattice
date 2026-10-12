import IGSIII34.Diffusion.OriginalJointCompactCoupling
import IGSIII34.Diffusion.JointMeasuredMarkedStateMetricBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open TopologicalSpace MeasureTheory

theorem OriginalJointCompactCoupling.cost_triangle_of_placements
    {first middle last : OriginalJointCompactRepresentative}
    (left : OriginalJointCompactCoupling first middle)
    (right : OriginalJointCompactCoupling middle last)
    (combined : OriginalJointCompactCoupling first last)
    (leftMapping : left.ambient → combined.ambient) (leftIsometry : Isometry leftMapping)
    (rightMapping : right.ambient → combined.ambient) (rightIsometry : Isometry rightMapping)
    (firstIdentity : combined.firstPlacement = leftMapping ∘ left.firstPlacement)
    (lastIdentity : combined.lastPlacement = rightMapping ∘ right.lastPlacement)
    (middleIdentity : leftMapping ∘ left.lastPlacement = rightMapping ∘ right.firstPlacement) :
    combined.cost ≤ left.cost + right.cost := by
  let firstState := jointMeasuredMarkedStateMap left.firstPlacement left.firstIsometry.continuous
    (originalJointRepresentativeState first)
  let middleLeftState := jointMeasuredMarkedStateMap left.lastPlacement left.lastIsometry.continuous
    (originalJointRepresentativeState middle)
  let middleRightState := jointMeasuredMarkedStateMap right.firstPlacement right.firstIsometry.continuous
    (originalJointRepresentativeState middle)
  let lastState := jointMeasuredMarkedStateMap right.lastPlacement right.lastIsometry.continuous
    (originalJointRepresentativeState last)
  have middleStateIdentity : jointMeasuredMarkedStateMap leftMapping leftIsometry.continuous middleLeftState =
      jointMeasuredMarkedStateMap rightMapping rightIsometry.continuous middleRightState := by
    dsimp only [middleLeftState, middleRightState]
    rw [jointMeasuredMarkedStateMap_comp, jointMeasuredMarkedStateMap_comp]
    congr 1
  have stateBound := jointMeasuredMarkedStateCost_triangle
    (jointMeasuredMarkedStateMap leftMapping leftIsometry.continuous firstState)
    (jointMeasuredMarkedStateMap leftMapping leftIsometry.continuous middleLeftState)
    (jointMeasuredMarkedStateMap rightMapping rightIsometry.continuous lastState)
  have stateLastBound := jointMeasuredMarkedStateCost_isometric_map_le
    rightMapping rightIsometry middleRightState lastState
  rw [← middleStateIdentity] at stateLastBound
  have stateFirstBound := jointMeasuredMarkedStateCost_isometric_map_le
    leftMapping leftIsometry firstState middleLeftState
  have pathMiddleIdentity :
      skorokhodCadlagContinuousCarrierMapCompletion leftMapping leftIsometry.continuous
        (skorokhodCadlagContinuousCarrierMapCompletion left.lastPlacement left.lastIsometry.continuous middle.path) =
      skorokhodCadlagContinuousCarrierMapCompletion rightMapping rightIsometry.continuous
        (skorokhodCadlagContinuousCarrierMapCompletion right.firstPlacement right.firstIsometry.continuous middle.path) := by
    rw [skorokhodCadlagCarrierMap_comp, skorokhodCadlagCarrierMap_comp]
    congr 1
  have pathBound := dist_triangle
    (skorokhodCadlagContinuousCarrierMapCompletion leftMapping leftIsometry.continuous
      (skorokhodCadlagContinuousCarrierMapCompletion left.firstPlacement left.firstIsometry.continuous first.path))
    (skorokhodCadlagContinuousCarrierMapCompletion leftMapping leftIsometry.continuous
      (skorokhodCadlagContinuousCarrierMapCompletion left.lastPlacement left.lastIsometry.continuous middle.path))
    (skorokhodCadlagContinuousCarrierMapCompletion rightMapping rightIsometry.continuous
      (skorokhodCadlagContinuousCarrierMapCompletion right.lastPlacement right.lastIsometry.continuous last.path))
  rw [(skorokhodCadlagCarrierMap_isometry leftMapping leftIsometry).dist_eq,
    pathMiddleIdentity, (skorokhodCadlagCarrierMap_isometry rightMapping rightIsometry).dist_eq] at pathBound
  unfold cost
  simp only [firstIdentity, lastIdentity]
  rw [← jointMeasuredMarkedStateMap_comp left.firstPlacement left.firstIsometry.continuous
      leftMapping leftIsometry.continuous,
    ← jointMeasuredMarkedStateMap_comp right.lastPlacement right.lastIsometry.continuous
      rightMapping rightIsometry.continuous,
    ← skorokhodCadlagCarrierMap_comp left.firstPlacement left.firstIsometry.continuous
      leftMapping leftIsometry.continuous,
    ← skorokhodCadlagCarrierMap_comp right.lastPlacement right.lastIsometry.continuous
      rightMapping rightIsometry.continuous]
  have summed := add_le_add (stateBound.trans (add_le_add stateFirstBound stateLastBound)) pathBound
  dsimp only [firstState, middleLeftState, middleRightState, lastState] at summed
  convert summed using 1 <;> first | rfl | ring

/-- The two given common ambients are glued along the entire middle
carrier, so both placed versions of every middle point agree exactly. -/
def OriginalJointCompactCoupling.glue
    {first middle last : OriginalJointCompactRepresentative}
    (left : OriginalJointCompactCoupling first middle)
    (right : OriginalJointCompactCoupling middle last) :
    OriginalJointCompactCoupling first last := by
  letI : Nonempty (Metric.GlueSpace left.lastIsometry right.firstIsometry) :=
    ⟨Metric.toGlueL left.lastIsometry right.firstIsometry (Classical.arbitrary left.ambient)⟩
  let embedding := (kuratowskiEmbedding.isometry
    (Metric.GlueSpace left.lastIsometry right.firstIsometry)).isometryEquivOnRange
  exact {
    ambient := NonemptyCompacts.kuratowskiEmbedding
      (Metric.GlueSpace left.lastIsometry right.firstIsometry)
    firstPlacement := embedding ∘ Metric.toGlueL left.lastIsometry right.firstIsometry ∘ left.firstPlacement
    firstIsometry := embedding.isometry.comp
      ((Metric.toGlueL_isometry left.lastIsometry right.firstIsometry).comp left.firstIsometry)
    lastPlacement := embedding ∘ Metric.toGlueR left.lastIsometry right.firstIsometry ∘ right.lastPlacement
    lastIsometry := embedding.isometry.comp
      ((Metric.toGlueR_isometry left.lastIsometry right.firstIsometry).comp right.lastIsometry) }

theorem OriginalJointCompactCoupling.glue_cost_le
    {first middle last : OriginalJointCompactRepresentative}
    (left : OriginalJointCompactCoupling first middle)
    (right : OriginalJointCompactCoupling middle last) :
    (left.glue right).cost ≤ left.cost + right.cost := by
  letI : Nonempty (Metric.GlueSpace left.lastIsometry right.firstIsometry) :=
    ⟨Metric.toGlueL left.lastIsometry right.firstIsometry (Classical.arbitrary left.ambient)⟩
  let embedding := (kuratowskiEmbedding.isometry
    (Metric.GlueSpace left.lastIsometry right.firstIsometry)).isometryEquivOnRange
  apply cost_triangle_of_placements left right (left.glue right)
    (embedding ∘ Metric.toGlueL left.lastIsometry right.firstIsometry)
    (embedding.isometry.comp (Metric.toGlueL_isometry left.lastIsometry right.firstIsometry))
    (embedding ∘ Metric.toGlueR left.lastIsometry right.firstIsometry)
    (embedding.isometry.comp (Metric.toGlueR_isometry left.lastIsometry right.firstIsometry))
  · rfl
  · rfl
  · funext point
    apply congrArg embedding
    exact congrFun (Metric.toGlue_commute left.lastIsometry right.firstIsometry) point

end
end IGSIII34.Diffusion
