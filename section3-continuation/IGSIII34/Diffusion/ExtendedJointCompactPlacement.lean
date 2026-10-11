import IGSIII34.Diffusion.ExtendedJointCompactCoupling
import IGSIII34.Diffusion.JointMeasuredMarkedStateIsometry
import IGSIII34.Diffusion.JointMeasuredMarkedStateMetricBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped BigOperators

@[simp] theorem jointMeasuredMarkedStateMap_id
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space) :
    jointMeasuredMarkedStateMap id continuous_id state = state := by
  apply Prod.ext
  · exact state.1.map_id
  · apply Prod.ext
    · rfl
    · funext side
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_id

@[simp] theorem skorokhodCadlagContinuousCarrierMap_id
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    skorokhodCadlagContinuousCarrierMapCompletion20261011 id continuous_id path = path := by
  apply Subtype.ext
  rfl

def originalExtendedJointCompactCouplingEquiv
    (first last : OriginalJointCompactRepresentative) :
    OriginalJointCompactCoupling first last ≃
      ExtendedJointCompactCoupling (.ofOriginal first) (.ofOriginal last) where
  toFun := OriginalJointCompactCoupling.toExtended
  invFun := ExtendedJointCompactCoupling.toOriginal
  left_inv coupling := by cases coupling; rfl
  right_inv coupling := by cases coupling; rfl

/-- Two states and paths already in the same compact space use the same
true Kuratowski spatial placement. -/
def ExtendedJointCompactCoupling.sameCompactSpace
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (first last : JointMeasuredMarkedState Space)
    (firstPath lastPath : SkorokhodCadlagPathCompletion20261011 Space) :
    ExtendedJointCompactCoupling
      (.ofCompactSpace first firstPath) (.ofCompactSpace last lastPath) where
  ambient := (ExtendedJointCompactRepresentative.ofCompactSpace first firstPath).ambient
  firstPlacement := id
  firstIsometry := isometry_id
  lastPlacement := id
  lastIsometry := isometry_id

theorem ExtendedJointCompactCoupling.sameCompactSpace_cost
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (first last : JointMeasuredMarkedState Space)
    (firstPath lastPath : SkorokhodCadlagPathCompletion20261011 Space) :
    (sameCompactSpace first last firstPath lastPath).cost =
      jointMeasuredMarkedStateCost first last + dist firstPath lastPath := by
  letI : Nonempty Space := first.1.nonempty.to_subtype.map Subtype.val
  let compact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding Space
  let embedding : Space ≃ᵢ compact :=
    (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  simp only [cost, sameCompactSpace, ExtendedJointCompactRepresentative.ofCompactSpace,
    jointMeasuredMarkedStateMap_id, skorokhodCadlagContinuousCarrierMap_id]
  change jointMeasuredMarkedStateCost
      (jointMeasuredMarkedStateMap embedding embedding.isometry.continuous first)
      (jointMeasuredMarkedStateMap embedding embedding.isometry.continuous last) +
    dist (skorokhodCadlagContinuousCarrierMapCompletion20261011
      embedding embedding.isometry.continuous firstPath)
      (skorokhodCadlagContinuousCarrierMapCompletion20261011
        embedding embedding.isometry.continuous lastPath) = _
  rw [jointMeasuredMarkedStateCost_isometric_map embedding embedding.isometry,
    (skorokhodCadlagCarrierMap_isometry embedding embedding.isometry).dist_eq]

theorem ExtendedJointCompactCoupling.sameCompactSpace_same_path_cost
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (first last : JointMeasuredMarkedState Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) :
    (sameCompactSpace first last path path).cost = jointMeasuredMarkedStateCost first last := by
  rw [sameCompactSpace_cost, dist_self, add_zero]

theorem ExtendedJointCompactCoupling.sameCompactSpace_same_state_cost
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (firstPath lastPath : SkorokhodCadlagPathCompletion20261011 Space) :
    (sameCompactSpace state state firstPath lastPath).cost = dist firstPath lastPath := by
  rw [sameCompactSpace_cost]
  simp [jointMeasuredMarkedStateCost, levyProkhorovDist_self]

/-- Re-encoding an extended representative by its compact ambient leaves
its state and entire path at zero coupling cost. -/
def ExtendedJointCompactCoupling.canonicalize
    (representative : ExtendedJointCompactRepresentative) :
    ExtendedJointCompactCoupling representative
      (.ofCompactSpace representative.state representative.path) where
  ambient := NonemptyCompacts.kuratowskiEmbedding representative.ambient
  firstPlacement := (kuratowskiEmbedding.isometry representative.ambient).isometryEquivOnRange
  firstIsometry := (kuratowskiEmbedding.isometry representative.ambient).isometryEquivOnRange.isometry
  lastPlacement := id
  lastIsometry := isometry_id

theorem ExtendedJointCompactCoupling.canonicalize_cost
    (representative : ExtendedJointCompactRepresentative) :
    (canonicalize representative).cost = 0 := by
  simp only [cost, canonicalize, ExtendedJointCompactRepresentative.ofCompactSpace]
  rw [jointMeasuredMarkedStateMap_id, skorokhodCadlagContinuousCarrierMap_id]
  simp [jointMeasuredMarkedStateCost, levyProkhorovDist_self]

/-- A spatial isometry is realized inside the entire target compact
ambient, so it has zero extended joint cost. -/
def ExtendedJointCompactCoupling.isometricTransport
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First)
    (path : SkorokhodCadlagPathCompletion20261011 First) :
    ExtendedJointCompactCoupling (.ofCompactSpace state path)
      (.ofCompactSpace (jointMeasuredMarkedStateMap mapping isometry.continuous state)
        (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path)) := by
  letI : Nonempty First := state.1.nonempty.to_subtype.map Subtype.val
  letI : Nonempty Last := (show Nonempty First from inferInstance).map mapping
  let firstCompact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding First
  let lastCompact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding Last
  let firstEmbedding : First ≃ᵢ firstCompact :=
    (kuratowskiEmbedding.isometry First).isometryEquivOnRange
  let lastEmbedding : Last ≃ᵢ lastCompact :=
    (kuratowskiEmbedding.isometry Last).isometryEquivOnRange
  exact {
    ambient := NonemptyCompacts.kuratowskiEmbedding Last
    firstPlacement := lastEmbedding ∘ mapping ∘ firstEmbedding.symm
    firstIsometry := lastEmbedding.isometry.comp (isometry.comp firstEmbedding.symm.isometry)
    lastPlacement := id
    lastIsometry := isometry_id }

theorem ExtendedJointCompactCoupling.isometricTransport_cost
    {First Last : Type} [MetricSpace First] [CompactSpace First]
    [MeasurableSpace First] [BorelSpace First]
    [MetricSpace Last] [CompactSpace Last]
    [MeasurableSpace Last] [BorelSpace Last]
    (mapping : First → Last) (isometry : Isometry mapping)
    (state : JointMeasuredMarkedState First)
    (path : SkorokhodCadlagPathCompletion20261011 First) :
    (isometricTransport mapping isometry state path).cost = 0 := by
  letI : Nonempty First := state.1.nonempty.to_subtype.map Subtype.val
  letI : Nonempty Last := (show Nonempty First from inferInstance).map mapping
  let firstCompact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding First
  let lastCompact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding Last
  let firstEmbedding : First ≃ᵢ firstCompact :=
    (kuratowskiEmbedding.isometry First).isometryEquivOnRange
  let lastEmbedding : Last ≃ᵢ lastCompact :=
    (kuratowskiEmbedding.isometry Last).isometryEquivOnRange
  have composition :
      (lastEmbedding ∘ mapping ∘ firstEmbedding.symm) ∘ firstEmbedding =
        lastEmbedding ∘ mapping := by
    funext point
    simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply]
  have states : jointMeasuredMarkedStateMap
      (lastEmbedding ∘ mapping ∘ firstEmbedding.symm)
      (lastEmbedding.isometry.comp (isometry.comp firstEmbedding.symm.isometry)).continuous
      (jointMeasuredMarkedStateMap firstEmbedding firstEmbedding.isometry.continuous state) =
      jointMeasuredMarkedStateMap lastEmbedding lastEmbedding.isometry.continuous
        (jointMeasuredMarkedStateMap mapping isometry.continuous state) := by
    rw [jointMeasuredMarkedStateMap_comp, jointMeasuredMarkedStateMap_comp]
    simp only [composition]
  have paths : skorokhodCadlagContinuousCarrierMapCompletion20261011
      (lastEmbedding ∘ mapping ∘ firstEmbedding.symm)
      (lastEmbedding.isometry.comp (isometry.comp firstEmbedding.symm.isometry)).continuous
      (skorokhodCadlagContinuousCarrierMapCompletion20261011
        firstEmbedding firstEmbedding.isometry.continuous path) =
      skorokhodCadlagContinuousCarrierMapCompletion20261011 lastEmbedding lastEmbedding.isometry.continuous
        (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path) := by
    rw [skorokhodCadlagCarrierMap_comp, skorokhodCadlagCarrierMap_comp]
    simp only [composition]
  simp only [cost, isometricTransport, ExtendedJointCompactRepresentative.ofCompactSpace,
    jointMeasuredMarkedStateMap_id, skorokhodCadlagContinuousCarrierMap_id]
  change jointMeasuredMarkedStateCost
      (jointMeasuredMarkedStateMap (lastEmbedding ∘ mapping ∘ firstEmbedding.symm)
        (lastEmbedding.isometry.comp (isometry.comp firstEmbedding.symm.isometry)).continuous
        (jointMeasuredMarkedStateMap firstEmbedding firstEmbedding.isometry.continuous state))
      (jointMeasuredMarkedStateMap lastEmbedding lastEmbedding.isometry.continuous
        (jointMeasuredMarkedStateMap mapping isometry.continuous state)) +
      dist (skorokhodCadlagContinuousCarrierMapCompletion20261011
        (lastEmbedding ∘ mapping ∘ firstEmbedding.symm)
        (lastEmbedding.isometry.comp (isometry.comp firstEmbedding.symm.isometry)).continuous
        (skorokhodCadlagContinuousCarrierMapCompletion20261011
          firstEmbedding firstEmbedding.isometry.continuous path))
      (skorokhodCadlagContinuousCarrierMapCompletion20261011
        lastEmbedding lastEmbedding.isometry.continuous
        (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous path)) = 0
  rw [states, paths]
  simp [jointMeasuredMarkedStateCost, levyProkhorovDist_self]

end
end IGSIII34.Diffusion
