import IGSIII34.Diffusion.OriginalJointCompactCoupling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace

/-- The entire compact ambient retains the original spatial metric. Its
specified geometric carrier may be a proper compact subset; these extended
states are used only to extend tests from legitimate original states. -/
structure ExtendedJointCompactRepresentative where
  ambient : NonemptyCompacts OriginalJointUniversalSpace
  state : JointMeasuredMarkedState ambient
  path : SkorokhodCadlagPathCompletion20261011 ambient

/-- Every original representative is an extended representative whose
specified geometric carrier is its entire compact ambient. -/
def ExtendedJointCompactRepresentative.ofOriginal
    (representative : OriginalJointCompactRepresentative) : ExtendedJointCompactRepresentative where
  ambient := representative.carrier
  state := originalJointRepresentativeState representative
  path := representative.path

/-- A compact-space state and entire cadlag path are represented using the
true Kuratowski spatial isometry, with no change of original metric. -/
def ExtendedJointCompactRepresentative.ofCompactSpace
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (state : JointMeasuredMarkedState Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) : ExtendedJointCompactRepresentative := by
  letI : Nonempty Space := state.1.nonempty.to_subtype.map Subtype.val
  let embedding := (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  exact {
    ambient := NonemptyCompacts.kuratowskiEmbedding Space
    state := jointMeasuredMarkedStateMap embedding embedding.isometry.continuous state
    path := skorokhodCadlagContinuousCarrierMapCompletion20261011
      embedding embedding.isometry.continuous path }

end
end IGSIII34.Diffusion
