import IGSIII34.Diffusion.OriginalJointCompactDistance
import IGSIII34.Diffusion.WholeCadlagIsometricTransport
import IGSIII34.Diffusion.JointMeasuredMarkedStateIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped NNReal

/-- Original compact spatial metrics, both ordered marks and masses, and
whole paths are encoded by an actual Kuratowski isometry. -/
def OriginalJointCompactRepresentative.ofCompactSpace
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion Space) : OriginalJointCompactRepresentative := by
  letI : Nonempty Space := ⟨marks true⟩
  let compact : NonemptyCompacts OriginalJointUniversalSpace := NonemptyCompacts.kuratowskiEmbedding Space
  let embedding : Space ≃ᵢ compact := (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  exact {
    carrier := compact
    marks := embedding ∘ marks
    masses := fun side => (masses side).map embedding.continuous.measurable.aemeasurable
    path := skorokhodCadlagContinuousCarrierMapCompletion embedding embedding.continuous path }

def originalJointCompactPathEncoding
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion Space) : OriginalJointCompactSpace :=
  originalJointCompactClass (.ofCompactSpace marks masses path)

end
end IGSIII34.Diffusion
