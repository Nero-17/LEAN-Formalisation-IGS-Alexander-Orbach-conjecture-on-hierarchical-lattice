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
    (path : SkorokhodCadlagPathCompletion20261011 Space) : OriginalJointCompactRepresentative := by
  letI : Nonempty Space := ⟨marks true⟩
  let embedding := (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  exact {
    carrier := NonemptyCompacts.kuratowskiEmbedding Space
    marks := embedding ∘ marks
    masses := fun side => (masses side).map embedding.continuous.measurable.aemeasurable
    path := skorokhodCadlagContinuousCarrierMapCompletion20261011 embedding embedding.continuous path }

def originalJointCompactPathEncoding
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space)
    (path : SkorokhodCadlagPathCompletion20261011 Space) : OriginalJointCompactSpace :=
  originalJointCompactClass (.ofCompactSpace marks masses path)

theorem originalJointCompactPathEncoding_lipschitz
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space) :
    LipschitzWith 1 (originalJointCompactPathEncoding marks masses) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  letI : Nonempty Space := ⟨marks true⟩
  let embedding := (kuratowskiEmbedding.isometry Space).isometryEquivOnRange
  let coupling : OriginalJointCompactCoupling
      (.ofCompactSpace marks masses first) (.ofCompactSpace marks masses last) := {
    ambient := NonemptyCompacts.kuratowskiEmbedding Space
    firstPlacement := id
    firstIsometry := isometry_id
    lastPlacement := id
    lastIsometry := isometry_id }
  have upper := originalJointCompactDistance_le_cost coupling
  have cost : coupling.cost = dist first last := by
    simp only [OriginalJointCompactCoupling.cost, coupling,
      OriginalJointCompactRepresentative.ofCompactSpace, originalJointRepresentativeState,
      jointMeasuredMarkedStateMap, Function.comp_def]
    simp only [jointMeasuredMarkedStateCost, dist_self, levyProkhorovDist_self, Finset.sum_const_zero,
      zero_add, add_zero]
    exact (skorokhodCadlagCarrierMap_isometry embedding embedding.isometry).dist_eq first last
  simpa only [originalJointCompactPathEncoding, originalJointCompactClass_dist,
    NNReal.coe_one, one_mul, cost] using upper

theorem originalJointCompactPathEncoding_continuous
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space) :
    Continuous (originalJointCompactPathEncoding marks masses) :=
  (originalJointCompactPathEncoding_lipschitz marks masses).continuous

end
end IGSIII34.Diffusion
