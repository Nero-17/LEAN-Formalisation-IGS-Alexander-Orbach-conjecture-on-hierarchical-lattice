import IGSIII34.Diffusion.OriginalExtendedJointCompactPathBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped NNReal

theorem originalJointCompactPathEncoding_lipschitz
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space) :
    LipschitzWith 1 (originalJointCompactPathEncoding marks masses) := by
  apply LipschitzWith.of_dist_le_mul
  intro first last
  rw [← originalJointCompactSpaceToExtended_isometry.dist_eq]
  simp only [originalJointCompactPathEncoding_toExtended]
  exact (extendedJointStatePathClass_lipschitz (originalJointCompactFullState marks masses)).dist_le_mul first last

theorem originalJointCompactPathEncoding_continuous
    {Space : Type} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (marks : Bool → Space) (masses : Bool → ProbabilityMeasure Space) :
    Continuous (originalJointCompactPathEncoding marks masses) :=
  (originalJointCompactPathEncoding_lipschitz marks masses).continuous

end
end IGSIII34.Diffusion
