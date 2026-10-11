import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteCountableLimitsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter ProbabilityTheory
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

local instance actualObservationCompatibilityMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance actualObservationCompatibilityBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

/-- The compactness laws and the full-past spectral-identification laws
are the same actual walk measure, with exactly the same clock and births. -/
theorem actualPaperDiscreteObservation_eq_completion20261011
    (times : ℕ → ℝ≥0)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (depth : ℕ) :
    actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive times initial depth =
      discreteRescaledObservationLawCompletion20261011
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true))
        (initial depth) (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value marks depth) times
        (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) := by
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion
