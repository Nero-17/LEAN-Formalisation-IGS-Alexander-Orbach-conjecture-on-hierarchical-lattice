import IGSIII34.Diffusion.FiniteVertexInitialApproximationCompletion20261011
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011
import IGSIII34.Diffusion.ElectricalHalfOwnershipCompletion20261011
import IGSIII34.Diffusion.VanishingComparison

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency true

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

local instance actualInitialApproxCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance actualInitialApproxCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)).IsOpenPosMeasure]

/-- Every point of the same actual electrical carrier has a sequence of
original finite full-cluster starting vertices converging to it. The
placed initial Dirac probabilities converge to its Dirac law. -/
theorem actual_electrical_every_initial_point_approximation_completion20261011
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :
    ∃ selected : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth,
      Tendsto (fun depth => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth (selected depth))
        atTop (𝓝 point) ∧
      Tendsto (fun depth => diracProba (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth (selected depth)))
        atTop (𝓝 (diracProba point)) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  let mass : ∀ depth, ProbabilityMeasure (vertices depth) := fun depth =>
    ⟨actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
      chemicalScale chemicalScalePositive depth, inferInstance⟩
  let placement := fun depth (vertex : vertices depth) =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex
  have weak : Tendsto (fun depth => (mass depth).map (measurable_of_finite (placement depth)).aemeasurable)
      atTop (𝓝 measure) := by
    apply probability_weak_of_levyProkhorov_completion20261011
    exact degreeLimit
  exact exists_finiteVertex_initial_approximation_completion20261011 vertices mass placement measure weak point

end
end IGSIII34.Diffusion
