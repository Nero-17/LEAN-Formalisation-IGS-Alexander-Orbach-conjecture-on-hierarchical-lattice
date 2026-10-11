import IGSIII34.Diffusion.ActualFiniteInitialApproximationCompletion20261011
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

local instance actualDiracInitialCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance actualDiracInitialCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)]
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks)).IsOpenPosMeasure]

/-- Every point is reached by genuine point-started original finite walk
initial laws; the initial-law convergence required by the actual path
convergence theorem is thus available for every starting point. -/
theorem actual_electrical_every_dirac_initial_law_completion20261011
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :
    ∃ initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth),
      Tendsto (fun depth => (initial depth).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)).aemeasurable)
        atTop (𝓝 (diracProba point)) ∧
      ∀ depth, ∃ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth,
        initial depth = diracProba vertex := by
  obtain ⟨selected, _, diracWeak⟩ := actual_electrical_every_initial_point_approximation_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure degreeLimit point
  refine ⟨fun depth => diracProba (selected depth), ?_, fun depth => ⟨selected depth, rfl⟩⟩
  apply diracWeak.congr'
  apply Eventually.of_forall
  intro depth
  apply Subtype.ext
  change Measure.dirac (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth (selected depth)) =
    (Measure.dirac (selected depth)).map
      (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)
  exact (Measure.map_dirac' (measurable_of_finite _) (selected depth)).symm

end
end IGSIII34.Diffusion
