import IGSIII34.ResistanceLimit.ActualPaperCadlagSameLaw
import IGSIII34.Diffusion.ActualCountableWholeWeakCompletion

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
local instance actualPaperInitialElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := borel _
local instance actualPaperInitialElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩) := ⟨rfl⟩
variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)]

/-- The continuous sample constructed from the actual walk limit has the
prescribed initial distribution, including for every Dirac starting point. -/
theorem actual_paper_limit_initial_law
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times)
    (initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))
    (initialConvergence : Tendsto (fun depth => (initial depth).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 initialLimit))
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion
      rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩
      chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw))
    (regular : ∀ᵐ path ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩)), countableTimeLocalUniformContinuityCompletion times path) :
    (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩)).map
      (fun path => countableTimeContinuousSampleCompletion times dense path 0) = (initialLimit : Measure _) := by
  let laws := fun depth => actualPaperDiscreteElectricalObservationLawCompletion
    rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩
    chemicalScale chemicalScalePositive times initial depth
  have zeroMarginal : ∀ depth, (laws depth).map (measurable_pi_apply 0).aemeasurable =
      (initial depth).map
        (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩ depth vertex)).aemeasurable := by
    intro depth
    exact discreteRescaledObservationLaw_initial_completion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      (initial depth) (actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩ depth)
      times timeZero (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ depth vertex)
  have marginalConvergence : Tendsto (fun depth => (laws depth).map (measurable_pi_apply 0).aemeasurable)
      atTop (𝓝 initialLimit) := by
    simpa only [zeroMarginal] using initialConvergence
  have initialIdentity := countableTimeLaws_limit_marginal_completion laws limitLaw id tendsto_id
    weak 0 initialLimit marginalConvergence
  have agreement := countableTimeContinuousSample_ae_agreement_completion times dense limitLaw regular
  have agreementZero : (fun path => countableTimeContinuousSampleCompletion times dense path 0) =ᵐ[
      (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩))] (fun path => path 0) := by
    filter_upwards [agreement] with path agrees
    simpa only [timeZero] using agrees 0
  rw [Measure.map_congr agreementZero]
  exact congrArg (fun law : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
    growth value growthPositive ⟨marks.val,marks.property.1.1⟩) =>
    (law : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val,marks.property.1.1⟩))) initialIdentity

end
end IGSIII34.ResistanceLimit
