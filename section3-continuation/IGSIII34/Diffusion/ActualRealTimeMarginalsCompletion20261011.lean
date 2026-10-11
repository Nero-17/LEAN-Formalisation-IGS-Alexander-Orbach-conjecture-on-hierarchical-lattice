import IGSIII34.Diffusion.ActualDiscreteSkorokhodConvergenceCompletion20261011
import IGSIII34.Diffusion.DiscreteSkorokhodWeakConvergenceCompletion20261011
import IGSIII34.Diffusion.DenseObservationFiniteTimesCompletion20261011
import IGSIII34.Diffusion.ScaledContinuousIntervalSampleCompletion20261011
import IGSIII34.Diffusion.ActualIntervalFloorModulusCompletion20261011
import IGSIII34.Diffusion.ActualContinuousWalkLimitsCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteObservationCompatibilityCompletion20261011
import IGSIII34.Diffusion.ActualElectricalChainModulusCompletion20261011
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion20261011
import IGSIII34.Diffusion.ActualCutoffResolventApproximationCompletion20261011
import IGSIII34.Diffusion.ActualWalkSmallJumpsCompletion20261011
import IGSIII34.Diffusion.ResolventChainTightnessCompletion20261011
import IGSIII34.Diffusion.CountableProcessJointMeasurabilityCompletion20261011
import IGSIII34.Diffusion.CompactPlateauCoverCompletion20261011
import IGSIII34.Diffusion.ActualScaledContinuousResolventCompletion20261011
import IGSIII34.Diffusion.ActualPaperClockGrowthCompletion20261011
import IGSIII34.Diffusion.ActualWholeContinuousResolventCompletion20261011
import IGSIII34.Forms.ActualRegularityCompletion20261011
import IGSIII34.Diffusion.ActualResolventWholePointwiseCompletion20261011
import IGSIII34.Diffusion.ActualPrescribedLimitEnergyCompletion20261011
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion20261011
import IGSIII34.Diffusion.ActualHarmonicObjectiveUniquenessCompletion20261011
import IGSIII34.Diffusion.ActualConstructedRecoveryCompletion20261011
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion20261011
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry IGSIII34.Forms MeasureTheory Filter
open scoped _root_.Topology BigOperators NNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance actualRealTimeMarginalCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualRealTimeMarginalCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualRealTimeMarginalCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualRealTimeMarginalCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualRealTimeMarginalCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualRealTimeMarginalNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualRealTimeMarginalCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRealTimeMarginalNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualRealTimeMarginalTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRealTimeMarginalNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualRealTimeMarginalInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualRealTimeMarginalCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
/-- Every real-time finite marginal of the original walk converges to
 the genuine continuous sample constructed from its dense observation
 weak limit. The original all-index modulus is proved internally. -/
theorem actual_real_time_marginals_completion20261011
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected depth)) atTop (𝓝 limitLaw))
    {count : ℕ} (futureTimes : Fin count → ℝ≥0) (horizon : ℕ)
    (within : ∀ index, (futureTimes index : ℝ) + 1 ≤ horizon) :
    Tendsto (fun depth => (discreteWalkProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth))
      (clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth)))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true))
      (initial (selected depth))).map
      (finiteFlooredTimeSample_measurable_completion20261011
        (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ (selected depth))
        futureTimes (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth) =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex)).aemeasurable) atTop
      (𝓝 (limitLaw.map (show AEMeasurable (fun path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ =>
        fun index : Fin count => countableTimeContinuousSampleCompletion20261011 times dense path (futureTimes index)) (limitLaw : Measure _) from
        (measurable_pi_lambda _ fun index => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense (futureTimes index)).aemeasurable))) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth)
  let edges := fun depth => ClusterEdge (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth))
  let endpoint : ∀ depth, edges depth → vertices depth × vertices depth := fun depth =>
    clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth))
  let positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex := fun depth =>
    cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true)
  let clocks := fun depth => actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value
    ⟨marks.val, marks.property.1.1⟩ (selected depth)
  let placement := fun depth (vertex : vertices depth) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex
  have clocksNonnegative (depth : ℕ) : 0 ≤ clocks depth :=
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ (selected depth)).le
  have weakGeneric : Tendsto (fun depth => discreteRescaledObservationLawCompletion20261011 (endpoint depth) (positiveDegree depth)
      (initial (selected depth)) (clocks depth) times (placement depth)) atTop (𝓝 limitLaw) := by
    apply weak.congr'
    apply Eventually.of_forall
    intro depth
    exact actualPaperDiscreteObservation_eq_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected depth)
  have regular := (actual_discrete_weak_limit_continuous_paths_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw selected selectedAtTop weak).1
  apply finiteFlooredTimeLaw_weak_of_dense_observations_completion20261011 vertices edges endpoint positiveDegree
    (fun depth => initial (selected depth)) clocks clocksNonnegative placement times dense limitLaw weakGeneric regular futureTimes horizon within
  intro tolerance error tolerancePositive errorPositive
  obtain ⟨duration, durationPositive, probabilities⟩ := actual_floor_interval_modulus_probability_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
    edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBound initial horizon tolerance error tolerancePositive errorPositive
  exact ⟨duration, durationPositive, selectedAtTop.eventually probabilities⟩

end
end IGSIII34.Diffusion
