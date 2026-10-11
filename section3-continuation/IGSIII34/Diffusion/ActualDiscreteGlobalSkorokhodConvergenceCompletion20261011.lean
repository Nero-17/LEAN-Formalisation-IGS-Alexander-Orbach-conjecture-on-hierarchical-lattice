import IGSIII34.Diffusion.DiscreteGlobalSkorokhodSampleCompletion20261011
import IGSIII34.Diffusion.ActualRealTimeMarginalsCompletion20261011
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
set_option maxHeartbeats 600000
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

local instance actualGlobalJ1CarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualGlobalJ1CarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualGlobalJ1Completion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualGlobalJ1Completion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualGlobalJ1Completion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualGlobalJ1NormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualGlobalJ1CutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualGlobalJ1NormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualGlobalJ1TopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualGlobalJ1NormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualGlobalJ1InnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualGlobalJ1CompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
theorem actual_discrete_global_skorokhod_convergence_completion20261011
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
    :
    Tendsto (fun depth => discreteGlobalSkorokhodProbabilityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth))
      (clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth)))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true))
      (initial (selected depth))
      (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ (selected depth))
      (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ (selected depth)).le
      (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex)) atTop
      (𝓝 (limitLaw.map (countableSkorokhodGlobalSample_measurable_completion20261011 times dense).aemeasurable)) := by
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
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial (selected depth))
  let samples := fun depth => discreteGlobalSkorokhodSampleCompletion20261011 (clocks depth) (placement depth)
  have clocksNonnegative (depth : ℕ) : 0 ≤ clocks depth :=
    (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ (selected depth)).le
  apply skorokhodGlobal_weak_of_finite_marginals_and_modulus_completion20261011 (fun depth => ℕ → vertices depth)
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (Outcome := ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    laws samples (fun depth => discreteGlobalSkorokhodSample_measurable_completion20261011 _ (clocksNonnegative depth) _)
    (fun depth time => (measurable_of_finite (placement depth)).comp (measurable_pi_apply ⌊clocks depth * (time : ℝ)⌋₊))
    (limitLaw : Measure _) (countableTimeContinuousSampleCompletion20261011 times dense)
    (countableTimeContinuousSample_continuous_completion20261011 times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense)
  · intro horizon grid
    have within (coordinate : Fin (grid+2)) :
        (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid coordinate : ℝ) + 1 ≤ (horizon+2 : ℕ) := by
      have before := NNReal.coe_le_coe.mpr (skorokhodGlobalRegularGridPoint_le_completion20261011 horizon grid coordinate)
      simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at before
      rw [Nat.cast_add, Nat.cast_ofNat]
      linarith
    exact actual_real_time_marginals_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw selected selectedAtTop weak
      (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid) (horizon+2) within
  · intro horizon tolerance error tolerancePositive errorPositive
    let count : ℕ := ⌊(horizon : ℝ)⌋₊ + 2
    have horizonBound : (horizon : ℝ) + 1 ≤ (count : ℝ) := by
      have bound := Nat.lt_floor_add_one (horizon : ℝ)
      dsimp only [count]
      rw [Nat.cast_add, Nat.cast_ofNat]
      linarith
    obtain ⟨duration, durationPositive, probabilities⟩ := actual_floor_interval_modulus_probability_completion20261011
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
      edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBound initial count tolerance error tolerancePositive errorPositive
    refine ⟨duration, durationPositive, ?_⟩
    filter_upwards [selectedAtTop.eventually probabilities] with depth bound
    refine ⟨finiteIntervalChainBadModulusCompletion20261011 (placement depth) (clocks depth) count duration tolerance,
      finiteIntervalChainBadModulus_measurable_completion20261011 _ (measurable_of_finite _) _ _ _ _, bound, ?_⟩
    intro outcome good first second firstBefore secondBefore near
    exact finiteGlobalChain_good_modulus_completion20261011 (placement depth) (clocks depth) count duration tolerance
      (clocksNonnegative depth) outcome good first second
      ((NNReal.coe_le_coe.mpr firstBefore).trans horizonBound)
      ((NNReal.coe_le_coe.mpr secondBefore).trans horizonBound) near

end
end IGSIII34.Diffusion

