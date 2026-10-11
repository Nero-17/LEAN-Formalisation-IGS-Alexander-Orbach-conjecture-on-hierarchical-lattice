import IGSIII34.Diffusion.FiniteWeightedClockRescaleWeakCompletion20261011
import IGSIII34.Diffusion.FiniteWeightedGlobalWeakCompletion20261011
import IGSIII34.Diffusion.CenteredClockProbabilityBridgeCompletion20261011
import IGSIII34.Diffusion.ActualVertexVariableSpeedWalkCompletion20261011
import IGSIII34.Diffusion.ActualCountingClockDensityCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteGlobalWholeWeakCompletion20261011
import IGSIII34.Diffusion.FiniteContinuousGlobalWeakCompletion20261011
import IGSIII34.Diffusion.ActualDiscreteGlobalSkorokhodConvergenceCompletion20261011
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
open scoped _root_.Topology BigOperators NNReal ENNReal

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance actualRescaledWeightedGlobalJ1CarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualRescaledWeightedGlobalJ1CarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualRescaledWeightedGlobalJ1Completion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualRescaledWeightedGlobalJ1Completion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualRescaledWeightedGlobalJ1Completion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualRescaledWeightedGlobalJ1NormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualRescaledWeightedGlobalJ1CutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledWeightedGlobalJ1NormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualRescaledWeightedGlobalJ1TopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledWeightedGlobalJ1NormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualRescaledWeightedGlobalJ1InnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualRescaledWeightedGlobalJ1CompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

def actualWeightedClockRescaledGlobalLawCompletion20261011
    (countingSpeed : Bool) (ratios : ℕ → ℝ≥0) (ratiosPositive : ∀ depth, 0 < ratios depth)
    (depth : ℕ) (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011
      (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  exact finiteWeightedGlobalSkorokhodProbabilityCompletion20261011
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
    (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) initial
    (fun vertex => if countingSpeed then finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex else 1)
    (by intro vertex; cases countingSpeed
        · exact zero_lt_one
        · exact finiteCountingClockDensity_positive_completion20261011
            (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
            _ (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) vertex)
    (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth * (ratios depth:ℝ))
    (mul_pos (actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)
      (NNReal.coe_pos.mpr (ratiosPositive depth)))
    (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth)
include anchor in
theorem actual_weighted_rescaled_global_weak_completion20261011
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
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (weightsBounded : ∀ depth vertex, finiteCountingClockDensityCompletion20261011
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) vertex ≤ bound)
    (centeredClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (finiteDiscreteWalkLaw
        (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
        (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
        (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)) (initial depth)).real
        {path | ∃ count ≤ ⌊actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth * horizon⌋₊,
          tolerance ≤ |finiteWalkScaledAdditiveCompletion20261011
            (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth)
            (actualCountingClockCenteredForcingCompletion20261011 rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) count path|}) atTop (𝓝 0))
    (countingSpeed : Bool) (ratios : ℕ → ℝ≥0) (ratiosPositive : ∀ depth, 0 < ratios depth)
    (ratio : ℝ≥0) (ratioPositive : 0 < ratio) (ratioConvergence : Tendsto ratios atTop (𝓝 ratio))
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw)) :
    Tendsto (fun depth => actualWeightedClockRescaledGlobalLawCompletion20261011
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive
      countingSpeed ratios ratiosPositive depth (initial depth)) atTop
      (𝓝 (limitLaw.map (continuousGlobalFamily_measurable_completion20261011
        (fun path time => countableTimeContinuousSampleCompletion20261011 times dense path (ratio*time))
        (fun path => (countableTimeContinuousSample_continuous_completion20261011 times dense path).comp (continuous_const.mul continuous_id))
        (fun time => countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense (ratio*time))).aemeasurable)) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  let edges := fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let endpoint : ∀ depth, edges depth → vertices depth × vertices depth := fun depth =>
    clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let positiveDegree := fun depth => cluster_degree_positive _ _
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  let clocks := fun depth => actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth
  let weights := fun depth (vertex : vertices depth) => if countingSpeed then finiteCountingClockDensityCompletion20261011 (endpoint depth) vertex else 1
  let placement := fun depth (vertex : vertices depth) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ depth vertex
  letI : ∀ depth, Nonempty (vertices depth) := fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI : ∀ depth, MeasurableSpace (vertices depth) := fun depth =>
    actualFiniteClusterMeasurableSpace rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  have clocksPositive : ∀ depth, 0 < clocks depth :=
    actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩
  have weightPositive (depth : ℕ) (vertex : vertices depth) : 0 < weights depth vertex := by
    letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
      (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
    cases countingSpeed
    · exact zero_lt_one
    · exact finiteCountingClockDensity_positive_completion20261011 (endpoint depth) (positiveDegree depth) vertex
  have weightBound (depth : ℕ) (vertex : vertices depth) : weights depth vertex ≤ max bound 1 := by
    cases countingSpeed
    · exact le_max_right _ _
    · exact (weightsBounded depth vertex).trans (le_max_left _ _)
  have centered : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth))
        {path | ∃ count ≤ ⌊clocks depth*horizon⌋₊, clocks depth*tolerance <
          |centeredWeightClockCompletion20261011 (fun index => weights depth (path index)) count|}) atTop (𝓝 0) := by
    cases countingSpeed
    · intro horizon tolerance horizonNonnegative tolerancePositive
      have empty (depth : ℕ) : {path : ℕ → vertices depth | ∃ count ≤ ⌊clocks depth*horizon⌋₊,
          clocks depth*tolerance < |centeredWeightClockCompletion20261011 (fun index => weights depth (path index)) count|} = ∅ := by
        ext path
        simp only [weights, Bool.false_eq_true, ↓reduceIte, centeredWeightClockCompletion20261011, sub_self,
          Finset.sum_const_zero, abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro count bounded
        exact (mul_pos (clocksPositive depth) tolerancePositive).le.not_gt
      simpa only [empty, measure_empty] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
    · exact centeredClock_probability_of_scaled_real_completion20261011 vertices
        (fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth))
        (fun depth => finiteCountingClockDensityCompletion20261011 (endpoint depth)) clocks clocksPositive centeredClock
  have modulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion20261011 (placement depth) (clocks depth) horizon duration tolerance) ≤ error := by
    intro horizon tolerance error tolerancePositive errorPositive
    exact actual_floor_interval_modulus_probability_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound initial horizon tolerance error tolerancePositive errorPositive
  have marginals : ∀ count (futureTimes : Fin count → ℝ≥0),
      Tendsto (fun depth => ProbabilityMeasure.map
        (⟨finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth), inferInstance⟩ : ProbabilityMeasure (ℕ → vertices depth))
        ((measurable_pi_lambda _ fun coordinate => (measurable_of_finite (placement depth)).comp
          (measurable_pi_apply ⌊clocks depth * futureTimes coordinate⌋₊)).aemeasurable)) atTop
        (𝓝 (limitLaw.map ((measurable_pi_lambda _ fun coordinate =>
          countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense (futureTimes coordinate)).aemeasurable))) := by
    intro count futureTimes
    let horizon := ⌈((Finset.univ.sup futureTimes : ℝ≥0):ℝ) + 1⌉₊
    have within (index : Fin count) : (futureTimes index:ℝ)+1 ≤ (horizon:ℝ) := by
      have before : (futureTimes index:ℝ) ≤ ((Finset.univ.sup futureTimes:ℝ≥0):ℝ) :=
        NNReal.coe_le_coe.mpr (Finset.le_sup (f := futureTimes) (Finset.mem_univ index))
      have after : ((Finset.univ.sup futureTimes:ℝ≥0):ℝ)+1 ≤ (horizon:ℝ) := Nat.le_ceil _
      linarith
    exact actual_real_time_marginals_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw id tendsto_id weak
      futureTimes horizon within
  have result := finiteWeighted_varying_clock_weak_completion20261011 vertices edges endpoint positiveDegree initial weights weightPositive
    (max bound 1) (le_max_of_le_left boundNonnegative) weightBound clocks clocksPositive
    (actualPaperDiscreteClock_diverges_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ growthGreaterThanOne)
    placement centered ratios ratiosPositive ratio ratioPositive ratioConvergence limitLaw
    (countableTimeContinuousSampleCompletion20261011 times dense)
    (countableTimeContinuousSample_continuous_completion20261011 times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense) marginals modulus
  convert result using 1
  funext depth
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion
