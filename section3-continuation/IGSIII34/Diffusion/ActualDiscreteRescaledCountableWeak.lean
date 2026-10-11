import IGSIII34.Diffusion.ActualDiscreteClockRescaleCompletion20261011
import IGSIII34.Diffusion.CountableObservationCouplingWeak
import IGSIII34.Diffusion.FiniteDiscreteClockRescaleWeakCompletion20261011
import IGSIII34.Diffusion.DiscreteCadlagWeakCompletion20261011
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
set_option maxHeartbeats 4200000
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

local instance actualRescaledDiscreteCountableCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualRescaledDiscreteCountableCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualRescaledDiscreteCountableCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualRescaledDiscreteCountableCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualRescaledDiscreteCountableCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualRescaledDiscreteCountableNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualRescaledDiscreteCountableCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledDiscreteCountableNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualRescaledDiscreteCountableTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledDiscreteCountableNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualRescaledDiscreteCountableInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualRescaledDiscreteCountableCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


def actualDiscreteRescaledCountableObservationLaw
    (ratios : ℕ → ℝ≥0) (futureTimes : ℕ → ℝ≥0) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) :=
  ProbabilityMeasure.map
    (⟨finiteDiscreteWalkLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      (clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      initial, inferInstance⟩ : ProbabilityMeasure _)
    ((measurable_pi_lambda _ (fun coordinate =>
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
          chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ depth vertex)).comp
        (measurable_pi_apply ⌊actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value
          ⟨marks.val, marks.property.1.1⟩ depth * (ratios depth : ℝ) * (futureTimes coordinate : ℝ)⌋₊))).aemeasurable)

include anchor in
theorem actual_discrete_rescaled_countable_weak
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
    (ratios : ℕ → ℝ≥0) (ratiosPositive : ∀ depth, 0 < ratios depth)
    (ratio : ℝ≥0) (ratioPositive : 0 < ratio) (ratioConvergence : Tendsto ratios atTop (𝓝 ratio))
    (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw))
    (futureTimes : ℕ → ℝ≥0) :
    Tendsto (fun depth => actualDiscreteRescaledCountableObservationLaw rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive ratios futureTimes depth (initial depth)) atTop
      (𝓝 (limitLaw.map ((measurable_pi_lambda _ (fun coordinate =>
        countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense
          (ratio * futureTimes coordinate))).aemeasurable))) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  let edges := fun depth => ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let endpoint : ∀ depth, edges depth → vertices depth × vertices depth := fun depth =>
    clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let positiveDegree := fun depth => cluster_degree_positive _ _
    (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
  let clocks := fun depth => actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ depth
  let placement := fun depth (vertex : vertices depth) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ depth vertex
  letI : ∀ depth, Nonempty (vertices depth) := fun depth => ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI : ∀ depth, MeasurableSpace (vertices depth) := fun depth =>
    actualFiniteClusterMeasurableSpace rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth
  have clocksPositive : ∀ depth, 0 < clocks depth :=
    actualPaperDiscreteClock_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩
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
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let original := fun depth (trajectory : ℕ → vertices depth) (time : ℝ≥0) =>
    placement depth (trajectory ⌊clocks depth * ((ratios depth * time : ℝ≥0) : ℝ)⌋₊)
  let approximate := fun depth (trajectory : ℕ → vertices depth) (time : ℝ≥0) =>
    placement depth (trajectory ⌊clocks depth * ((ratio * time : ℝ≥0) : ℝ)⌋₊)
  have originalMeasurable (depth : ℕ) (time : ℝ≥0) : Measurable (fun trajectory => original depth trajectory time) :=
    (measurable_of_finite (placement depth)).comp (measurable_pi_apply _)
  have approximateMeasurable (depth : ℕ) (time : ℝ≥0) : Measurable (fun trajectory => approximate depth trajectory time) :=
    (measurable_of_finite (placement depth)).comp (measurable_pi_apply _)
  let target := limitLaw.map ((measurable_pi_lambda _ (fun coordinate =>
    countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense
      (ratio * futureTimes coordinate))).aemeasurable)
  have fixedWeak : Tendsto (fun depth => ProbabilityMeasure.map
      (⟨laws depth, inferInstance⟩ : ProbabilityMeasure (ℕ → vertices depth))
      ((measurable_pi_lambda _ (fun coordinate => approximateMeasurable depth (futureTimes coordinate))).aemeasurable))
      atTop (𝓝 target) := by
    apply countableTimeLaws_weak_of_finite_marginals_completion20261011
    intro count coordinates
    have marginal := marginals count (fun coordinate => ratio * futureTimes (coordinates coordinate))
    convert marginal using 1
    · congr 1
      funext depth
      apply Subtype.ext
      change ((laws depth).map (fun trajectory coordinate => approximate depth trajectory (futureTimes coordinate))).map
        (fun path => fun index : Fin count => path (coordinates index)) =
          (laws depth).map (fun trajectory coordinate => placement depth
            (trajectory ⌊clocks depth * ((ratio * futureTimes (coordinates coordinate) : ℝ≥0) : ℝ)⌋₊))
      rw [Measure.map_map (measurable_pi_lambda _ (fun index => measurable_pi_apply (coordinates index)))
        (measurable_pi_lambda _ (fun coordinate => approximateMeasurable depth (futureTimes coordinate)))]
      rfl
    · apply congrArg (fun probability => 𝓝 probability)
      apply Subtype.ext
      change ((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
        growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map (fun path coordinate =>
        countableTimeContinuousSampleCompletion20261011 times dense path (ratio * futureTimes coordinate))).map
          (fun path => fun index : Fin count => path (coordinates index)) =
            (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
              growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map (fun path coordinate =>
              countableTimeContinuousSampleCompletion20261011 times dense path (ratio * futureTimes (coordinates coordinate)))
      rw [Measure.map_map (measurable_pi_lambda _ (fun index => measurable_pi_apply (coordinates index)))
        (measurable_pi_lambda _ (fun coordinate =>
          countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense
            (ratio * futureTimes coordinate)))]
      rfl
  have physical := finiteFloor_physical_modulus_of_chain_completion20261011 vertices laws placement
    (fun depth => measurable_of_finite _) clocks (fun depth => (clocksPositive depth).le) modulus
  have coupling : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∀ᶠ depth in atTop, ∃ bad : Set (ℕ → vertices depth), MeasurableSet bad ∧ (laws depth).real bad ≤ error ∧
        ∀ trajectory, trajectory ∉ bad → ∀ time : ℝ≥0, (time : ℝ) ≤ horizon →
          dist (original depth trajectory time) (approximate depth trajectory time) ≤ tolerance := by
    intro horizon tolerance error tolerancePositive errorPositive
    let largeHorizon : ℝ≥0 := (ratio+1)*(horizon+1)
    obtain ⟨duration, durationPositive, probabilities⟩ := physical largeHorizon tolerance error tolerancePositive errorPositive
    have ratioBound : ∀ᶠ depth in atTop, ratios depth < ratio+1 :=
      ratioConvergence.eventually (gt_mem_nhds (by simp))
    have ratioNear : ∀ᶠ depth in atTop, dist (ratios depth) ratio < duration/(horizon+1:ℝ) :=
      ratioConvergence.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [probabilities, ratioBound, ratioNear] with depth probability bound near
    obtain ⟨bad, measurableBad, probabilityBad, good⟩ := probability
    refine ⟨bad, measurableBad, probabilityBad, ?_⟩
    intro trajectory outside time before
    have timeBound : time ≤ (horizon+1 : ℝ≥0) := by
      have realBound : (time : ℝ) ≤ (horizon+1 : ℝ) := by exact before.trans (by norm_num)
      exact_mod_cast realBound
    apply good trajectory outside (ratios depth * time) (ratio * time)
      (mul_le_mul bound.le timeBound (by positivity) (by positivity))
      (mul_le_mul (show ratio ≤ ratio+1 from by simp) timeBound (by positivity) (by positivity))
    have identity : dist (ratios depth * time) (ratio * time) = dist (ratios depth) ratio * (time : ℝ) := by
      change |(ratios depth : ℝ)*(time : ℝ)-(ratio : ℝ)*(time : ℝ)| =
        |(ratios depth : ℝ)-(ratio : ℝ)| * (time : ℝ)
      rw [← sub_mul, abs_mul]
      congr 1
      exact abs_of_nonneg time.property
    rw [identity]
    have rawBound : (time : ℝ) ≤ (horizon+1:ℝ) := by exact_mod_cast timeBound
    exact (mul_le_mul_of_nonneg_left rawBound dist_nonneg).trans_lt
      ((lt_div_iff₀ (by positivity : 0 < (horizon+1:ℝ))).mp near)
  have result := countableObservation_weak_of_compact_uniform_coupling
    (fun depth => ℕ → vertices depth) laws futureTimes original approximate originalMeasurable approximateMeasurable
    target fixedWeak coupling
  convert result using 1
  congr 1
  funext depth
  apply Subtype.ext
  change (laws depth).map (fun trajectory coordinate =>
    placement depth (trajectory ⌊clocks depth * (ratios depth : ℝ) * (futureTimes coordinate : ℝ)⌋₊)) =
      (laws depth).map (fun trajectory coordinate =>
    placement depth (trajectory ⌊clocks depth * ((ratios depth * futureTimes coordinate : ℝ≥0) : ℝ)⌋₊))
  congr 1
  funext trajectory coordinate
  simp only [NNReal.coe_mul, mul_assoc]

end
end IGSIII34.Diffusion
