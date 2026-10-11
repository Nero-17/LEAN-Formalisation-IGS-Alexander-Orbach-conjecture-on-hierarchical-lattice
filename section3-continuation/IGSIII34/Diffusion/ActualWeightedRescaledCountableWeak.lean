import IGSIII34.Diffusion.ActualDiscreteRescaledCountableWeak
import IGSIII34.Diffusion.CountableObservationCouplingWeak
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

local instance actualRescaledWeightedCountableCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualRescaledWeightedCountableCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualRescaledWeightedCountableCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualRescaledWeightedCountableCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualRescaledWeightedCountableCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualRescaledWeightedCountableNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualRescaledWeightedCountableCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledWeightedCountableNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualRescaledWeightedCountableTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualRescaledWeightedCountableNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualRescaledWeightedCountableInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualRescaledWeightedCountableCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

/-- Literal original neighbour-chain and independent exponential sample,
with rate-one or normalized inverse-degree holding times. -/
def actualWeightedRescaledCountableObservationLaw
    (countingSpeed : Bool) (ratios : ℕ → ℝ≥0) (futureTimes : ℕ → ℝ≥0) (depth : ℕ)
    (initial : ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)) :
    ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩) := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  let endpoint := clusterRetainedEndpoint (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
  let weights := fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
    if countingSpeed then finiteCountingClockDensityCompletion20261011 endpoint vertex else 1
  let placement := fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex
  exact ProbabilityMeasure.map
    (⟨finiteContinuousWalkSampleLaw
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
      endpoint (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true))
      initial, inferInstance⟩ : ProbabilityMeasure _)
    ((measurable_pi_lambda _ (fun coordinate => (measurable_of_finite placement).comp
      ((holdingTimePath_measurable (actualPaperDiscreteClockCompletion20261011 rule p positive belowOne fixedPoint growth value
        ⟨marks.val, marks.property.1.1⟩ depth * (ratios depth : ℝ) * (futureTimes coordinate : ℝ))).comp
          (weightedHoldingSample_measurable_completion20261011 weights)))).aemeasurable)

include anchor in
theorem actual_weighted_rescaled_countable_weak
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
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw))    (futureTimes : ℕ → ℝ≥0) :
    Tendsto (fun depth => actualWeightedRescaledCountableObservationLaw rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive countingSpeed ratios futureTimes depth (initial depth)) atTop
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
  have diverge : Tendsto clocks atTop atTop :=
    actualPaperDiscreteClock_diverges_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ growthGreaterThanOne
  have realConvergence : Tendsto (fun depth => (ratios depth : ℝ)) atTop (𝓝 (ratio:ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp ratioConvergence
  let upper : ℕ := ⌈(ratio:ℝ)⌉₊ + 1
  have upperPositive : 0 < upper := by dsimp only [upper]; omega
  have upperLimit : (ratio:ℝ) < (upper:ℝ) := by
    have before := Nat.le_ceil (ratio:ℝ)
    dsimp only [upper]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have lowerPositive : 0 < (ratio:ℝ)/2 := by positivity
  have bounds : ∀ᶠ depth in atTop, (ratio:ℝ)/2 * clocks depth ≤ clocks depth*(ratios depth:ℝ) ∧
      clocks depth*(ratios depth:ℝ) ≤ (upper:ℝ)*clocks depth := by
    filter_upwards [realConvergence.eventually (lt_mem_nhds (by linarith : (ratio:ℝ)/2 < ratio)),
      realConvergence.eventually (gt_mem_nhds upperLimit)] with depth lowerBound upperBound
    have first := mul_le_mul_of_nonneg_right lowerBound.le (clocksPositive depth).le
    have second := mul_le_mul_of_nonneg_right upperBound.le (clocksPositive depth).le
    constructor <;> nlinarith
  have newDiverges : Tendsto (fun depth => clocks depth*(ratios depth:ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (bounds.mono fun _ bound => bound.1) (diverge.const_mul_atTop lowerPositive)
  let newClocks := fun depth => clocks depth * (ratios depth : ℝ)
  have newClocksPositive (depth : ℕ) : 0 < newClocks depth :=
    mul_pos (clocksPositive depth) (NNReal.coe_pos.mpr (ratiosPositive depth))
  let chainLaws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  have newCentered := centered_clock_change_probability_completion20261011 vertices chainLaws weights
    clocks newClocks (upper:ℝ) ((ratio:ℝ)/2)
    (by exact_mod_cast upperPositive) lowerPositive bounds centered
  have newModulus := chain_modulus_clock_change_completion20261011 vertices chainLaws placement clocks newClocks
    (fun depth => (clocksPositive depth).le) upper upperPositive (bounds.mono (fun _ bound => bound.2)) modulus
  have discreteWeak := actual_discrete_rescaled_countable_weak rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound initial ratios ratiosPositive
    ratio ratioPositive ratioConvergence times dense limitLaw weak futureTimes
  let laws := fun depth => finiteContinuousWalkSampleLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let samples := fun depth (outcome : (ℕ → vertices depth) × (ℕ → ℝ)) (time : ℝ≥0) =>
    placement depth (holdingTimePath outcome.1 (weightedHoldingSampleCompletion20261011 (weights depth) outcome).2
      (newClocks depth * (time : ℝ)))
  let approximations := fun depth (outcome : (ℕ → vertices depth) × (ℕ → ℝ)) (time : ℝ≥0) =>
    placement depth (outcome.1 ⌊newClocks depth * (time : ℝ)⌋₊)
  have samplesMeasurable (depth : ℕ) (time : ℝ≥0) : Measurable (fun outcome => samples depth outcome time) :=
    (measurable_of_finite (placement depth)).comp
      ((holdingTimePath_measurable (newClocks depth * (time : ℝ))).comp
        (weightedHoldingSample_measurable_completion20261011 (weights depth)))
  have approximationsMeasurable (depth : ℕ) (time : ℝ≥0) : Measurable (fun outcome => approximations depth outcome time) :=
    (measurable_of_finite (placement depth)).comp ((measurable_pi_apply _).comp measurable_fst)
  have approximationIdentity (depth : ℕ) :
      ProbabilityMeasure.map (⟨laws depth, inferInstance⟩ : ProbabilityMeasure ((ℕ → vertices depth) × (ℕ → ℝ)))
        ((measurable_pi_lambda _ (fun coordinate => approximationsMeasurable depth (futureTimes coordinate))).aemeasurable) =
      actualDiscreteRescaledCountableObservationLaw rule p positive belowOne fixedPoint growth value growthPositive
        marks chemicalScale chemicalScalePositive ratios futureTimes depth (initial depth) := by
    apply Subtype.ext
    let observed : (ℕ → vertices depth) → (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint
        growth value growthPositive ⟨marks.val, marks.property.1.1⟩) :=
      fun trajectory coordinate => placement depth (trajectory ⌊newClocks depth * (futureTimes coordinate : ℝ)⌋₊)
    have observedMeasurable : Measurable observed :=
      measurable_pi_lambda _ (fun coordinate => (measurable_of_finite (placement depth)).comp (measurable_pi_apply _))
    change ((chainLaws depth).prod exponentialHoldingTimeLaw).map (observed ∘ Prod.fst) = (chainLaws depth).map observed
    rw [← Measure.map_map observedMeasurable measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have approximationWeak := discreteWeak.congr' (Eventually.of_forall (fun depth => (approximationIdentity depth).symm))
  have coupling : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∀ᶠ depth in atTop, ∃ bad : Set ((ℕ → vertices depth) × (ℕ → ℝ)), MeasurableSet bad ∧ (laws depth).real bad ≤ error ∧
        ∀ outcome, outcome ∉ bad → ∀ time : ℝ≥0, (time : ℝ) ≤ horizon →
          dist (samples depth outcome time) (approximations depth outcome time) ≤ tolerance := by
    intro horizon tolerance error tolerancePositive errorPositive
    have coupled := weightedClock_uniform_coupling_probability_completion20261011 vertices
      (fun depth => (⟨chainLaws depth, inferInstance⟩ : ProbabilityMeasure (ℕ → vertices depth)))
      placement weights weightPositive (max bound 1) (le_max_of_le_left boundNonnegative) weightBound
      newClocks newClocksPositive newDiverges newCentered newModulus horizon tolerance error tolerancePositive errorPositive
    filter_upwards [coupled] with depth near
    obtain ⟨bad, measurableBad, probabilityBad, close⟩ := near
    exact ⟨bad, measurableBad, probabilityBad, fun outcome outside time before => close outcome outside time time.property before⟩
  have result := countableObservation_weak_of_compact_uniform_coupling
    (fun depth => (ℕ → vertices depth) × (ℕ → ℝ)) laws futureTimes samples approximations samplesMeasurable approximationsMeasurable
    (limitLaw.map ((measurable_pi_lambda _ (fun coordinate =>
      countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense
        (ratio * futureTimes coordinate))).aemeasurable)) approximationWeak coupling
  convert result using 1
  funext depth
  apply Subtype.ext
  rfl

end
end IGSIII34.Diffusion
