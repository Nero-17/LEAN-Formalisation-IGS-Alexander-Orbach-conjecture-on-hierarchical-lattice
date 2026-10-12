import IGSIII34.Diffusion.DiscreteSkorokhodWeakConvergenceCompletion
import IGSIII34.Diffusion.DenseObservationFiniteTimesCompletion
import IGSIII34.Diffusion.ScaledContinuousIntervalSampleCompletion
import IGSIII34.Diffusion.ActualIntervalFloorModulusCompletion
import IGSIII34.Diffusion.ActualContinuousWalkLimitsCompletion
import IGSIII34.Diffusion.ActualDiscreteObservationCompatibilityCompletion
import IGSIII34.Diffusion.ActualElectricalChainModulusCompletion
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion
import IGSIII34.Diffusion.ActualCutoffResolventApproximationCompletion
import IGSIII34.Diffusion.ActualWalkSmallJumpsCompletion
import IGSIII34.Diffusion.ResolventChainTightnessCompletion
import IGSIII34.Diffusion.CountableProcessJointMeasurabilityCompletion
import IGSIII34.Diffusion.CompactPlateauCoverCompletion
import IGSIII34.Diffusion.ActualScaledContinuousResolventCompletion
import IGSIII34.Diffusion.ActualPaperClockGrowthCompletion
import IGSIII34.Diffusion.ActualWholeContinuousResolventCompletion
import IGSIII34.Forms.ActualRegularityCompletion
import IGSIII34.Diffusion.ActualResolventWholePointwiseCompletion
import IGSIII34.Diffusion.ActualPrescribedLimitEnergyCompletion
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion
import IGSIII34.Diffusion.ActualHarmonicObjectiveUniquenessCompletion
import IGSIII34.Diffusion.ActualConstructedRecoveryCompletion
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion
import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion

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

local instance actualJ1CarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualJ1CarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualJ1CompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualJ1CompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualJ1CompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualJ1NormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualJ1CutoffApproximationCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualJ1NormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualJ1TopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualJ1NormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualJ1InnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualJ1CompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
/-- The original full-cluster walk with the exact manuscript clock
converges in the genuine interval J1 topology along every countable
observation weak subsequence. The limit is the constructed continuous
process, and no finite-dimensional, path tightness, or J1 convergence
hypothesis is inserted. -/
theorem actual_discrete_skorokhod_convergence_completion
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
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
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected depth)) atTop (𝓝 limitLaw))
    (horizon : ℕ) :
    Tendsto (fun depth => discreteIntervalSkorokhodProbabilityCompletion
      (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth))
      (clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth)))
      (cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true))
      (initial (selected depth))
      (actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩ (selected depth))
      (actualPaperDiscreteClock_positive_completion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ (selected depth)).le horizon
      (fun vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex)) atTop
      (𝓝 (limitLaw.map (countableScaledSkorokhodIntervalSample_measurable_completion times dense horizon).aemeasurable)) := by
  let vertices := fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (selected depth)
  let edges := fun depth => ClusterEdge (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth))
  let endpoint : ∀ depth, edges depth → vertices depth × vertices depth := fun depth =>
    clusterRetainedEndpoint (rule.generation (selected depth)).network (stationaryConfiguration rule marks.val (selected depth))
  let positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex := fun depth =>
    cluster_degree_positive _ _ (markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 (selected depth) [] true)
  let clocks := fun depth => actualPaperDiscreteClockCompletion rule p positive belowOne fixedPoint growth value
    ⟨marks.val, marks.property.1.1⟩ (selected depth)
  let placement := fun depth (vertex : vertices depth) => actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    ⟨marks.val, marks.property.1.1⟩ (selected depth) vertex
  have clocksNonnegative (depth : ℕ) : 0 ≤ clocks depth :=
    (actualPaperDiscreteClock_positive_completion rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ (selected depth)).le
  have weakGeneric : Tendsto (fun depth => discreteRescaledObservationLawCompletion (endpoint depth) (positiveDegree depth)
      (initial (selected depth)) (clocks depth) times (placement depth)) atTop (𝓝 limitLaw) := by
    apply weak.congr'
    apply Eventually.of_forall
    intro depth
    exact actualPaperDiscreteObservation_eq_completion rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected depth)
  have regular := (actual_discrete_weak_limit_continuous_paths_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw selected selectedAtTop weak).1
  have chainModulus (bound : ℕ) (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial (selected depth))).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (clocks depth) bound duration tolerance) ≤ error := by
    obtain ⟨duration, durationPositive, probabilities⟩ := actual_floor_interval_modulus_probability_completion
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
      edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBound initial bound tolerance error tolerancePositive errorPositive
    exact ⟨duration, durationPositive, selectedAtTop.eventually probabilities⟩
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion,
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion,
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩
  apply discreteSkorokhod_weak_of_finite_marginals_and_chain_modulus_completion vertices edges endpoint positiveDegree
    (fun depth => initial (selected depth)) clocks clocksNonnegative horizon placement (limitLaw : Measure _)
    (countableScaledContinuousIntervalSampleCompletion times dense horizon)
    (countableScaledContinuousIntervalSample_measurable_completion times dense horizon)
  · intro grid
    let futureTimes : Fin (grid + 2) → ℝ≥0 := fun index =>
      ⟨(horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index).val,
        mul_nonneg (Nat.cast_nonneg horizon)
          (skorokhodRegularGridPointCompletion grid index).property.1⟩
    have futureTimeValue (index : Fin (grid + 2)) : (futureTimes index : ℝ) =
        (horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index).val := by rfl
    have within (index : Fin (grid + 2)) : (futureTimes index : ℝ) + 1 ≤ (horizon + 1 : ℕ) := by
      have bound := mul_le_mul_of_nonneg_left (skorokhodRegularGridPointCompletion grid index).property.2
        (Nat.cast_nonneg horizon : (0 : ℝ) ≤ horizon)
      rw [futureTimeValue, Nat.cast_add, Nat.cast_one]
      have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
      rw [realLE] at bound
      exact add_le_add (by simpa only [mul_one] using bound) le_rfl
    have marginal := finiteFlooredTimeLaw_weak_of_dense_observations_completion vertices edges endpoint positiveDegree
      (fun depth => initial (selected depth)) clocks clocksNonnegative placement times dense limitLaw weakGeneric regular
      futureTimes (horizon + 1) within (chainModulus (horizon + 1))
    convert marginal using 1
    · funext depth
      apply Subtype.ext
      apply Measure.map_congr
      apply Eventually.of_forall
      intro path
      funext index
      dsimp only [finiteFlooredTimeSampleCompletion]
      rw [futureTimeValue, NNReal.coe_natCast, mul_assoc]
    · apply congrArg (fun probability : ProbabilityMeasure (Fin (grid + 2) →
          ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) => 𝓝 probability)
      apply Subtype.ext
      apply Measure.map_congr
      apply Eventually.of_forall
      intro path
      funext index
      rfl
  · exact chainModulus horizon

end
end IGSIII34.Diffusion


