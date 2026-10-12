import IGSIII34.Diffusion.ContinuousProcessNaturalMarkovCompletion
import IGSIII34.Diffusion.ActualAllTimeFiniteKernelCompletion
import IGSIII34.Diffusion.ActualReobservedWalkWeakCompletion
import IGSIII34.Diffusion.ActualObservedKernelCompletion
import IGSIII34.Diffusion.DenseObservationReobserveCompletion
import IGSIII34.Diffusion.ActualDiscreteSkorokhodConvergenceCompletion
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

local instance actualNaturalMarkovCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualNaturalMarkovCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualNaturalMarkovCompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualNaturalMarkovCompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualNaturalMarkovCompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance actualNaturalMarkovNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualNaturalMarkovCutoffApproximationCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualNaturalMarkovNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualNaturalMarkovTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualNaturalMarkovNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualNaturalMarkovInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualNaturalMarkovCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
theorem actual_continuous_process_natural_markov_completion
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) atTop (𝓝 0))
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
    (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (present future : ℝ≥0) (ordered : present ≤ future)
    (function : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, ℝ)) :
    (limitLaw : Measure _)[(fun path => function (countableTimeContinuousSampleCompletion times dense path future)) |
      Filtration.natural (fun time path => countableTimeContinuousSampleCompletion times dense path time)
        (fun time => (countableTimeContinuousSample_evaluation_measurable_completion times dense time).stronglyMeasurable) present] =ᵐ[(limitLaw : Measure _)]
      (fun path => ∫ retained, function retained ∂actualTransitionKernelCompletion rule p positive belowOne fixedPoint
        growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
        (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data (future-present) (countableTimeContinuousSampleCompletion times dense path present)) := by
  letI : Nonempty (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) :=
    nonempty_of_isProbabilityMeasure (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
  letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
    change Nonempty (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    infer_instance
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
    (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data (future-present)
  apply continuous_process_natural_markov_of_finite_histories_completion
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (Outcome := ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (countableTimeContinuousSampleCompletion times dense)
    (countableTimeContinuousSample_continuous_completion times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion times dense)
    times dense present future
    (actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data (future-present))
    ?_ function
  intro count
  let futureTimes : ℕ → ℝ≥0
    | 0 => future
    | index+1 => countableDensePastTimeCompletion times present index
  have before (coordinate : Fin (count+1)) :
      futureTimes (coordinate.val+1) ≤ futureTimes ((0 : Fin (count+1)).val+1) :=
    countableDensePastTime_before_completion times present coordinate.val
  have kernel := actual_all_time_finite_conditional_transition_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw selected selectedAtTop weak data
    futureTimes (fun coordinate : Fin (count+1) => coordinate.val+1) (0 : Fin (count+1)) 0 before ordered
  exact kernel

end
end IGSIII34.Diffusion

