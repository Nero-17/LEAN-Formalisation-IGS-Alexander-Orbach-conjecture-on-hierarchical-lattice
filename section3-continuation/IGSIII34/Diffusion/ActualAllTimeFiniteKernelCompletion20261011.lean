import IGSIII34.Diffusion.ActualReobservedWalkWeakCompletion20261011
import IGSIII34.Diffusion.ActualObservedKernelCompletion20261011
import IGSIII34.Diffusion.DenseObservationReobserveCompletion20261011
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

local instance actualAllTimeKernelCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualAllTimeKernelCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualAllTimeKernelCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualAllTimeKernelCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualAllTimeKernelCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance actualAllTimeKernelNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualAllTimeKernelCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualAllTimeKernelNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualAllTimeKernelTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualAllTimeKernelNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualAllTimeKernelInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualAllTimeKernelCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
/-- The actual continuous process has the true constructed transition
kernel at arbitrary finite collections of real times. It is obtained
from the original walk, not postulated as a Markov process. -/
theorem actual_all_time_finite_conditional_transition_completion20261011
    (edgePositive : 0 < rule.edges) (growthGreaterThanOne : 1 < growth)
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
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
    (weak : Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected depth)) atTop (𝓝 limitLaw))
    (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (futureTimes : ℕ → ℝ≥0)
    {count : ℕ} (pastCoordinates : Fin count → ℕ) (present : Fin count) (futureCoordinate : ℕ)
    (before : ∀ coordinate, futureTimes (pastCoordinates coordinate) ≤ futureTimes (pastCoordinates present))
    (ordered : futureTimes (pastCoordinates present) ≤ futureTimes futureCoordinate) :
    letI : Nonempty (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) :=
      nonempty_of_isProbabilityMeasure (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    condDistrib (fun path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ =>
        countableTimeContinuousSampleCompletion20261011 times dense path (futureTimes futureCoordinate))
      (fun path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ =>
        fun coordinate : Fin count => countableTimeContinuousSampleCompletion20261011 times dense path (futureTimes (pastCoordinates coordinate)))
      (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) =ᵐ[(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map
        (fun path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ =>
          fun coordinate : Fin count => countableTimeContinuousSampleCompletion20261011 times dense path (futureTimes (pastCoordinates coordinate)))]
      (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data
          (futureTimes futureCoordinate - futureTimes (pastCoordinates present))).comap
            (fun history => history present) (measurable_pi_apply present) := by
  letI : Nonempty (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) :=
    nonempty_of_isProbabilityMeasure (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
  let reobserve := countableReobservedContinuousSampleCompletion20261011
    (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    times dense futureTimes
  have reobserveMeasurable : Measurable reobserve :=
    countableReobservedContinuousSample_measurable_completion20261011 (Space := ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) times dense futureTimes
  let newLaw := limitLaw.map reobserveMeasurable.aemeasurable
  have newWeakActual := actual_reobserved_walk_weak_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit stationary fieldLimit
    eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound times dense initial limitLaw selected selectedAtTop weak futureTimes
  have newWeakGeneric := newWeakActual.congr' (Eventually.of_forall (fun depth =>
    actualPaperDiscreteObservation_eq_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive futureTimes initial (selected depth)))
  have kernel := actual_walk_limit_conditional_transition_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure anchor degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBound growthGreaterThanOne data initial futureTimes selected selectedAtTop newLaw newWeakGeneric
    pastCoordinates present futureCoordinate before ordered
    (actualCompletionEnergyDomain_dense rule p positive belowOne fixedPoint growth value growthPositive marks)
  let history : (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) → Fin count →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ :=
    fun path coordinate => path (pastCoordinates coordinate)
  have historyMeasurable : Measurable history := by fun_prop
  have historyMap : (newLaw : Measure _).map history = (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map (history ∘ reobserve) := by
    change ((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map reobserve).map history = _
    rw [Measure.map_map historyMeasurable reobserveMeasurable]
  change condDistrib (fun path => path futureCoordinate) history (newLaw : Measure _) =ᵐ[(newLaw : Measure _).map history] _ at kernel
  rw [historyMap] at kernel
  have pullback := condDistrib_map (ν := (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (X := history) (Y := fun path => path futureCoordinate) (f := reobserve)
    historyMeasurable.aemeasurable (measurable_pi_apply futureCoordinate).aemeasurable reobserveMeasurable.aemeasurable
  exact pullback.symm.trans kernel

end
end IGSIII34.Diffusion

