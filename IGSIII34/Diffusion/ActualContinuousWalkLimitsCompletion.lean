import IGSIII34.Diffusion.ActualElectricalPathTightnessCompletion
import IGSIII34.Diffusion.ActualCutoffResolventApproximationCompletion
import IGSIII34.Diffusion.ActualWalkSmallJumpsCompletion
import IGSIII34.Diffusion.ResolventCutoffTightnessCompletion
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

local instance continuousPathCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance continuousPathCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualContinuousPathCompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualContinuousPathCompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualContinuousPathCompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualContinuousPathNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualContinuousPathCutoffApproximationCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualContinuousPathNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualContinuousPathTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualContinuousPathNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualContinuousPathInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualContinuousPathCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
theorem actual_discrete_weak_limit_continuous_paths_completion
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
    (limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩))
    (selected : ℕ → ℕ) (selectedDiverges : Tendsto selected atTop atTop)
    (convergence : Tendsto (fun index => actualPaperDiscreteElectricalObservationLawCompletion rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected index))
      atTop (𝓝 limitLaw)) :
    (∀ᵐ sample ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)), countableTimeLocalUniformContinuityCompletion times sample) ∧
      Measurable (fun pair : ℝ≥0 × (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩) => countableTimeContinuousSampleCompletion times dense pair.2 pair.1) ∧
      (∀ sample : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩,
        Continuous (countableTimeContinuousSampleCompletion times dense sample)) ∧
      (∀ᵐ sample ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)), ∀ coordinate,
        countableTimeContinuousSampleCompletion times dense sample (times coordinate) = sample coordinate) ∧
      (∀ (count : ℕ) (coordinates : Fin count → ℕ),
        (countableContinuousProcessProbabilityLawCompletion times dense limitLaw : Measure (ℝ≥0 → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map
          (fun path => fun index : Fin count => path (times (coordinates index))) =
            (limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).map (fun path => fun index : Fin count => path (coordinates index))) := by
  have bounds : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        (actualPaperDiscreteElectricalObservationLawCompletion rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive times initial (selected index) : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).real
          (countableTimeBadModulusCompletion times horizon duration tolerance) ≤ error := by
    intro horizon tolerance error tolerancePositive errorPositive
    obtain ⟨duration, durationPositive, probability⟩ := actual_discrete_countable_modulus_probability_completion rule p positive belowOne
      fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne degreeLimit
      stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound
      times initial horizon tolerance error tolerancePositive errorPositive
    exact ⟨duration, durationPositive, selectedDiverges.eventually probability⟩
  have regular := countableTimeWeakLimit_ae_local_uniform_continuity_completion times _ limitLaw convergence bounds
  refine ⟨regular, countableTimeContinuousSample_joint_measurable_completion times dense,
    countableTimeContinuousSample_continuous_completion times dense,
    countableTimeContinuousSample_ae_agreement_completion times dense limitLaw regular, ?_⟩
  intro count coordinates
  exact countableContinuousProcess_observed_finite_marginal_completion times dense limitLaw regular coordinates

end
end IGSIII34.Diffusion




