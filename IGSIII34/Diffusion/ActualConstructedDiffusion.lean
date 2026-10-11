import IGSIII34.Diffusion.ActualStrongMarkovKernelLawCompletion20261011
import IGSIII34.Diffusion.ActualContinuousLimitAssemblyCompletion20261011
import IGSIII34.Diffusion.ActualContinuousGlobalWholeWeakCompletion20261011
import IGSIII34.Diffusion.ActualAeFiniteStoppingMarkovCompletion20261011
import IGSIII34.Diffusion.StrongMarkovKernelLawCompletion20261011

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

local instance actualConstructedDiffusionCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance actualConstructedDiffusionCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualConstructedDiffusionCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualConstructedDiffusionCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualConstructedDiffusionCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral ProbabilityTheory
local instance actualConstructedDiffusionNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualConstructedDiffusionCutoffApproximationCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualConstructedDiffusionNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualConstructedDiffusionTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualConstructedDiffusionNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualConstructedDiffusionInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualConstructedDiffusionCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

include anchor in
/-- The same genuinely constructed limit law has continuous paths, is the
weak global-J1 limit of the original continuous-time walks, and satisfies
its transition-kernel law at every almost-surely finite stopping time.
No process existence, path tightness, path convergence or Markov conclusion
is assumed. The hypotheses are the actual electrical-form and mass inputs. -/
theorem actual_constructed_continuous_diffusion
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
    (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)))
    (initial : ∀ depth, ProbabilityMeasure (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (times : ℕ → ℝ≥0) (timeZero : times 0 = 0) (dense : DenseRange times)
    (initialLimit : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    (initialConvergence : Tendsto (fun depth => (initial depth).map
      (measurable_of_finite (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
        actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)).aemeasurable)
      atTop (𝓝 initialLimit)) :
    ∃ limitLaw : ProbabilityMeasure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩),
      Tendsto (fun depth => actualPaperDiscreteElectricalObservationLawCompletion20261011
        rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩
        chemicalScale chemicalScalePositive times initial depth) atTop (𝓝 limitLaw) ∧
      (∀ᵐ sample ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)), countableTimeLocalUniformContinuityCompletion20261011 times sample) ∧
      (∀ sample : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, Continuous (countableTimeContinuousSampleCompletion20261011 times dense sample)) ∧
      Tendsto (fun depth => actualPaperContinuousElectricalGlobalJ1LawCompletion20261011 rule p positive belowOne fixedPoint
        growth value growthPositive marks chemicalScale chemicalScalePositive initial depth) atTop
        (𝓝 (limitLaw.map (countableSkorokhodGlobalSample_measurable_completion20261011 times dense).aemeasurable)) ∧
      ∀ (time : (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) → WithTop ℝ≥0),
      ∀ stopping : IsStoppingTime
        (Filtration.natural (fun present (path : ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) => countableTimeContinuousSampleCompletion20261011 times dense path present)
          (fun present => (countableTimeContinuousSample_evaluation_measurable_completion20261011 times dense present).stronglyMeasurable)) time,
      (∀ᵐ path ∂(limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)), time path ≠ ⊤) → ∀ future : ℝ≥0,
      ∀ event : Set (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩),
      MeasurableSet[stopping.measurableSpace] event →
      ((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).restrict event).map
        (fun path => countableTimeContinuousSampleCompletion20261011 times dense path ((time path).untopA + future)) =
        (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) data future) ∘ₘ
        (((limitLaw : Measure (ℕ → ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).restrict event).map
          (fun path => countableTimeContinuousSampleCompletion20261011 times dense path (time path).untopA)) := by
  obtain ⟨limitLaw, weak, regular⟩ := actual_discrete_continuous_limit_assembly_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor
    degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound
    growthGreaterThanOne data initial edgePositive times timeZero dense initialLimit initialConvergence
  refine ⟨limitLaw, weak, regular, ?_, ?_, ?_⟩
  · exact countableTimeContinuousSample_continuous_completion20261011 times dense
  · exact actual_continuous_global_skorokhod_convergence_completion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne
      degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound
      times dense initial limitLaw id tendsto_id weak
  · intro time stopping finiteTime future event eventKnown
    exact actual_continuous_process_stopping_kernel_law_completion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks chemicalScale chemicalScalePositive measure anchor edgePositive growthGreaterThanOne
      degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound
      times dense initial limitLaw id tendsto_id weak data time stopping finiteTime future event eventKnown

end
end IGSIII34.Diffusion




