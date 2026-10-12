import IGSIII34.Diffusion.ActualHarmonicObjectiveComparisonCompletion
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
open scoped _root_.Topology BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance resolventIdentificationCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance resolventIdentificationCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualResolventLimitIdentificationCompletionCompact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualResolventLimitIdentificationCompletionMeasurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualResolventLimitIdentificationCompletionBorel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualResolventIdentificationNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualResolventIdentificationUniformCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualResolventIdentificationNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualResolventIdentificationTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualResolventIdentificationNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualResolventIdentificationInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualResolventIdentificationCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


theorem actualOriginalResolvent_limit_identification_completion
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
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (parameterPositive : 0 < parameter)
    (forcing : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, ℝ))
    (candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (limitEnergy : ℝ)
    (energyLimit : Tendsto (fun index => sourceComponentEnergy
      (network (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)))
      (fun _ => (growth ^ (selected index + 1))⁻¹)
      (actualOriginalPaperClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive parameter parameterPositive
        (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ depth vertex)) (selected index))) atTop (𝓝 limitEnergy))
    (candidateEnergyBound : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val ≤ limitEnergy)
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |actualOriginalPaperClockResolventPotentialCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
            chemicalScale chemicalScalePositive parameter parameterPositive
            (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ depth vertex)) (selected index) vertex.val -
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance)
    : candidate = actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
      (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
      parameter parameterAtLeastOne forcing := by
  apply actualContinuousEnergySolution_unique_of_harmonic_comparison_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    anchor (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    parameter parameterAtLeastOne forcing candidate
  intro coarse
  let solution := actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
    (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    parameter parameterAtLeastOne forcing
  let boundary := fun vertex : Fin (rule.generation coarse).vertices => solution.val
    (actualEnergyFiniteVertexCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) coarse vertex)
  have harmonicIdentity : actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks anchor coarse solution =
      ⟨actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary,
        actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary⟩ := by
    rfl
  rw [harmonicIdentity, actualContinuousObjective_integral_completion, actualContinuousObjective_integral_completion,
    actualHarmonicFunction_limiting_energy]
  exact actualOriginalResolvent_compares_harmonic_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive measure degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative
    radiusBound parameter parameterPositive forcing candidate selected selectedAtTop limitEnergy energyLimit candidateEnergyBound uniform coarse boundary

end
end IGSIII34.Diffusion

