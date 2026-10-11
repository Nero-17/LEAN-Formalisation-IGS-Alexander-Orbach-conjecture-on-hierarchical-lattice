import IGSIII34.Diffusion.ActualResolventLimitIdentificationCompletion20261011
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
open scoped _root_.Topology BigOperators

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

local instance resolventWholeCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance resolventWholeCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance ActualResolventWholePointwiseCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance ActualResolventWholePointwiseCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance ActualResolventWholePointwiseCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance actualResolventWholeNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualResolventWholeUniformCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualResolventWholeNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualResolventWholeTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualResolventWholeNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualResolventWholeInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualResolventWholeCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


theorem actualOriginalResolvent_pointwise_completion20261011
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
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (parameterPositive : 0 < parameter)
    (forcing : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, ℝ))
    : ∀ point, Tendsto
      (fun depth => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        (actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
          chemicalScale chemicalScalePositive parameter parameterPositive
          (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val, marks.property.1.1⟩ depth vertex))) depth point) atTop
      (𝓝 ((actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
        (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
        parameter parameterAtLeastOne forcing).val point)) := by
  let forcingFamily := fun depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) =>
    forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
  let potentials := actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily
  let solution := actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
    (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    parameter parameterAtLeastOne forcing
  have forcingBound (depth : ℕ) (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :
      |forcingFamily depth vertex| ≤ ‖forcing‖ := by
    simpa only [Real.norm_eq_abs] using forcing.norm_coe_le_norm
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
  have voltageBound := actualOriginalPaperClockResolvent_voltage_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily ‖forcing‖ (norm_nonneg _) forcingBound
  have energyBound := actualOriginalPaperClockResolvent_energy_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily ‖forcing‖ (norm_nonneg _) forcingBound
  letI := countable_actualEnergySkeleton_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  apply bounded_countable_unique_limit_tendsto_completion20261011
    (actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
    (‖forcing‖ / parameter)
    (actualMicroscopicHarmonicLift_bounded_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary potentials (‖forcing‖ / parameter) (fun depth vertex _ => voltageBound depth vertex)) solution.val
  intro outer outerStrict limitPotential pointwise
  obtain ⟨inner, innerStrict, limitEnergy, _, candidate, candidateValue, energyLower, energyConvergence⟩ :=
    actualOriginal_prescribed_limit_energy_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      fieldLimit potentials (‖forcing‖ ^ 2 / parameter) energyBound outer outerStrict limitPotential pointwise
  have finitePointwise : ∀ point, Tendsto (fun index => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive marks potentials (outer (inner index)) point) atTop (𝓝 (candidate.val point)) := by
    intro point
    simpa only [candidateValue, Function.comp_def] using (pointwise point).comp innerStrict.tendsto_atTop
  have uniform := actualOriginal_selected_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials (‖forcing‖ ^ 2 / parameter)
    (by positivity) energyBound candidate (outer ∘ inner) (outerStrict.comp innerStrict).tendsto_atTop finitePointwise
  have identified := actualOriginalResolvent_limit_identification_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive measure anchor degreeLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative
    radiusBound parameter parameterAtLeastOne parameterPositive forcing candidate (outer ∘ inner) (outerStrict.comp innerStrict).tendsto_atTop
    limitEnergy energyConvergence energyLower uniform
  exact candidateValue.symm.trans (congrArg Subtype.val identified)

end
end IGSIII34.Diffusion


