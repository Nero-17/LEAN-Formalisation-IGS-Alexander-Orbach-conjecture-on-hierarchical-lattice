import IGSIII34.Diffusion.ActualVertexResolventWholePointwiseCompletion20261011
import IGSIII34.Diffusion.ActualPrescribedLimitEnergyCompletion20261011
import IGSIII34.Diffusion.UniqueSkeletonLimitCompletion20261011
import IGSIII34.Diffusion.ActualHarmonicObjectiveUniquenessCompletion20261011
import IGSIII34.Diffusion.ActualConstructedRecoveryCompletion20261011
import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion20261011
import IGSIII34.Diffusion.ActualElectricalCountingMeasureCompletion20261011

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

local instance vertexCopyresolventUniformCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance vertexCopyresolventUniformCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
  (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

local instance vertexCopyActualResolventUniformCompletion20261011Compact : CompactSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := by
  change CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  infer_instance
local instance vertexCopyActualResolventUniformCompletion20261011Measurable : MeasurableSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := borel _
local instance vertexCopyActualResolventUniformCompletion20261011Borel : BorelSpace
    (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))) := ⟨rfl⟩

open IGSIII34.Spectral
local instance vertexCopyactualResolventUniformNormCompletion20261011 : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance vertexCopyactualResolventUniformUniformCompletion20261011 : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (vertexCopyactualResolventUniformNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance vertexCopyactualResolventUniformTopologyCompletion20261011 : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (vertexCopyactualResolventUniformNormCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance vertexCopyactualResolventUniformInnerCompletion20261011 : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance vertexCopyactualResolventUniformCompleteCompletion20261011 : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


theorem actualOriginalVertexResolvent_uniform_completion20261011
    (countingLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalCountingMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
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
    : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth),
        |actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
            chemicalScale chemicalScalePositive parameter parameterPositive
            (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ depth vertex)) depth vertex.val -
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
            (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
              (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
              (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
              parameter parameterAtLeastOne forcing)
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ depth vertex)| < tolerance := by
  let forcingFamily := fun depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) =>
    forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
  let potentials := actualOriginalVertexClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily
  let solution := actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
    (measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    parameter parameterAtLeastOne forcing
  have forcingBound (depth : ℕ) (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) :
      |forcingFamily depth vertex| ≤ ‖forcing‖ := by
    simpa only [Real.norm_eq_abs] using forcing.norm_coe_le_norm
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
  have energyBound := actualOriginalVertexClockResolvent_energy_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily ‖forcing‖ (norm_nonneg _) forcingBound
  have pointwise := actualOriginalVertexResolvent_pointwise_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive measure anchor countingLimit stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative
    radiusBound parameter parameterAtLeastOne parameterPositive forcing
  exact actualOriginal_selected_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials (‖forcing‖ ^ 2 / parameter)
    (by positivity) energyBound solution id tendsto_id pointwise

end
end IGSIII34.Diffusion


