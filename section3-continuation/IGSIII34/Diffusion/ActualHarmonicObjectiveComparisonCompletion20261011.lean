import IGSIII34.Diffusion.ActualOriginalObjectivePassageCompletion20261011
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

local instance harmonicObjectiveCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance harmonicObjectiveCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

/-- Every actual finite-resolvent subsequential limit is compared with the
true harmonic function of every finite trace. Its recovery is constructed,
rather than postulated as an arbitrary limiting test. -/
theorem actualOriginalResolvent_compares_harmonic_completion20261011
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
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (forcing : C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩, ℝ))
    (candidate : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (selected : ℕ → ℕ) (selectedAtTop : Tendsto selected atTop atTop)
    (limitEnergy : ℝ)
    (energyLimit : Tendsto (fun index => sourceComponentEnergy
      (network (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)))
      (fun _ => (growth ^ (selected index + 1))⁻¹)
      (actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive parameter parameterPositive
        (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
          ⟨marks.val, marks.property.1.1⟩ depth vertex)) (selected index))) atTop (𝓝 limitEnergy))
    (candidateEnergyBound : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val ≤ limitEnergy)
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
            chemicalScale chemicalScalePositive parameter parameterPositive
            (fun depth vertex => forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ depth vertex)) (selected index) vertex.val -
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate
            (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
              ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance)
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ) :
    parameter * (∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate point ^ 2 ∂(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) +
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)) candidate.val -
      2 * (∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate point ∂(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) ≤
    parameter * (∫ point, IGSIII34.Spectral.actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks coarse boundary point ^ 2 ∂(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) +
      sourceComponentEnergy (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse))
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val coarse) boundary -
      2 * (∫ point, forcing point * IGSIII34.Spectral.actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks coarse boundary point ∂(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))) := by
  let forcingFamily := fun depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) =>
    forcing (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)
  let potentials := actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily
  have candidateLimit := actualOriginalDegreeObjective_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure degreeLimit selected selectedAtTop potentials
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) candidate) forcing uniform parameter limitEnergy energyLimit
  obtain ⟨recovery, _, _, recoveryEnergy, recoveryUniform⟩ := exists_actualOriginal_uniform_trace_recovery_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks stationary fieldLimit eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBound coarse boundary
  have recoveryUniformSelected : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ vertex : RetainedSkeletonVertex (rule.generation (selected index)).network (stationaryConfiguration rule marks.val (selected index)),
        |recovery (selected index) vertex.val - IGSIII34.Spectral.actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
          marks coarse boundary (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
            ⟨marks.val, marks.property.1.1⟩ (selected index) vertex)| < tolerance :=
    fun tolerance positive => selectedAtTop.eventually (recoveryUniform tolerance positive)
  have recoveryLimit := actualOriginalDegreeObjective_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive measure degreeLimit selected selectedAtTop recovery
    (IGSIII34.Spectral.actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary)
    forcing recoveryUniformSelected parameter _ (recoveryEnergy.comp selectedAtTop)
  have comparison := le_of_tendsto_of_tendsto candidateLimit recoveryLimit (Eventually.of_forall fun index =>
    actualOriginalPaperClockResolvent_minimizes_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily (selected index) (recovery (selected index)))
  exact (sub_le_sub_right (add_le_add le_rfl candidateEnergyBound) _).trans comparison

end
end IGSIII34.Diffusion



