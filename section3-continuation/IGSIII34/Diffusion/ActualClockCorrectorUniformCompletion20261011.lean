import IGSIII34.Diffusion.ActualClockCorrectorZeroCompletion20261011

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

local instance clockCorrectorUniformCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance clockCorrectorUniformCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable [CompactSpace (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)]
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (measure : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))

variable [(measure : Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)).IsOpenPosMeasure]

theorem actual_clock_corrector_uniform_zero_completion20261011
    (degreeLimit : Tendsto (fun depth => levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ chemicalScale chemicalScalePositive depth) (measure : Measure _)) atTop (𝓝 0))
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
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ depth vertex,
      |actualCountingClockCenteredForcingCompletion20261011 rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth vertex| ≤ bound) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth,
        |actualPaperClockGraphResolventCompletion20261011 rule (stationaryConfiguration rule marks.val)
          (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
          chemicalScale chemicalScalePositive depth growth growthPositive parameter parameterPositive
          (actualCountingClockCenteredForcingCompletion20261011 rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth) vertex| < tolerance := by
  let forcingFamily := actualCountingClockCenteredForcingCompletion20261011 rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive
  let potentials := actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily
  have voltageBound := actualOriginalPaperClockResolvent_voltage_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily bound boundNonnegative forcingBound
  have energyBound := actualOriginalPaperClockResolvent_energy_bound_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily bound boundNonnegative forcingBound
  letI := countable_actualEnergySkeleton_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
  have pointwise : ∀ point, Tendsto
      (fun depth => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials depth point)
      atTop (𝓝 (0 : ℝ)) := by
    apply bounded_countable_unique_limit_tendsto_completion20261011
      (actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks potentials)
      (bound / parameter)
      (actualMicroscopicHarmonicLift_bounded_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks stationary potentials (bound / parameter) (fun depth vertex _ => voltageBound depth vertex)) (fun _ => 0)
    intro outer outerStrict limitPotential limitPointwise
    obtain ⟨inner, innerStrict, limitEnergy, _, candidate, candidateValue, energyLower, energyConvergence⟩ :=
      actualOriginal_prescribed_limit_energy_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        fieldLimit potentials (bound ^ 2 / parameter) energyBound outer outerStrict limitPotential limitPointwise
    have finitePointwise : ∀ point, Tendsto (fun index => actualMicroscopicHarmonicLiftCompletion20261011 rule p positive belowOne fixedPoint growth value
        growthPositive marks potentials (outer (inner index)) point) atTop (𝓝 (candidate.val point)) := by
      intro point
      simpa only [candidateValue, Function.comp_def] using (limitPointwise point).comp innerStrict.tendsto_atTop
    have uniform := actualOriginal_selected_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials (bound ^ 2 / parameter)
      (by positivity) energyBound candidate (outer ∘ inner) (outerStrict.comp innerStrict).tendsto_atTop finitePointwise
    have identified := actual_clock_corrector_subsequence_zero_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      chemicalScale chemicalScalePositive measure degreeLimit countingLimit parameter parameterPositive candidate
      (outer ∘ inner) (outerStrict.comp innerStrict).tendsto_atTop uniform
    exact candidateValue.symm.trans (congrArg Subtype.val identified)
  have uniform := actualOriginal_selected_uniform_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    fieldLimit eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBound potentials (bound ^ 2 / parameter)
    (by positivity) energyBound 0 id tendsto_id pointwise
  intro tolerance tolerancePositive
  filter_upwards [uniform tolerance tolerancePositive] with depth close
  intro vertex
  have current := close vertex
  simp only [map_zero, ContinuousMap.zero_apply, sub_zero] at current
  have restricted := retainedPotentialExtension_retained_completion20261011 (rule.generation depth).network (stationaryConfiguration rule marks.val depth)
    (actualPaperClockGraphResolventCompletion20261011 rule (stationaryConfiguration rule marks.val)
      (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.1.1.2.1 depth [] true)
      chemicalScale chemicalScalePositive depth growth growthPositive parameter parameterPositive (forcingFamily depth)) vertex
  change |actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily depth vertex.val| < tolerance at current
  rw [show actualOriginalPaperClockResolventPotentialCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    chemicalScale chemicalScalePositive parameter parameterPositive forcingFamily depth vertex.val = _ from restricted] at current
  exact current

end
end IGSIII34.Diffusion
