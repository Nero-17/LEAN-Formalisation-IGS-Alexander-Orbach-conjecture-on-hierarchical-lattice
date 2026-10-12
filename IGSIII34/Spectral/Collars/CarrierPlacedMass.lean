import IGSIII34.Spectral.Collars.CarrierWordPoint
import IGSIII34.Spectral.Collars.MeasureTransport
import IGSIII34.ResistanceLimit.CommonChemicalMeasureTransfer
import IGSIII.Geometry.ActualFiniteMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII34.ResistanceLimit IGSIII34.Percolation MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (classicalRule : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
  (growth : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

local instance carrierPlacedElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance carrierPlacedElectricalBorel : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := ⟨rfl⟩

variable (homeomorph : (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks.val depth [] true)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) ≃ₜ
  (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
  (inverseBirth : ∀ depth (vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth),
    homeomorph.symm (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
      ⟨marks.val, marks.property.1.1⟩ depth vertex) =
    actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)

include inverseBirth in
theorem actual_same_carrier_placed_mass
    {Ambient : Type*} [MetricSpace Ambient] [TopologicalSpace.SeparableSpace Ambient]
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (realizationMeasurable : Measurable realization)
    (measures : ∀ depth, ProbabilityMeasure
      (ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth))
    (bornProjectionLP : Tendsto (fun depth => levyProkhorovEDist
      ((measures depth : Measure _).map
        (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
          actualStationaryElectricalVertex rule p positive belowOne fixedPoint
        growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex))
      (boundary.map realization)) atTop (𝓝 0))
    (target : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks.val depth [] true)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → Ambient)
    (targetContinuous : Continuous target)
    (placements : ∀ depth, ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
      chemicalScale chemicalScalePositive depth → Ambient)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (placements depth vertex) (target (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth vertex)) < tolerance) :
    Tendsto (fun depth => (measures depth).map (measurable_of_finite (placements depth)).aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map (⟨boundary.map realization, Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable⟩ : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
        (targetContinuous.comp homeomorph.symm.continuous).measurable.aemeasurable)) ∧
    Tendsto (fun depth => levyProkhorovEDist ((measures depth : Measure _).map (placements depth))
      ((boundary.map realization).map (target ∘ homeomorph.symm))) atTop (𝓝 0) := by
  have projectionMeasurable : ∀ depth, Measurable (fun vertex : ActualFiniteCluster rule
      (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩ depth vertex) := fun _ => measurable_of_finite _
  have projectedWeak := IGSIII34.Diffusion.probability_weak_of_levyProkhorov_completion
    (fun depth => (measures depth).map (projectionMeasurable depth).aemeasurable)
    (⟨boundary.map realization, Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable⟩ : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)) bornProjectionLP
  have close : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (placements depth vertex)
        ((target ∘ homeomorph.symm) (actualStationaryElectricalVertex rule p positive belowOne fixedPoint
          growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex)) < tolerance := by
    intro tolerance tolerancePositive
    filter_upwards [placementClose tolerance tolerancePositive] with depth near
    intro vertex
    simpa only [Function.comp_apply, inverseBirth] using near vertex
  have placedWeak := common_chemical_measure_transfer
    (fun depth => ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth)
    measures (fun depth vertex => actualStationaryElectricalVertex rule p positive belowOne fixedPoint
      growth value growthPositive ⟨marks.val, marks.property.1.1⟩ depth vertex) projectionMeasurable
    placements (fun depth => measurable_of_finite (placements depth)) (target ∘ homeomorph.symm)
    (targetContinuous.comp homeomorph.symm.continuous)
    (⟨boundary.map realization, Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable⟩ : ProbabilityMeasure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩))
    projectedWeak close
  exact ⟨placedWeak, probability_levyProkhorov_of_weak _ _ placedWeak⟩

end
end IGSIII34.Spectral
