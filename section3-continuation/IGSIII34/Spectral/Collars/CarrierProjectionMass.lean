import IGSIII34.Spectral.Collars.CarrierWordPoint
import IGSIII34.Spectral.Collars.MeasureTransport

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

local instance carrierProjectionElectricalMeasurable : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩) := borel _
local instance carrierProjectionElectricalBorel : BorelSpace
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
theorem actual_inverse_carrier_boundary_projection_mass
    [TopologicalSpace.SeparableSpace (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks.val depth [] true)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))) [IsProbabilityMeasure boundary]
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (realizationMeasurable : Measurable realization)
    (projection : Tendsto (fun depth => levyProkhorovEDist
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1)))) (boundary.map realization)) atTop (𝓝 0)) :
    Tendsto (fun depth => levyProkhorovEDist
      (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth (path (depth + 1))))
      (boundary.map (homeomorph.symm ∘ realization))) atTop (𝓝 0) := by
  have pointMeasurable : ∀ depth, Measurable (fun path : Π age, Fin age → (Fin rule.edges × Bool) =>
      actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1))) := by
    intro depth
    have coordinate : Measurable (fun path : Π age, Fin age → (Fin rule.edges × Bool) => path (depth + 1)) :=
      measurable_pi_apply (depth + 1)
    exact (measurable_of_finite (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint
      growth value growthPositive marks.val marks.property.1.1 depth)).comp coordinate
  haveI : ∀ depth, IsProbabilityMeasure (boundary.map (fun path =>
      actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1)))) :=
    fun depth => Measure.isProbabilityMeasure_map (pointMeasurable depth).aemeasurable
  haveI : IsProbabilityMeasure (boundary.map realization) :=
    Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable
  have transported := levyProkhorovEDist_map_continuous_tendsto_zero
    (fun depth => boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks.val marks.property.1.1 depth (path (depth + 1))))
    (boundary.map realization) (fun point => homeomorph.symm point) homeomorph.symm.continuous projection
  have images : ∀ depth,
      (boundary.map (fun path => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1)))).map homeomorph.symm =
      boundary.map (fun path => actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth (path (depth + 1))) := by
    intro depth
    rw [Measure.map_map homeomorph.symm.measurable (pointMeasurable depth)]
    apply Measure.map_congr
    exact Eventually.of_forall (fun path => actual_inverse_carrier_component_word_point rule classicalRule p positive belowOne
      fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive lengths lengthNonnegative
      lengthPositive childConvergence homeomorph inverseBirth depth (path (depth + 1)))
  simp_rw [images] at transported
  rw [Measure.map_map homeomorph.symm.measurable realizationMeasurable] at transported
  exact transported

end
end IGSIII34.Spectral
