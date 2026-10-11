import IGSIII34.ResistanceLimit.ActualCarrierMeasureCompletion20261011
import IGSIII.Geometry.ActualFiniteCluster
import IGSIII34.Spectral.Collars.CellCarrierTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

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

variable (homeomorph : (ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
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
theorem actual_inverse_carrier_component_word_point
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    homeomorph.symm (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
      marks.val marks.property.1.1 depth word) =
    actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth word := by
  unfold actualElectricalComponentWordPoint actualComponentWordPoint
  split_ifs <;> exact inverseBirth _ _

include inverseBirth in
theorem actual_inverse_carrier_boundary_convergence
    (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (convergence : ∀ᵐ path ∂boundary, Tendsto (fun depth =>
      actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive
        marks.val marks.property.1.1 depth (path (depth + 1))) atTop (𝓝 (realization path))) :
    ∀ᵐ path ∂boundary, Tendsto (fun depth =>
      actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth (path (depth + 1)))
      atTop (𝓝 (homeomorph.symm (realization path))) := by
  filter_upwards [convergence] with path limit
  have mapped := (homeomorph.symm.continuous.tendsto (realization path)).comp limit
  apply mapped.congr'
  exact Eventually.of_forall (fun depth => actual_inverse_carrier_component_word_point rule classicalRule p positive belowOne
    fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive lengths lengthNonnegative
    lengthPositive childConvergence homeomorph inverseBirth depth (path (depth + 1)))

theorem inverse_homeomorph_boundary_mass_pushforward
    {Path First Last : Type*} [MeasurableSpace Path]
    [TopologicalSpace First] [TopologicalSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (identification : First ≃ₜ Last) (boundary : Measure Path) (realization : Path → Last)
    (realizationMeasurable : Measurable realization) :
    (boundary.map (identification.symm ∘ realization)).map identification = boundary.map realization := by
  rw [Measure.map_map identification.measurable (identification.symm.measurable.comp realizationMeasurable)]
  apply Measure.map_congr
  exact Eventually.of_forall (fun path => identification.apply_symm_apply (realization path))

theorem inverse_homeomorph_boundary_mass_null_singletons
    {Path First Last : Type*} [MeasurableSpace Path]
    [TopologicalSpace First] [TopologicalSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    [MeasurableSingletonClass First] [MeasurableSingletonClass Last]
    (identification : First ≃ₜ Last) (boundary : Measure Path) (realization : Path → Last)
    (realizationMeasurable : Measurable realization)
    [NullSingletonClass (boundary.map realization)] :
    NullSingletonClass (boundary.map (identification.symm ∘ realization)) := by
  have equality := inverse_homeomorph_boundary_mass_pushforward identification boundary realization realizationMeasurable
  haveI : NullSingletonClass ((boundary.map (identification.symm ∘ realization)).map identification) := by
    rw [equality]
    infer_instance
  exact homeomorph_null_singletons_of_pushforward identification _

end
end IGSIII34.Spectral
