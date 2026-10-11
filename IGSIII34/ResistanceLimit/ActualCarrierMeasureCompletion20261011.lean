import IGSIII34.ResistanceLimit.ActualCarrierHomeomorphCompletion20261011
import IGSIII34.ResistanceLimit.ElectricalBoundaryCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalElectricalContinuityCompletion20261011
import IGSIII.Geometry.ActualChemicalNets
import Mathlib.Topology.Homeomorph.Lemmas
import IGSIII34.ResistanceLimit.ChemicalElectricalCompletionMapCompletion20261011
import IGSIII34.ResistanceLimit.HarmonicTowerComponentBoundsCompletion20261011
import IGSIII34.ResistanceLimit.ActualHarmonicGlobalRangeCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalLocalMeshCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalBlockAnchorsCompletion20261011
import IGSIII.Geometry.ChemicalMetricCodeFaithfulness

/-! The actual chemical-to-electrical carrier map preserves component boundary
realizations and therefore the same boundary-law mass measure. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Spectral IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

variable (classicalRule : rule.Classical) (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

variable (continuousSkeleton : UniformContinuous (chemicalElectricalSkeletonMapCompletion20261011 rule classicalRule
  (stationaryConfiguration rule marks.val)
  (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
  chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
  (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
  (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
  marks.property.1.1.2.2))

include continuousSkeleton in
theorem actual_carrier_map_component_word_point_completion20261011
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    chemicalElectricalCompletionMapCompletion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2
      (actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth word) =
    actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1 depth word := by
  unfold actualComponentWordPoint actualElectricalComponentWordPoint
  split_ifs <;> exact chemicalElectricalCompletionMap_birth_completion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2 continuousSkeleton _ _

variable (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
  (chemicalRealization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
    ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)
  (electricalRealization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
    ElectricalSpace rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2)
  (chemicalConvergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
    actualComponentWordPoint rule classicalRule marks.val marks.property.1.1.2.1
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth (path (depth+1)))
    atTop (𝓝 (chemicalRealization path)))
  (electricalConvergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
    actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1
      depth (path (depth+1))) atTop (𝓝 (electricalRealization path)))

include continuousSkeleton chemicalConvergence electricalConvergence in
theorem actual_carrier_map_boundary_realization_ae_completion20261011 :
    ∀ᵐ path ∂boundaryLaw,
      chemicalElectricalCompletionMapCompletion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
        marks.property.1.1.2.2 (chemicalRealization path) = electricalRealization path := by
  filter_upwards [chemicalConvergence, electricalConvergence] with path chemicalLimit electricalLimit
  have mappedLimit := ((chemicalElectricalCompletionMap_uniformContinuous_completion20261011 rule classicalRule
    (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2).continuous.tendsto (chemicalRealization path)).comp chemicalLimit
  have actualLimit := mappedLimit.congr' (Eventually.of_forall (fun depth => actual_carrier_map_component_word_point_completion20261011 rule p
    positive belowOne fixedPoint growth value growthPositive marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative
    lengthPositive childConvergence continuousSkeleton depth (path (depth+1))))
  exact tendsto_nhds_unique actualLimit electricalLimit

variable [MeasurableSpace (ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
  [BorelSpace (ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence)]
  [MeasurableSpace (ElectricalSpace rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2)]
  [BorelSpace (ElectricalSpace rule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2)]
include continuousSkeleton chemicalConvergence electricalConvergence in
theorem actual_carrier_pushforward_mass_eq_completion20261011
    (chemicalMeasurable : Measurable chemicalRealization) :
    (boundaryLaw.map chemicalRealization).map (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) = boundaryLaw.map electricalRealization := by
  rw [Measure.map_map ((chemicalElectricalCompletionMap_uniformContinuous_completion20261011 rule classicalRule
    (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2).continuous.measurable) chemicalMeasurable]
  apply Measure.map_congr
  exact actual_carrier_map_boundary_realization_ae_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
    classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence continuousSkeleton boundaryLaw
    chemicalRealization electricalRealization chemicalConvergence electricalConvergence

end
end IGSIII34.ResistanceLimit




