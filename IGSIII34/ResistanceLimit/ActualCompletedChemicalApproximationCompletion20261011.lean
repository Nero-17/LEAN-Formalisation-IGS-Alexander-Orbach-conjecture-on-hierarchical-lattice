import IGSIII34.ResistanceLimit.ActualChemicalHarmonicApproximationCompletion20261011
import IGSIII34.ResistanceLimit.ChemicalElectricalCompletionMapCompletion20261011
import IGSIII34.ResistanceLimit.HarmonicTowerComponentBoundsCompletion20261011
import IGSIII34.ResistanceLimit.ActualHarmonicGlobalRangeCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalLocalMeshCompletion20261011
import IGSIII34.ResistanceLimit.ActualChemicalBlockAnchorsCompletion20261011
import IGSIII.Geometry.ChemicalMetricCodeFaithfulness

/-! The actual continuous harmonic interpolation preserves the entire range
of the retained initial boundary, including every hanging component. -/
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

theorem actual_harmonic_completed_chemical_approximation_completion20261011
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (continuousSkeleton : UniformContinuous (chemicalElectricalSkeletonMapCompletion20261011 rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2))
    (test : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → ℝ)
    (testLipschitz : LipschitzWith 1 test)
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse : ℕ) (beyond : start ≤ coarse)
    (point : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence) :
    |actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks coarse
      (actualChemicalSampledBoundaryCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule chemicalScale
        chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence test coarse)
      (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
        marks.property.1.1.2.2 point) - test point| ≤ coefficient * eta ^ (coarse + 1) := by
  have mapContinuous := (chemicalElectricalCompletionMap_uniformContinuous_completion20261011 rule classicalRule
    (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
    marks.property.1.1.2.2).continuous
  have closed : IsClosed {point | |actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive marks coarse
      (actualChemicalSampledBoundaryCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule chemicalScale
        chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence test coarse)
      (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
        marks.property.1.1.2.2 point) - test point| ≤ coefficient * eta ^ (coarse + 1)} :=
    isClosed_le (((actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks coarse
      (actualChemicalSampledBoundaryCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule chemicalScale
        chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence test coarse)).continuous.comp mapContinuous).sub
        testLipschitz.continuous).abs continuous_const
  have contains : (⋃ depth, Set.range (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth)) ⊆ {point | |actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive marks coarse
      (actualChemicalSampledBoundaryCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule chemicalScale
        chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence test coarse)
      (chemicalElectricalCompletionMapCompletion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
        (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
        marks.property.1.1.2.2 point) - test point| ≤ coefficient * eta ^ (coarse + 1)} := by
    intro point membership
    obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
    simp only [Set.mem_setOf_eq]
    rw [actualChemicalVertex_persistent rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence depth (coarse + depth + 1) (by omega)]
    rw [chemicalElectricalCompletionMap_birth_completion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2 continuousSkeleton]
    exact actual_harmonic_fine_chemical_approximation_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence stationary test testLipschitz
      eta coefficient start radiusBounds coarse depth beyond _
  have full := closure_minimal contains closed
  rw [(actualChemicalVertex_dense rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence).closure_eq] at full
  exact full (Set.mem_univ point)

end
end IGSIII34.ResistanceLimit



