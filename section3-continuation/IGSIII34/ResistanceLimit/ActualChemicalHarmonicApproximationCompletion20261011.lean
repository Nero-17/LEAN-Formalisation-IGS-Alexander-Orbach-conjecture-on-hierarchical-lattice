import IGSIII34.Spectral.ActualBoundaryHarmonicCompletion20261011
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

def actualChemicalSampledBoundaryCompletion20261011
    (test : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → ℝ)
    (coarse : ℕ) (vertex : Fin (rule.generation coarse).vertices) : ℝ :=
  test (actualChemicalLabelPoint rule classicalRule (stationaryConfiguration rule marks.val)
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence ⟨coarse,vertex⟩)

theorem actual_harmonic_completion_fine_value_completion20261011
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (vertex : RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks.val (coarse + fine + 1))) :
    actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      coarse boundary (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ (coarse + fine + 1) vertex) =
    harmonicTower rule (stationaryConfiguration rule marks.val)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val) marks.property.2
      coarse boundary (coarse + fine + 1) (by omega) vertex.val := by
  have extensionValue := completionExtension_coe
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    ⟨_, actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary⟩
    (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1) vertex)
  exact extensionValue.trans (actualHarmonicFunction_retained_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks coarse boundary (coarse + fine + 1) (by omega) vertex)

theorem actual_harmonic_fine_chemical_approximation_completion20261011
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (test : ActualChemicalSpace rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence → ℝ)
    (testLipschitz : LipschitzWith 1 test)
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (coarse fine : ℕ) (beyond : start ≤ coarse)
    (vertex : RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
      (stationaryConfiguration rule marks.val (coarse + fine + 1))) :
    |actualHarmonicCompletionFunctionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks coarse
      (actualChemicalSampledBoundaryCompletion20261011 rule p positive belowOne fixedPoint growth value marks classicalRule chemicalScale
        chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence test coarse)
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val,marks.property.1.1⟩ (coarse + fine + 1) vertex) -
      test (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence (coarse + fine + 1) vertex)| ≤
      coefficient * eta ^ (coarse + 1) := by
  rw [actual_harmonic_completion_fine_value_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks]
  obtain ⟨edge, child, side, identity, reachable, _⟩ := actual_retained_generation_available_cell_cover
    rule marks.val marks.property.1.1.2.1 coarse fine vertex.val vertex.property
  rw [identity]
  refine stationary_harmonic_tower_component_deviation_completion20261011 rule marks.val
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth growthPositive
    marks.property.1.1.1 marks.property.1.1.2.1 stationary [] true
    (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
    marks.property.2 coarse fine _ edge _ (coefficient * eta ^ (coarse + 1)) child ?_ ?_ (identity ▸ vertex.property)
  · intro availableSide localReachable
    have coarseRetained := actual_available_block_anchor_retained_completion20261011 rule marks.val marks.property.1.1.2.1 coarse fine [] true
      edge availableSide child localReachable (identity ▸ vertex.property)
    obtain ⟨fineRetained, chemicalBound⟩ := actual_chemical_local_component_mesh_completion20261011 rule classicalRule marks.val
      (stationaryConfiguration rule marks.val) (fun _ => rfl)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence eta coefficient start radiusBounds
      coarse fine beyond edge availableSide child localReachable (identity ▸ vertex.property)
    have pointIdentity : (⟨(generationBlockCellEmbedding rule coarse fine edge).vertex child, identity ▸ vertex.property⟩ :
      RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network (stationaryConfiguration rule marks.val (coarse + fine + 1))) = vertex :=
      Subtype.ext identity.symm
    rw [pointIdentity] at chemicalBound
    unfold actualChemicalSampledBoundaryCompletion20261011
    rw [actualChemicalLabelPoint_of_retained rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence coarse ⟨_,coarseRetained⟩,
      actual_chemical_block_anchor_point_completion20261011 rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence coarse fine edge availableSide
        coarseRetained fineRetained]
    have testBound := testLipschitz.dist_le_mul
      (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        (coarse + fine + 1) ⟨_,fineRetained⟩)
      (actualChemicalVertex rule classicalRule (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence (coarse + fine + 1) vertex)
    simp only [NNReal.coe_one, one_mul] at testBound
    simpa only [Real.dist_eq] using testBound.trans chemicalBound
  · cases side
    · exact Or.inr reachable
    · exact Or.inl reachable

end
end IGSIII34.ResistanceLimit


