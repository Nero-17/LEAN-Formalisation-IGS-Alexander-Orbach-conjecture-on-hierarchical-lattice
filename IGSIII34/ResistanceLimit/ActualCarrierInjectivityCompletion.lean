import IGSIII34.ResistanceLimit.ActualCompletedChemicalApproximationCompletion
import IGSIII34.ResistanceLimit.ChemicalElectricalCompletionMapCompletion
import IGSIII34.ResistanceLimit.HarmonicTowerComponentBoundsCompletion
import IGSIII34.ResistanceLimit.ActualHarmonicGlobalRangeCompletion
import IGSIII34.ResistanceLimit.ActualChemicalLocalMeshCompletion
import IGSIII34.ResistanceLimit.ActualChemicalBlockAnchorsCompletion
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

theorem actual_chemical_electrical_completion_injective_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (continuousSkeleton : UniformContinuous (chemicalElectricalSkeletonMapCompletion rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks.val depth address opened : ℝ) / chemicalScale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length) :
    Function.Injective (chemicalElectricalCompletionMapCompletion rule classicalRule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val,marks.property.1.1⟩)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val,marks.property.1.1⟩)
      marks.property.1.1.2.2) := by
  intro first last same
  by_contra distinct
  have distancePositive := dist_pos.mpr distinct
  have vanishing : Tendsto (fun coarse : ℕ => coefficient * eta ^ (coarse + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1))
  obtain ⟨coarse, beyond, small⟩ := ((eventually_ge_atTop start).and
    ((tendsto_order.mp vanishing).2 (dist first last / 4) (div_pos distancePositive (by norm_num)))).exists
  have firstApprox := actual_harmonic_completed_chemical_approximation_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary continuousSkeleton (fun point => dist point first) (LipschitzWith.dist_left first)
    eta coefficient start radiusBounds coarse beyond first
  have lastApprox := actual_harmonic_completed_chemical_approximation_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks classicalRule chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
    stationary continuousSkeleton (fun point => dist point first) (LipschitzWith.dist_left first)
    eta coefficient start radiusBounds coarse beyond last
  rw [same] at firstApprox
  simp only [dist_self, sub_zero] at firstApprox
  rw [dist_comm last first] at lastApprox
  have firstBoth := abs_le.mp firstApprox
  have lastBoth := abs_le.mp lastApprox
  linarith

end
end IGSIII34.ResistanceLimit


