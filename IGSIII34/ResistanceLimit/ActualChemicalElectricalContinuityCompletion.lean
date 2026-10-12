import IGSIII34.ResistanceLimit.ChemicalElectricalSkeletonMapCompletion
import IGSIII34.ResistanceLimit.FiniteAnchorModulusCompletion
import IGSIII34.ResistanceLimit.ActualChemicalBlockCompatibilityCompletion
import IGSIII34.ResistanceLimit.ActualElectricalLocalMeshCompletion

/-! The actual chemical-to-electrical map is uniformly continuous. Every
finite-level modulus is derived from true available components and the
original unit-edge radius limits; continuity is not a supplied certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

theorem actualChemicalElectricalSkeletonMap_uniformContinuous_completion
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (lengthNonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (lengthPositive : ∀ depth edge, stationaryConfiguration rule marks.val depth edge = true → 0 < lengths depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (stationaryConfiguration rule marks.val (coarse + fine + 1)) edge)).dist
        (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        chemicalScale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length) :
    UniformContinuous (chemicalElectricalSkeletonMapCompletion rule classicalRule
      (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
      chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
      marks.property.2.2) := by
  apply chemicalElectricalSkeletonMap_uniformContinuous_completion
  intro epsilon epsilonPositive
  have vanishing : Tendsto (fun coarse : ℕ => coefficient * eta ^ (coarse + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one etaNonnegative etaBelowOne).comp (tendsto_add_atTop_nat 1))
  obtain ⟨coarse, beyond, small⟩ := ((eventually_ge_atTop start).and
    ((tendsto_order.mp vanishing).2 (epsilon / 2) (div_pos epsilonPositive (by norm_num)))).exists
  obtain ⟨delta, deltaPositive, modulus⟩ := actual_generation_chemical_electrical_modulus_completion
    rule classicalRule marks.val marks.property.2.1 lengths lengthNonnegative lengthPositive
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks)
    coarse (coefficient * eta ^ (coarse + 1))
    (by
      intro fine first last firstRetained lastRetained
      exact actual_chemical_block_weighted_compatibility_completion rule classicalRule
        (stationaryConfiguration rule marks.val)
        (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value marks)
        chemicalScale chemicalScalePositive lengths lengthNonnegative lengthPositive childConvergence
        coarse fine ⟨first,firstRetained⟩ ⟨last,lastRetained⟩)
    (by
      intro fine edge side vertex reachable retained
      exact actual_stationary_local_resistance_mesh_completion rule p positive belowOne fixedPoint growth value
        growthPositive marks fieldLimit eta coefficient start radiusBounds coarse fine beyond edge side vertex reachable retained)
  refine ⟨coarse, delta, deltaPositive, ?_⟩
  intro fine first last chemicalSmall
  rw [actualChemicalVertex_distance] at chemicalSmall
  rw [electricalVertex_distance]
  exact (modulus fine first last chemicalSmall).trans_lt (by linarith)

end
end IGSIII34.ResistanceLimit
