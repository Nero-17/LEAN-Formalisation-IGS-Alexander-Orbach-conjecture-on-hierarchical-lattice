import IGSIII34.ResistanceLimit.StationarySourceTrace
import IGSIII34.ResistanceLimit.StationaryGeneration

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

theorem actual_stationary_generation_source_energy_le
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (fixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ depth address opened (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
        sourceComponentEnergy (network (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth address opened))
          (fun edge => stationaryGenerationResistance rule
            (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
            growth depth address edge.val) (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
        sourceComponentEnergy (network (rule.generation (depth + 1)).network
            (markedGenerationConfiguration rule marks (depth + 1) address opened))
          (fun edge => stationaryGenerationResistance rule
            (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks)
            growth (depth + 1) address edge.val) potential := by
  have allTraces : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ depth address coarse (potential : Fin (Fintype.card ((rule.generation depth).network.SubstitutionVertex rule.network)) → ℝ),
        sourceComponentEnergy (network (rule.generation depth).network coarse)
          (fun edge => growth⁻¹ ^ (depth + 2) * growth * electricalField rule p positive belowOne fixedPoint value
            (address ++ generationEdgeAddress rule depth edge.val) marks)
          (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
        sourceComponentEnergy (network ((rule.generation depth).network.substitute rule.network)
            (substitutionConfigurationEquiv (fun edge => marks
              (address ++ generationEdgeAddress rule depth edge, coarse edge))))
          (fun edge => growth⁻¹ ^ (depth + 2) * electricalField rule p positive belowOne fixedPoint value
            ((address ++ generationEdgeAddress rule depth
              ((substitutionOpenEdgeEquiv (fun edge => marks
                (address ++ generationEdgeAddress rule depth edge, coarse edge))).symm edge).1) ++
              [((substitutionOpenEdgeEquiv (fun edge => marks
                (address ++ generationEdgeAddress rule depth edge, coarse edge))).symm edge).2.val]) marks) potential := by
    apply ae_all_iff.mpr
    intro depth
    apply ae_all_iff.mpr
    intro address
    apply ae_all_iff.mpr
    intro coarse
    exact actual_stationary_substitution_source_energy_le rule p positive belowOne fixedPoint growth growthPositive
      value valuePositive fixed (rule.generation depth).network
      (fun edge => address ++ generationEdgeAddress rule depth edge) coarse
      (growth⁻¹ ^ (depth + 2)) (pow_pos (inv_pos.mpr growthPositive) _)
  filter_upwards [allTraces] with marks traces
  intro depth address opened potential
  have trace := traces depth address (markedGenerationConfiguration rule marks depth address opened) potential
  have configurationIdentity : markedGenerationConfiguration rule marks (depth + 1) address opened =
      substitutionConfigurationEquiv (fun edge => marks
        (address ++ generationEdgeAddress rule depth edge,
          markedGenerationConfiguration rule marks depth address opened edge)) := by
    funext leaf
    obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective leaf
    simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
      markedGenerationConfiguration_bottom_apply rule marks depth address opened edge child
  have coefficientIdentity : growth⁻¹ ^ (depth + 2) * growth = growth⁻¹ ^ (depth + 1) := by
    rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ, mul_assoc,
      inv_mul_cancel₀ growthPositive.ne', mul_one]
  rw [configurationIdentity]
  convert trace using 1
  · congr 1
    funext edge
    simp only [stationaryGenerationResistance, coefficientIdentity]
  · congr 1
    funext edge
    have reconstruction : finProdFinEquiv
        (((substitutionOpenEdgeEquiv (fun edge => marks
            (address ++ generationEdgeAddress rule depth edge,
              markedGenerationConfiguration rule marks depth address opened edge))).symm edge).1,
          ((substitutionOpenEdgeEquiv (fun edge => marks
            (address ++ generationEdgeAddress rule depth edge,
              markedGenerationConfiguration rule marks depth address opened edge))).symm edge).2.val) = edge.val :=
      congrArg Subtype.val ((substitutionOpenEdgeEquiv (fun edge => marks
        (address ++ generationEdgeAddress rule depth edge,
          markedGenerationConfiguration rule marks depth address opened edge))).apply_symm_apply edge)
    unfold stationaryGenerationResistance
    rw [← reconstruction, generationEdgeAddress_bottom]
    simp only [List.append_assoc, Nat.add_assoc]

end
end IGSIII34.ResistanceLimit
