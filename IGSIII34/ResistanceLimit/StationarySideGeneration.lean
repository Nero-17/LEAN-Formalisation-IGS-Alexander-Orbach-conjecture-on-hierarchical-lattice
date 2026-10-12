import IGSIII34.ResistanceLimit.SideSourceTrace
import IGSIII34.ResistanceLimit.StationaryBlockTraceCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution

theorem stationary_side_block_source_energy_le
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    {outerVertices outerEdges : ℕ} (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (addresses : Fin outerEdges → List (Fin rule.edges)) (coarse : Configuration outerEdges)
    (fine : ℕ) (scalar : ℝ) (scalarPositive : 0 < scalar) (sourceSide : Bool)
    (potential : Fin (Fintype.card (outer.SubstitutionVertex (rule.generation fine).network)) → ℝ) :
    sourceComponentEnergy (sideNetwork (network outer coarse) sourceSide)
      (fun edge => scalar * growth ^ (fine + 1) * field (addresses edge.val))
      (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex (rule.generation fine).network))) ≤
    sourceComponentEnergy (sideNetwork (network (outer.substitute (rule.generation fine).network)
      (substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge)))) sourceSide)
      (fun edge => scalar * field (addresses ((substitutionOpenEdgeEquiv
        (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).1 ++
        generationEdgeAddress rule fine ((substitutionOpenEdgeEquiv
          (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).2.val)) potential := by
  cases sourceSide with
  | true =>
      exact stationary_block_source_energy_le rule marks field growth growthPositive fieldPositive
        crossing stationary outer addresses coarse fine scalar scalarPositive potential
  | false =>
      exact stationary_block_source_energy_le rule marks field growth growthPositive fieldPositive
        crossing stationary (swapNetworkTerminals outer) addresses coarse fine scalar scalarPositive potential

/-- Both genuinely retained sides of every stationary descendant component
have monotone finite traces under the original old-vertex embedding. -/
theorem stationary_generation_side_source_energy_le
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (potential : Fin (rule.generation (depth + 1)).vertices → ℝ) :
    sourceComponentEnergy (sideNetwork (network (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth address opened)) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth depth address edge.val)
      (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
    sourceComponentEnergy (sideNetwork (network (rule.generation (depth + 1)).network
      (markedGenerationConfiguration rule marks (depth + 1) address opened)) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth (depth + 1) address edge.val) potential := by
  have comparison := stationary_side_block_source_energy_le rule marks field growth growthPositive fieldPositive
    crossing stationary (rule.generation depth).network
    (fun edge => address ++ generationEdgeAddress rule depth edge)
    (markedGenerationConfiguration rule marks depth address opened) 0
    (growth⁻¹ ^ (depth + 2)) (pow_pos (inv_pos.mpr growthPositive) _) sourceSide potential
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
  convert comparison using 1
  · congr 1
    funext edge
    simp only [stationaryGenerationResistance, Nat.zero_add, pow_one, coefficientIdentity]
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
    simp only [generationEdgeAddress, markedGenerationConfiguration, List.append_assoc, Nat.add_assoc]
    rfl

end
end IGSIII34.ResistanceLimit
