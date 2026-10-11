import IGSIII34.ResistanceLimit.StationaryBlockZeroEnergy
import IGSIII34.ResistanceLimit.ActualBlockZeroTower
import IGSIII34.ResistanceLimit.StationarySideGeneration
import IGSIII34.Forms.ComponentEnergyDecomposition

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped Topology

variable (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (coarse : ℕ) (chosen : Fin (rule.generation coarse).edges) (sourceSide : Bool)
    (potentials : ∀ fine, Fin (rule.generation fine).vertices → ℝ)
    (projection : ∀ fine, sourceProjection (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide) (potentials fine) = potentials fine)
    (atSource : ∀ fine, potentials fine (rule.generation fine).network.source = 0)
    (atTarget : ∀ fine, potentials fine (rule.generation fine).network.target = 0)
    (restriction : ∀ fine vertex, potentials (fine + 1) (rule.generationOldVertex fine vertex) = potentials fine vertex)
    (anchorRetained : ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks coarse [] true)).Reachable
      (rule.generation coarse).network.source (coarseCellPlantedVertex rule coarse chosen sourceSide))

include crossing growthPositive fieldPositive stationary projection atSource atTarget restriction anchorRetained

/-- A finite-energy local potential vanishing at the planted boundary has a
genuine coherent global zero extension, with the prescribed energy scaling. -/
theorem stationary_block_zero_extension_limit
    (finite : BddAbove (Set.range (fun fine => sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth fine
        (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine)))) :
    BddAbove (Set.range (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (actualBlockZeroTowerStage rule coarse chosen potentials depth))) ∧
    (⨆ depth, sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (actualBlockZeroTowerStage rule coarse chosen potentials depth)) =
    growth ^ (coarse + 1) * ⨆ fine, sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth fine
        (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine) := by
  let localTrace : ℕ → ℝ := fun fine => sourceComponentEnergy
    (sideNetwork (network (rule.generation fine).network
      (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
        (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
    (fun edge => stationaryGenerationResistance rule field growth fine
      (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine)
  let globalTrace : ℕ → ℝ := fun depth => sourceComponentEnergy
    (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
    (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    (actualBlockZeroTowerStage rule coarse chosen potentials depth)
  have localMonotone : Monotone localTrace := by
    apply monotone_nat_of_le_succ
    intro fine
    have comparison := stationary_generation_side_source_energy_le rule marks field growth growthPositive
      fieldPositive crossing stationary fine (generationEdgeAddress rule coarse chosen)
      (markedGenerationConfiguration rule marks coarse [] true chosen) sourceSide (potentials (fine + 1))
    simpa only [restriction] using comparison
  have globalMonotone : Monotone globalTrace := by
    apply monotone_nat_of_le_succ
    intro depth
    have comparison := stationary_generation_side_source_energy_le rule marks field growth growthPositive
      fieldPositive crossing stationary depth [] true true
      (actualBlockZeroTowerStage rule coarse chosen potentials (depth + 1))
    simpa only [sideNetwork, if_true,
      actualBlockZeroTowerStage_next rule coarse chosen potentials atSource atTarget restriction] using comparison
  have scaledFinite : BddAbove (Set.range (fun fine => growth ^ (coarse + 1) * localTrace fine)) := by
    obtain ⟨upper, bound⟩ := finite
    refine ⟨growth ^ (coarse + 1) * upper, ?_⟩
    rintro value ⟨fine, rfl⟩
    exact mul_le_mul_of_nonneg_left (bound (Set.mem_range_self fine)) (pow_pos growthPositive _).le
  have identity (fine : ℕ) : globalTrace (fine + (coarse + 1)) = growth ^ (coarse + 1) * localTrace fine := by
    have order : fine + (coarse + 1) = coarse + fine + 1 := by omega
    rw [order]
    dsimp only [globalTrace, localTrace]
    have stageIdentity : actualBlockZeroTowerStage rule coarse chosen potentials (coarse + fine + 1) =
        actualBlockZeroExtension rule coarse fine chosen (potentials fine) := by
      funext vertex
      exact actualBlockZeroTowerStage_tail rule coarse fine chosen potentials vertex
    rw [stageIdentity]
    exact stationary_block_zero_extension_energy rule marks crossing field growth coarse fine chosen sourceSide
      (potentials fine) (projection fine) (atSource fine) (atTarget fine) anchorRetained
  have result := component_zero_extension_energy globalTrace
    (fun fine => growth ^ (coarse + 1) * localTrace fine) (coarse + 1)
    globalMonotone (localMonotone.const_mul (pow_pos growthPositive _).le) identity scaledFinite
  refine ⟨result.1, ?_⟩
  have localLimit := (tendsto_atTop_ciSup localMonotone finite).const_mul (growth ^ (coarse + 1))
  have globalLimit := (tendsto_atTop_ciSup globalMonotone result.1).comp
    (tendsto_add_atTop_nat (coarse + 1))
  have equalLimits : (⨆ depth, globalTrace depth) = growth ^ (coarse + 1) * ⨆ fine, localTrace fine := by
    apply tendsto_nhds_unique globalLimit
    simpa only [Function.comp_def, identity] using localLimit
  exact equalLimits

end
end IGSIII34.ResistanceLimit
