import IGSIII34.ResistanceLimit.StationaryBlockZeroLimit
import IGSIII34.Forms.CoherentSkeletonPotential

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
      ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable first last →
      pairResistance (network (rule.generation (depth + 1)).network
          (markedGenerationConfiguration rule marks (depth + 1) [] true))
        (fun edge => stationaryGenerationResistance rule field growth (depth + 1) [] edge.val)
        (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
      pairResistance (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
        (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val) first last)
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

theorem stationaryBlockZeroPositive (depth : ℕ)
    (edge : {edge : Fin (rule.generation depth).edges // markedGenerationConfiguration rule marks depth [] true edge = true}) :
    0 < stationaryGenerationResistance rule field growth depth [] edge.val :=
  mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)

def stationaryBlockZeroSkeletonPotential := coherentSkeletonPotential rule
  (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
  (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
  (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
  (actualBlockZeroTowerStage rule coarse chosen potentials)
  (fun depth vertex => actualBlockZeroTowerStage_next rule coarse chosen potentials atSource atTarget restriction depth vertex.val)

include crossing stationary projection anchorRetained

/-- Zero extension is an actual element of the global energy domain; its
values on the entire dense retained skeleton and its energy are exact. -/
theorem stationary_block_zero_skeleton_extension
    (finite : BddAbove (Set.range (fun fine => sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth fine
        (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine)))) :
    let endpoint := skeletonEnergyEndpoint rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
    let conductance := skeletonEnergyConductance rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    let nonnegative := skeletonEnergyConductance_nonnegative rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive)
    let potential := stationaryBlockZeroSkeletonPotential rule marks field growth growthPositive fieldPositive
      coherent compatible coarse chosen potentials atSource atTarget restriction
    potential ∈ energyDomain endpoint conductance nonnegative ∧
    limitingEnergy endpoint conductance potential = growth ^ (coarse + 1) * ⨆ fine, sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth fine
        (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine) := by
  dsimp only
  have result := stationary_block_zero_extension_limit rule marks crossing field growth growthPositive fieldPositive
    stationary coarse chosen sourceSide potentials projection atSource atTarget restriction anchorRetained finite
  refine ⟨?_, ?_⟩
  · apply (coherentSkeletonPotential_finite_iff rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
      (actualBlockZeroTowerStage rule coarse chosen potentials)
      (fun depth vertex => actualBlockZeroTowerStage_next rule coarse chosen potentials atSource atTarget restriction depth vertex.val)).mpr
    exact result.1
  · rw [stationaryBlockZeroSkeletonPotential, coherentSkeletonPotential_limiting_energy]
    exact result.2

omit crossing stationary projection anchorRetained in
theorem stationaryBlockZeroSkeletonPotential_retained (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)) :
    stationaryBlockZeroSkeletonPotential rule marks field growth growthPositive fieldPositive coherent compatible
      coarse chosen potentials atSource atTarget restriction
      (electricalSkeletonVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
        (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
        (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible depth vertex) =
      actualBlockZeroTowerStage rule coarse chosen potentials depth vertex.val := rfl

include crossing stationary projection anchorRetained in
/-- The same zero extension belongs to the full continuous completion form,
with unchanged energy. No values off the dense skeleton are chosen freely. -/
theorem stationary_block_zero_completion_extension
    (finite : BddAbove (Set.range (fun fine => sourceComponentEnergy
      (sideNetwork (network (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
          (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
      (fun edge => stationaryGenerationResistance rule field growth fine
        (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine)))) :
    let endpoint := skeletonEnergyEndpoint rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
    let conductance := skeletonEnergyConductance rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    let nonnegative := skeletonEnergyConductance_nonnegative rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive)
    let potential := stationaryBlockZeroSkeletonPotential rule marks field growth growthPositive fieldPositive
      coherent compatible coarse chosen potentials atSource atTarget restriction
    ∃ extension : C(UniformSpace.Completion (ElectricalSkeleton rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
      (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
      (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible), ℝ),
      (∀ point : ElectricalSkeleton rule (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
        (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
        (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible,
        extension point = potential point) ∧
      (extension : UniformSpace.Completion (ElectricalSkeleton rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
        (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
        (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible) → ℝ) ∈
        energyDomain (completionEnergyEndpoint endpoint) conductance nonnegative ∧
      limitingEnergy (completionEnergyEndpoint endpoint) conductance extension =
        growth ^ (coarse + 1) * ⨆ fine, sourceComponentEnergy
          (sideNetwork (network (rule.generation fine).network
            (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse chosen)
              (markedGenerationConfiguration rule marks coarse [] true chosen))) sourceSide)
          (fun edge => stationaryGenerationResistance rule field growth fine
            (generationEdgeAddress rule coarse chosen) edge.val) (potentials fine) := by
  dsimp only
  obtain ⟨globalFinite, energy⟩ := stationary_block_zero_skeleton_extension rule marks crossing field growth
    growthPositive fieldPositive stationary coherent compatible coarse chosen sourceSide potentials
    projection atSource atTarget restriction anchorRetained finite
  let potential := stationaryBlockZeroSkeletonPotential rule marks field growth growthPositive fieldPositive
    coherent compatible coarse chosen potentials atSource atTarget restriction
  let endpoint := skeletonEnergyEndpoint rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
  let conductance := skeletonEnergyConductance rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
  let nonnegative := skeletonEnergyConductance_nonnegative rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive)
  have resistanceBound := skeleton_finite_energy_resistance_bound rule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
    (fun depth edge => stationaryGenerationResistance rule field growth depth [] edge.val)
    (stationaryBlockZeroPositive rule marks field growth growthPositive fieldPositive) compatible
  refine ⟨completionExtension endpoint conductance nonnegative ⟨potential, globalFinite⟩, ?_, ?_, ?_⟩
  · intro point
    exact completionExtension_coe endpoint conductance nonnegative resistanceBound ⟨potential, globalFinite⟩ point
  · exact completionExtension_energyDomain endpoint conductance nonnegative resistanceBound ⟨potential, globalFinite⟩
  · rw [completionExtension_limitingEnergy endpoint conductance nonnegative resistanceBound]
    exact energy

end
end IGSIII34.ResistanceLimit
