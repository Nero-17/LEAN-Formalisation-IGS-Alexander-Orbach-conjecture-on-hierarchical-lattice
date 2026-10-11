import IGSIII34.ResistanceLimit.HarmonicTower
import IGSIII34.ResistanceLimit.SourcePairHarmonic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

variable (rule : Rule)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
variable (positive : ∀ depth edge, 0 < resistance depth edge)
variable (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
  ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
  pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
    pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)
variable (minimizer : ∀ depth (boundary : Fin (rule.generation depth).vertices → ℝ),
  ∃ potential : Fin (rule.generation (depth + 1)).vertices → ℝ,
    (∀ vertex, ((rule.generation depth).network.openGraph (configuration depth)).Reachable
        (rule.generation depth).network.source vertex →
      potential (rule.generationOldVertex depth vertex) = boundary vertex) ∧
    sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
      (resistance (depth + 1)) potential =
    sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth) boundary)
variable (sourceEnergyLe : ∀ depth (potential : Fin (rule.generation (depth + 1)).vertices → ℝ),
  sourceComponentEnergy (network (rule.generation depth).network (configuration depth)) (resistance depth)
    (fun vertex => potential (rule.generationOldVertex depth vertex)) ≤
  sourceComponentEnergy (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
    (resistance (depth + 1)) potential)

include minimizer sourceEnergyLe in
/-- Every resistance distance on the whole born-vertex skeleton is attained by
a globally finite-energy function, not merely by a finite-network potential. -/
theorem skeleton_resistance_attained :
    ∀ first last : ElectricalSkeleton rule configuration coherent resistance positive compatible,
      first ≠ last → ∃ potential : energyDomain
        (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
        (skeletonEnergyConductance rule configuration resistance)
        (skeletonEnergyConductance_nonnegative rule configuration resistance positive),
        potential.val first = 0 ∧ potential.val last = 1 ∧
        limitingEnergy (skeletonEnergyEndpoint rule configuration coherent resistance positive compatible)
          (skeletonEnergyConductance rule configuration resistance) potential.val = (dist first last)⁻¹ := by
  intro first last
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedSkeletonVertex (rule.generation depth).network (configuration depth))
      (retainedOldVertexEmbedding rule configuration coherent)) (fun depth first last => ?_) first last
  intro distinct
  have vertexDistinct : first.val ≠ last.val := by
    intro equal
    apply distinct
    exact congrArg (fun vertex => electricalSkeletonVertex rule configuration coherent resistance positive compatible depth vertex)
      (Subtype.ext equal)
  obtain ⟨boundary, atFirst, atLast, energy⟩ := exists_source_pair_minimizer
    (network (rule.generation depth).network (configuration depth)) (resistance depth) (positive depth)
    vertexDistinct (by rw [graph_eq_openGraph]; exact first.property)
    (by rw [graph_eq_openGraph]; exact last.property)
  refine ⟨⟨harmonicTowerFunction rule configuration coherent resistance positive compatible minimizer depth boundary,
      harmonicTowerFunction_finite rule configuration coherent resistance positive compatible minimizer sourceEnergyLe depth boundary⟩,
    ?_, ?_, ?_⟩
  · exact (harmonicTowerFunction_boundary rule configuration coherent resistance positive compatible minimizer depth boundary first).trans atFirst
  · exact (harmonicTowerFunction_boundary rule configuration coherent resistance positive compatible minimizer depth boundary last).trans atLast
  · exact (harmonicTowerFunction_limiting_energy rule configuration coherent resistance positive compatible minimizer
      sourceEnergyLe depth boundary).trans (energy.trans (congrArg Inv.inv
        (electricalSkeletonVertex_distance rule configuration coherent resistance positive compatible depth first last).symm))

end
end IGSIII34.ResistanceLimit
