import IGSIII34.ResistanceLimit.SkeletonTrace
import IGSIII.Geometry.ActualSkeletonLimits

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry Filter
open scoped Topology

/-- Exact all-pair elimination on the actual generation graph. All child
components are present; only their terminal response is eliminated. -/
theorem actual_block_scaled_resistance_trace (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (coarse fine : ℕ) (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (first last : Fin (rule.generation coarse).vertices)
    (reachable : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable first last) :
    scalar * pairResistance (network (rule.generation (coarse + fine + 1)).network
        (configuration (coarse + fine + 1))) (fun _ => 1)
      (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last) =
    pairResistance (network (rule.generation coarse).network (configuration coarse))
      (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge.val)) first last := by
  have transported := networkEquivalence_pairResistance (rule.generationBlockDecomposition coarse fine)
    (configuration (coarse + fine + 1))
    (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last)
  have configurationIdentity :
      (rule.generationBlockDecomposition coarse fine).configuration (configuration (coarse + fine + 1)) =
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))) := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  rw [configurationIdentity] at transported
  simp only [blockOldVertexEmbedding, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] at transported
  have coarseIdentity := generationBlockCoarse_of_coherent rule configuration coherent coarse fine
  change (rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))) = configuration coarse at coarseIdentity
  have coarseReachable :
      ((rule.generation coarse).network.openGraph
        ((rule.generation fine).network.coarseConfiguration
          (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))))).Reachable first last := by
    rwa [coarseIdentity]
  have traced := actual_substitution_scaled_pairResistance_trace (rule.generation coarse).network
    (rule.generation fine).network
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)))
    scalar scalarNonnegative first last coarseReachable
  have coarseTransport := congrArg (fun coarseConfiguration : Configuration (rule.generation coarse).edges =>
    pairResistance (network (rule.generation coarse).network coarseConfiguration)
      (fun edge => scalar * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge.val)) first last) coarseIdentity
  exact (congrArg (fun value : ℝ => scalar * value) transported.symm).trans (traced.trans coarseTransport)

/-- The finite stationary resistance matrix is the limit of normalized
resistances between the same vertices in the actual microscopic graphs. -/
theorem actual_block_skeleton_resistances_tendsto (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (scale : ℝ) (scalePositive : 0 < scale) (coarse : ℕ)
    (limitResistance : {edge : Fin (rule.generation coarse).edges // configuration coarse edge = true} → ℝ)
    (limitNonnegative : ∀ edge, 0 ≤ limitResistance edge)
    (childConvergence : ∀ edge, Tendsto (fun fine =>
      (scale ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge.val))
      atTop (𝓝 (limitResistance edge)))
    {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph (configuration coarse)).Reachable first last) :
    Tendsto (fun fine => (scale ^ (coarse + fine + 2))⁻¹ *
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (configuration (coarse + fine + 1))) (fun _ => 1)
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last))
      atTop (𝓝 (pairResistance (network (rule.generation coarse).network (configuration coarse))
        limitResistance first last)) := by
  have weightNonnegative : ∀ fine (edge : {edge : Fin (rule.generation coarse).edges // configuration coarse edge = true}),
      0 ≤ (scale ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge.val) := by
    intro fine edge
    have coarseIdentity := generationBlockCoarse_of_coherent rule configuration coherent coarse fine
    change (rule.generation fine).network.coarseConfiguration (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))) = configuration coarse at coarseIdentity
    have retained : (rule.generation fine).network.coarseConfiguration
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1))) edge.val = true := by
      rw [coarseIdentity]
      exact edge.property
    exact mul_nonneg (inv_nonneg.mpr (pow_pos scalePositive _).le)
      ((coarseResistance_positive (rule.generation fine).network
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)))
        (fun _ => 1) (fun _ => zero_lt_one) ⟨edge.val, retained⟩).le)
  have convergence := pairResistance_tendsto
    (network (rule.generation coarse).network (configuration coarse))
    (fun fine edge => (scale ^ (coarse + fine + 2))⁻¹ * unitConfigurationResistance (rule.generation fine).network
      (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge.val))
    limitResistance weightNonnegative limitNonnegative childConvergence first last
  apply convergence.congr'
  exact Eventually.of_forall (fun fine =>
    (actual_block_scaled_resistance_trace rule configuration coherent coarse fine _
      (inv_nonneg.mpr (pow_pos scalePositive _).le) first last reachable).symm)

end
end IGSIII34.ResistanceLimit
