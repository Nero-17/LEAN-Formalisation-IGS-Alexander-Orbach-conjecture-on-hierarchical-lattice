import IGSIII34.ResistanceLimit.ActualCellLocalisation
import IGSIII34.ResistanceLimit.ActualBlockZeroEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem networkEquivalence_pairResistance_weighted
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (resistance : Fin firstEdges → ℝ) (positive : ∀ edge, configuration edge = true → 0 < resistance edge)
    (initial terminal : Fin firstVertices) :
    pairResistance (network second (equivalence.configuration configuration))
      (fun edge => resistance (equivalence.edge.symm edge.val))
      (equivalence.vertex initial) (equivalence.vertex terminal) =
    pairResistance (network first configuration) (fun edge => resistance edge.val) initial terminal := by
  exact pairResistance_reindex (network first configuration)
    (network second (equivalence.configuration configuration)) equivalence.vertex
    (networkEquivalenceOpenEdges equivalence configuration) (fun edge => equivalence.endpoint edge.val)
    (fun edge => resistance edge.val) (fun edge => positive edge.val edge.property) initial terminal

/-- The original finite block map uses the same weighted resistance as the
actual substitution; all labels are transported by its canonical equivalence. -/
theorem actualBlock_pairResistance_transport (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (resistance : Fin (rule.generation (coarse + fine + 1)).edges → ℝ)
    (positive : ∀ edge, configuration edge = true → 0 < resistance edge)
    (chosen : Fin (rule.generation coarse).edges) (first last : Fin (rule.generation fine).vertices) :
    pairResistance (network ((rule.generation coarse).network.substitute (rule.generation fine).network)
      (substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration)))
      (fun edge => resistance ((rule.generationBlockDecomposition coarse fine).edge.symm edge.val))
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network chosen first))
      (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network chosen last)) =
    pairResistance (network (rule.generation (coarse + fine + 1)).network configuration)
      (fun edge => resistance edge.val)
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex last) := by
  have configurationIdentity : (rule.generationBlockDecomposition coarse fine).configuration configuration =
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  have transported := networkEquivalence_pairResistance_weighted (rule.generationBlockDecomposition coarse fine)
    configuration resistance positive ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex last)
  rw [configurationIdentity] at transported
  simpa only [generationBlockCellEmbedding, NetworkEmbedding.trans, NetworkEmbedding.ofEquivalence,
    cellNetworkEmbedding, NetworkEquivalence.symm, Function.Embedding.trans_apply,
    Function.Embedding.coeFn_mk, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using transported

theorem actualBlockComponentResistance_positive (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (resistance : Fin (rule.generation (coarse + fine + 1)).edges → ℝ)
    (positive : ∀ edge, configuration edge = true → 0 < resistance edge)
    (edge : Σ chosen : Fin (rule.generation coarse).edges,
      {child : Fin (rule.generation fine).edges // generationBlockCells rule coarse fine configuration chosen child = true}) :
    0 < resistance ((generationBlockCellEmbedding rule coarse fine edge.1).edge edge.2.val) := by
  apply positive
  exact edge.2.property

/-- A crossing actual finite block has a genuine inverse electrical bound;
the finite coarse boundary factor will be fixed by stationary trace response. -/
theorem actualBlock_component_resistance_lower_bound (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (resistance : Fin (rule.generation (coarse + fine + 1)).edges → ℝ)
    (positive : ∀ edge, configuration edge = true → 0 < resistance edge)
    (chosen : Fin (rule.generation coarse).edges)
    (crossing : (rule.generation fine).network.crosses (generationBlockCells rule coarse fine configuration chosen) = true)
    (first last : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration chosen)).Reachable first last) :
    pairResistance (network (rule.generation fine).network (generationBlockCells rule coarse fine configuration chosen))
      (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) first last ≤
      (1 + cellBoundaryTestEnergy (rule.generation coarse).network (rule.generation fine).network
        (generationBlockCells rule coarse fine configuration)
        (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine edge.1).edge edge.2.val)) chosen *
        (network (rule.generation fine).network (generationBlockCells rule coarse fine configuration chosen)).effectiveResistance
          (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val))) *
      pairResistance (network (rule.generation (coarse + fine + 1)).network configuration) (fun edge => resistance edge.val)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
        ((generationBlockCellEmbedding rule coarse fine chosen).vertex last) := by
  have comparison := actual_substituted_cell_resistance_lower_bound
    (rule.generation coarse).network (rule.generation fine).network (generationBlockCells rule coarse fine configuration)
    (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine edge.1).edge edge.2.val))
    (actualBlockComponentResistance_positive rule coarse fine configuration resistance positive) chosen crossing first last reachable
  have weights (edge : {edge : Fin ((rule.generation coarse).edges * (rule.generation fine).edges) //
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) edge = true}) :
      resistance ((generationBlockCellEmbedding rule coarse fine
        ((substitutionOpenEdgeEquiv (generationBlockCells rule coarse fine configuration)).symm edge).1).edge
        ((substitutionOpenEdgeEquiv (generationBlockCells rule coarse fine configuration)).symm edge).2.val) =
      resistance ((rule.generationBlockDecomposition coarse fine).edge.symm edge.val) := by
    have reconstruction := congrArg Subtype.val ((substitutionOpenEdgeEquiv
      (generationBlockCells rule coarse fine configuration)).apply_symm_apply edge)
    change finProdFinEquiv _ = edge.val at reconstruction
    change resistance ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv _)) = _
    rw [reconstruction]
  simp_rw [weights] at comparison
  rw [actualBlock_pairResistance_transport rule coarse fine configuration resistance positive chosen first last] at comparison
  exact comparison

/-- The original global resistance on one B side equals its intrinsic block
resistance. The two planted sides are kept separate throughout. -/
theorem actualBlock_dangling_component_pairResistance_eq (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (resistance : Fin (rule.generation (coarse + fine + 1)).edges → ℝ)
    (positive : ∀ edge, configuration edge = true → 0 < resistance edge)
    (chosen : Fin (rule.generation coarse).edges)
    (noncrossing : (rule.generation fine).network.crosses (generationBlockCells rule coarse fine configuration chosen) = false)
    (sourceSide : Bool) (first last : Fin (rule.generation fine).vertices)
    (firstRetained : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration chosen)).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) first)
    (lastRetained : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine configuration chosen)).Reachable
      (plantedVertex (rule.generation fine).network sourceSide) last) :
    pairResistance (network (rule.generation (coarse + fine + 1)).network configuration) (fun edge => resistance edge.val)
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex first)
      ((generationBlockCellEmbedding rule coarse fine chosen).vertex last) =
    pairResistance (network (rule.generation fine).network (generationBlockCells rule coarse fine configuration chosen))
      (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine chosen).edge edge.val)) first last := by
  have comparison := actual_substituted_dangling_cell_pairResistance_eq
    (rule.generation coarse).network (rule.generation fine).network (generationBlockCells rule coarse fine configuration)
    (fun edge => resistance ((generationBlockCellEmbedding rule coarse fine edge.1).edge edge.2.val))
    (actualBlockComponentResistance_positive rule coarse fine configuration resistance positive) chosen noncrossing sourceSide first last
    (by simpa only [graph_eq_openGraph, sideNetwork_network_source] using firstRetained)
    (by simpa only [graph_eq_openGraph, sideNetwork_network_source] using lastRetained)
  have weights (edge : {edge : Fin ((rule.generation coarse).edges * (rule.generation fine).edges) //
      substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) edge = true}) :
      resistance ((generationBlockCellEmbedding rule coarse fine
        ((substitutionOpenEdgeEquiv (generationBlockCells rule coarse fine configuration)).symm edge).1).edge
        ((substitutionOpenEdgeEquiv (generationBlockCells rule coarse fine configuration)).symm edge).2.val) =
      resistance ((rule.generationBlockDecomposition coarse fine).edge.symm edge.val) := by
    have reconstruction := congrArg Subtype.val ((substitutionOpenEdgeEquiv
      (generationBlockCells rule coarse fine configuration)).apply_symm_apply edge)
    change finProdFinEquiv _ = edge.val at reconstruction
    change resistance ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv _)) = _
    rw [reconstruction]
  simp_rw [weights] at comparison
  rw [actualBlock_pairResistance_transport rule coarse fine configuration resistance positive chosen first last] at comparison
  exact comparison

end
end IGSIII34.Diffusion
