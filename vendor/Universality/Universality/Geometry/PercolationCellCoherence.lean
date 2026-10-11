import Universality.Geometry.PercolationCellSelection

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem percolationCellConfiguration_succ (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 2)).edges)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) (leaf : Fin rule.edges) :
    rule.percolationCellConfiguration (depth + 1) configuration edge
      (finProdFinEquiv (child, leaf)) =
    configuration (finProdFinEquiv
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf)) := by
  simp [percolationCellConfiguration, generationTopDecomposition,
    NetworkEquivalence.configuration, NetworkEquivalence.trans,
    NetworkEquivalence.substitute, NetworkEquivalence.substituteEdge,
    NetworkEquivalence.refl, substitutionAssociativity, substitutionAssociatorEdge,
    substitutionConfigurationEquiv]
  erw [Equiv.symm_apply_apply]
  congr 2
  apply Prod.ext
  · exact congrArg (fun x => (rule.generationTopDecomposition depth).edge.symm
      (finProdFinEquiv (edge, x)))
      (congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (child, leaf)))
  · have hleaf : (finProdFinEquiv (child, leaf)).modNat = leaf :=
      congrArg (fun pair : Fin (rule.generation depth).edges × Fin rule.edges => pair.2)
        (finProdFinEquiv.symm_apply_apply (child, leaf))
    exact hleaf

/-- Reassociation commutes with the actual percolation coarse-graining map. -/
theorem percolationCellConfiguration_coarsen (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 2)).edges) (edge : Fin rule.edges) :
    rule.coarsenGeneration depth (rule.percolationCellConfiguration (depth + 1) configuration edge) =
      rule.percolationCellConfiguration depth (rule.coarsenGeneration (depth + 1) configuration) edge := by
  funext child
  change rule.network.crosses (fun leaf =>
    rule.percolationCellConfiguration (depth + 1) configuration edge
      (finProdFinEquiv (child, leaf))) = _
  simp_rw [percolationCellConfiguration_succ]
  rfl

/-- Each child inherits a coherent infinite percolation configuration, rather than an assumed one. -/
theorem percolationCellConfiguration_coherent (rule : Rule)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (edge : Fin rule.edges) :
    ∀ n, rule.coarsenGeneration n
        (rule.percolationCellConfiguration (n + 1) (configuration (n + 2)) edge) =
      rule.percolationCellConfiguration n (configuration (n + 1)) edge := by
  intro n
  rw [percolationCellConfiguration_coarsen, hcoarsen]

theorem generation_crosses_coarsen (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges) :
    (rule.generation (depth + 1)).network.crosses configuration =
      (rule.generation depth).network.crosses (rule.coarsenGeneration depth configuration) := by
  have h := (rule.generation depth).network.substitute_crosses rule.network
    (substitutionConfigurationEquiv.symm configuration)
  change ((rule.generation depth).network.substitute rule.network).crosses configuration = _
  simpa only [Equiv.apply_symm_apply, coarsenGeneration] using h

theorem coherent_generation_crosses (rule : Rule)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (depth : ℕ) :
    (rule.generation depth).network.crosses (configuration depth) =
      rule.network.crosses (configuration 0) := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [generation_crosses_coarsen, hcoarsen, ih]

theorem percolationCell_coarseConfiguration (rule : Rule)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (depth : ℕ) :
    (rule.generation depth).network.coarseConfiguration
      (rule.percolationCellConfiguration depth (configuration (depth + 1))) = configuration 0 := by
  funext edge
  change (rule.generation depth).network.crosses
    (rule.percolationCellConfiguration depth (configuration (depth + 1)) edge) = _
  have h := coherent_generation_crosses rule
    (fun n => rule.percolationCellConfiguration n (configuration (n + 1)) edge)
    (rule.percolationCellConfiguration_coherent configuration hcoarsen edge) depth
  refine h.trans ?_
  have hzero := congrFun (hcoarsen 0) edge
  exact hzero

theorem percolationCellState_eq (rule : Rule)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (depth : ℕ) (sourceSelected targetSelected : Bool) (edge : Fin rule.edges) :
    rule.percolationCellState depth (configuration (depth + 1)) sourceSelected targetSelected edge =
      rule.network.orientedChildState sourceSelected targetSelected (configuration 0) edge := by
  unfold percolationCellState
  rw [percolationCell_coarseConfiguration rule configuration hcoarsen]

end
end Universality.Rule
