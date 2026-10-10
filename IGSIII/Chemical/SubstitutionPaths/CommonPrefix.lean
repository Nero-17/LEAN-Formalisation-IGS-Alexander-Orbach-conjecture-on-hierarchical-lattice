import IGSIII.Chemical.SubstitutionPaths.BlockConditioning
import IGSIII.Chemical.SubstitutionPaths.InnovationCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

/-! The extracted block configuration is the fixed earlier configuration
on the same innovation sample. In particular the block conditional mean
depends on a fixed finite prefix, independently of the remaining depth. -/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory

theorem generationBlockCells_apply (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 1)).edges)
    (edge : Fin (rule.generation coarse).edges) (child : Fin (rule.generation fine).edges) :
    generationBlockCells rule coarse fine configuration edge child =
      configuration ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child))) := rfl

theorem generationBlockCells_succ_apply (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 2)).edges)
    (edge : Fin (rule.generation coarse).edges) (child : Fin (rule.generation fine).edges)
    (leaf : Fin rule.edges) :
    generationBlockCells rule coarse (fine + 1) configuration edge (finProdFinEquiv (child, leaf)) =
      configuration (finProdFinEquiv
        ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf)) := by
  rw [generationBlockCells_apply]
  apply congrArg configuration
  apply (rule.generationBlockDecomposition coarse (fine + 1)).edge.injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (edge, finProdFinEquiv (child, leaf)) =
    substitutionAssociatorEdge (finProdFinEquiv
      (Prod.map (rule.generationBlockDecomposition coarse fine).edge id
        (finProdFinEquiv.symm (finProdFinEquiv
          ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf)))))
  rw [Equiv.symm_apply_apply]
  change _ = substitutionAssociatorEdge (finProdFinEquiv
    ((rule.generationBlockDecomposition coarse fine).edge
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child))), leaf))
  rw [Equiv.apply_symm_apply, substitutionAssociatorEdge_apply]

theorem generationBlockCells_coarsen (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 2)).edges)
    (edge : Fin (rule.generation coarse).edges) :
    generationBlockCells rule coarse fine (rule.coarsenGeneration (coarse + fine + 1) configuration) edge =
      rule.coarsenGeneration fine (generationBlockCells rule coarse (fine + 1) configuration edge) := by
  funext child
  rw [generationBlockCells_apply]
  change rule.network.crosses (fun leaf => configuration (finProdFinEquiv
      ((rule.generationBlockDecomposition coarse fine).edge.symm (finProdFinEquiv (edge, child)), leaf))) =
    rule.network.crosses (fun leaf =>
      generationBlockCells rule coarse (fine + 1) configuration edge (finProdFinEquiv (child, leaf)))
  congr 1
  funext leaf
  exact (generationBlockCells_succ_apply rule coarse fine configuration edge child leaf).symm

theorem generationBlockCoarse_zero (rule : Rule) (coarse : ℕ)
    (configuration : Configuration (rule.generation (coarse + 1)).edges) :
    generationBlockCoarse rule coarse 0 configuration = rule.coarsenGeneration coarse configuration := rfl

theorem generationBlockCoarse_coarsen (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse + fine + 2)).edges) :
    generationBlockCoarse rule coarse (fine + 1) configuration =
      generationBlockCoarse rule coarse fine (rule.coarsenGeneration (coarse + fine + 1) configuration) := by
  funext edge
  change (rule.generation (fine + 1)).network.crosses
      (generationBlockCells rule coarse (fine + 1) configuration edge) =
    (rule.generation fine).network.crosses
      (generationBlockCells rule coarse fine (rule.coarsenGeneration (coarse + fine + 1) configuration) edge)
  rw [generation_crosses_coarsen, generationBlockCells_coarsen]

theorem generationBlockCoarse_of_coherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (coarse fine : ℕ) :
    generationBlockCoarse rule coarse fine (configuration (coarse + fine + 1)) = configuration coarse := by
  induction fine with
  | zero => exact coherent coarse
  | succ fine inductionHypothesis =>
      rw [generationBlockCoarse_coarsen]
      change generationBlockCoarse rule coarse fine
        (rule.coarsenGeneration (coarse + fine + 1) (configuration ((coarse + fine + 1) + 1))) = _
      rw [coherent (coarse + fine + 1)]
      exact inductionHypothesis

theorem marked_generationBlockCoarse_eq (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (address : List (Fin rule.edges)) (opened : Bool) (coarse fine : ℕ) :
    generationBlockCoarse rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) =
        markedGenerationConfiguration rule marks coarse address opened :=
  generationBlockCoarse_of_coherent rule
    (fun depth => markedGenerationConfiguration rule marks depth address opened)
    (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth address opened) coarse fine

theorem marked_generationBlockCoarse_eq_ae (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ address opened coarse fine, generationBlockCoarse rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) =
          markedGenerationConfiguration rule marks coarse address opened := by
  filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint] with marks crossing
  exact fun address opened coarse fine => marked_generationBlockCoarse_eq rule marks crossing address opened coarse fine

end IGSIII.Chemical.Substitution
