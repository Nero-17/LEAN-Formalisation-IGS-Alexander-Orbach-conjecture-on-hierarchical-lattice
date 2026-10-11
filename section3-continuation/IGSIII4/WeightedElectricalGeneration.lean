import IGSIII34.Percolation.ElectricalTransfer
import IGSIII.Chemical.SubstitutionPaths.WeightedGeneration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII34.Resistance IGSIII34.Resistance.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability

theorem generation_weightedResistance_recursion (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (crossing : (rule.generation (depth + 1)).network.crosses configuration = true)
    (cost : Fin (rule.generation (depth + 1)).edges → ℝ)
    (positive : ∀ edge, 0 < cost edge) :
    electricalCell (rule.generation (depth + 1)).network configuration cost =
      electricalCell rule.network (generationRootConfiguration rule depth configuration)
        (fun edge => electricalCell (rule.generation depth).network
          (generationTopCells rule depth configuration edge)
          (fun child => cost ((rule.generationTopDecomposition depth).edge.symm
            (finProdFinEquiv (edge, child))))) := by
  have coarseCrossing : rule.network.crosses (generationRootConfiguration rule depth configuration) = true :=
    (generation_root_crosses rule depth configuration).trans crossing
  have relabel := networkEquivalence_resistance (rule.generationTopDecomposition depth)
    configuration crossing (fun edge => cost edge.val) (fun edge => positive edge.val)
  change (network (rule.network.substitute (rule.generation depth).network)
    ((rule.generationTopDecomposition depth).configuration configuration)).effectiveResistance
      (fun edge => cost ((rule.generationTopDecomposition depth).edge.symm edge.val)) = _ at relabel
  rw [← configuration_of_topCells rule depth configuration] at relabel
  have recursion := actual_substitution_resistance rule.network (rule.generation depth).network
    (generationTopCells rule depth configuration) coarseCrossing
    (fun edge => cost ((rule.generationTopDecomposition depth).edge.symm
      (finProdFinEquiv (edge.1, edge.2.val))))
    (fun edge => positive _)
  have pullbackIdentity :
      (fun edge => cost ((rule.generationTopDecomposition depth).edge.symm
        (finProdFinEquiv
          (((substitutionOpenEdgeEquiv (generationTopCells rule depth configuration)).symm edge).1,
            ((substitutionOpenEdgeEquiv (generationTopCells rule depth configuration)).symm edge).2.val)))) =
      (fun edge => cost ((rule.generationTopDecomposition depth).edge.symm edge.val)) := by
    funext edge
    exact congrArg (fun leaf => cost ((rule.generationTopDecomposition depth).edge.symm leaf))
      (congrArg Subtype.val ((substitutionOpenEdgeEquiv (generationTopCells rule depth configuration)).apply_symm_apply edge))
  rw [pullbackIdentity] at recursion
  exact relabel.symm.trans recursion

theorem electricalCell_depends_open {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (first second : Fin edges → ℝ)
    (same : ∀ edge, configuration edge = true → first edge = second edge) :
    electricalCell network configuration first = electricalCell network configuration second := by
  unfold electricalCell
  congr 1
  funext edge
  exact same edge.val edge.property

theorem electricalTransfer_iterate_eq_weighted_actual (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (positive : ∀ marks, 0 < value marks)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (electricalTransfer rule)^[depth + 1] value (innovationTreeShift rule address marks) =
      electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth address true)
        (fun leaf => value (innovationTreeShift rule
          (address ++ generationEdgeAddress rule depth leaf) marks)) := by
  induction depth generalizing address with
  | zero =>
      change electricalCell rule.network (marks (address ++ [], true))
        (fun edge => value (innovationTreeShift rule [edge] (innovationTreeShift rule address marks))) = _
      simp only [List.append_nil, innovationTreeShift_append, generationEdgeAddress,
        Rule.generation, markedGenerationConfiguration]
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', electricalTransfer,
        generation_weightedResistance_recursion rule depth _
          (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) address true)
          _ (fun _ => positive _),
        markedGenerationConfiguration_root rule marks crossing,
        markedGenerationConfiguration_topCells]
      simp only [innovationTreeShift, List.append_nil]
      apply electricalCell_depends_open
      intro edge retained
      rw [retained]
      have childIdentity := inductionHypothesis (address ++ [edge])
      rw [← innovationTreeShift_append] at childIdentity
      refine childIdentity.trans ?_
      congr 1
      funext child
      rw [generationEdgeAddress_top]
      simp only [List.append_assoc, List.singleton_append]

end
end IGSIII4
