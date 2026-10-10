import IGSIII34.Percolation.ElectricalTransfer
import IGSIII.Chemical.SubstitutionPaths.WeightedGeneration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution

theorem electricalCell_depends_open {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (first second : Fin edges → ℝ) (equal : ∀ edge, configuration edge = true → first edge = second edge) :
    electricalCell network configuration first = electricalCell network configuration second := by
  unfold electricalCell
  congr 1
  funext edge
  exact equal edge.val edge.property

theorem networkEquivalence_weighted_resistance
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (crosses : first.crosses configuration = true) (input : Fin firstEdges → ℝ)
    (positive : ∀ edge, 0 < input edge) :
    electricalCell second (equivalence.configuration configuration) (fun edge => input (equivalence.edge.symm edge)) =
      electricalCell first configuration input := by
  exact networkEquivalence_resistance equivalence configuration crosses (fun edge => input edge.val)
    (fun edge => positive edge.val)

theorem weighted_resistance_substitution
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges)
    (crosses : outer.crosses (inner.coarseConfiguration cells) = true)
    (input : Fin (outerEdges*innerEdges) → ℝ) (positive : ∀ edge, 0 < input edge) :
    electricalCell (outer.substitute inner) (substitutionConfigurationEquiv cells) input =
      electricalCell outer (inner.coarseConfiguration cells)
        (fun edge => electricalCell inner (cells edge) (fun child => input (finProdFinEquiv (edge, child)))) := by
  have identity := actual_substitution_resistance outer inner cells crosses
    (fun edge => input (finProdFinEquiv (edge.1, edge.2.val))) (fun edge => positive _)
  have reconstruction (edge : {edge : Fin (outerEdges*innerEdges) // substitutionConfigurationEquiv cells edge = true}) :
      finProdFinEquiv (((substitutionOpenEdgeEquiv cells).symm edge).1,
        ((substitutionOpenEdgeEquiv cells).symm edge).2.val) = edge.val :=
    congrArg Subtype.val ((substitutionOpenEdgeEquiv cells).apply_symm_apply edge)
  simp_rw [reconstruction] at identity
  exact identity

theorem generation_weighted_resistance_recursion (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth+1)).edges)
    (crosses : (rule.generation (depth+1)).network.crosses configuration = true)
    (input : Fin (rule.generation (depth+1)).edges → ℝ) (positive : ∀ edge, 0 < input edge) :
    electricalCell (rule.generation (depth+1)).network configuration input =
      electricalCell rule.network (generationRootConfiguration rule depth configuration)
        (fun edge => electricalCell (rule.generation depth).network (generationTopCells rule depth configuration edge)
          (fun child => input ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))))) := by
  have transport := networkEquivalence_weighted_resistance (rule.generationTopDecomposition depth)
    configuration crosses input positive
  rw [← transport, ← configuration_of_topCells]
  exact weighted_resistance_substitution rule.network (rule.generation depth).network
    (generationTopCells rule depth configuration) ((generation_root_crosses rule depth configuration).trans crosses)
    _ (fun edge => positive _)

theorem electricalTransfer_iterate_eq_weighted_actual (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (valuePositive : ∀ address, 0 < value (innovationTreeShift rule address marks))
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (electricalTransfer rule)^[depth+1] value (innovationTreeShift rule address marks) =
      electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth address true)
        (fun leaf => value (innovationTreeShift rule (address ++ generationEdgeAddress rule depth leaf) marks)) := by
  induction depth generalizing address with
  | zero =>
      change electricalCell rule.network (marks (address ++ [], true))
        (fun edge => value (innovationTreeShift rule [edge] (innovationTreeShift rule address marks))) = _
      simp only [List.append_nil, innovationTreeShift_append, generationEdgeAddress, Rule.generation, markedGenerationConfiguration]
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', electricalTransfer,
        generation_weighted_resistance_recursion rule depth _
          (markedGenerationConfiguration_crosses rule marks crossing (depth+1) address true)
          _ (fun leaf => valuePositive _),
        markedGenerationConfiguration_root rule marks crossing, markedGenerationConfiguration_topCells]
      simp only [innovationTreeShift, List.append_nil]
      apply electricalCell_depends_open rule.network (marks (address, true))
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
end IGSIII34.Percolation
