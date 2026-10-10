import IGSIII.Chemical.SubstitutionPaths.WeightedSubstitution
import IGSIII.Chemical.SubstitutionPaths.WeightedRelabelling
import IGSIII.Chemical.TransferIteration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability

theorem generation_weighted_shortest_recursion (rule : Rule) (classical : rule.Classical)
    (depth : ℕ) (configuration : Configuration (rule.generation (depth + 1)).edges)
    (crossing : (rule.generation (depth + 1)).network.crosses configuration = true)
    (cost : Fin (rule.generation (depth + 1)).edges → ℝ) :
    (edgePathFamily (rule.generation (depth + 1)).network configuration).shortest cost =
      (edgePathFamily rule.network (generationRootConfiguration rule depth configuration)).shortest
        (fun edge => (edgePathFamily (rule.generation depth).network
          (generationTopCells rule depth configuration edge)).shortest
          (fun child => cost ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))))) := by
  have substituteSimple := rule.network.substitute_simple (rule.generation depth).network
    (classical.generation depth).simple (classical.generation depth).scale
  have transport := networkEquivalence_edgePathFamily_shortest (rule.generationTopDecomposition depth)
    (classical.generation (depth + 1)).simple substituteSimple configuration crossing cost
  rw [← transport, ← configuration_of_topCells]
  exact substitute_edgePathFamily_shortest rule.network (rule.generation depth).network classical.simple
    (classical.generation depth).simple substituteSimple (generationTopCells rule depth configuration)
    ((generation_root_crosses rule depth configuration).trans crossing) _

noncomputable def generationEdgeAddress (rule : Rule) : (depth : ℕ) → Fin (rule.generation depth).edges → List (Fin rule.edges)
  | 0, edge => [edge]
  | depth + 1, leaf =>
      let pair := finProdFinEquiv.symm ((rule.generationTopDecomposition depth).edge leaf)
      pair.1 :: generationEdgeAddress rule depth pair.2

theorem generationEdgeAddress_top (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    generationEdgeAddress rule (depth + 1)
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))) =
        edge :: generationEdgeAddress rule depth child := by
  simp only [generationEdgeAddress, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem generationEdgeAddress_length (rule : Rule) (depth : ℕ) (leaf : Fin (rule.generation depth).edges) :
    (generationEdgeAddress rule depth leaf).length = depth + 1 := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [generationEdgeAddress, List.length_cons, inductionHypothesis]

theorem generationEdgeAddress_injective (rule : Rule) (depth : ℕ) :
    Function.Injective (generationEdgeAddress rule depth) := by
  induction depth with
  | zero => intro first second equality; exact (List.cons.inj equality).1
  | succ depth inductionHypothesis =>
      intro first second equality
      have parts := List.cons.inj equality
      apply (rule.generationTopDecomposition depth).edge.injective
      apply finProdFinEquiv.symm.injective
      exact Prod.ext parts.1 (inductionHypothesis parts.2)

theorem chemicalTransfer_iterate_eq_weighted_actual (rule : Rule) (classical : rule.Classical)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    (chemicalTransfer rule)^[depth + 1] value (innovationTreeShift rule address marks) =
      (edgePathFamily (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth address true)).shortest
          (fun leaf => value (innovationTreeShift rule (address ++ generationEdgeAddress rule depth leaf) marks)) := by
  induction depth generalizing address with
  | zero =>
      change (edgePathFamily rule.network (marks (address ++ [], true))).shortest
        (fun edge => value (innovationTreeShift rule [edge] (innovationTreeShift rule address marks))) = _
      simp only [List.append_nil, innovationTreeShift_append, generationEdgeAddress, Rule.generation,
        markedGenerationConfiguration]
  | succ depth inductionHypothesis =>
      rw [Function.iterate_succ_apply', chemicalTransfer,
        generation_weighted_shortest_recursion rule classical depth _
          (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) address true),
        markedGenerationConfiguration_root rule marks crossing,
        markedGenerationConfiguration_topCells]
      simp only [innovationTreeShift, List.append_nil]
      apply edgePathFamily_shortest_depends_open rule.network classical.simple (marks (address, true))
      intro edge retained
      rw [retained]
      have childIdentity := inductionHypothesis (address ++ [edge])
      rw [← innovationTreeShift_append] at childIdentity
      refine childIdentity.trans ?_
      congr 1
      funext child
      rw [generationEdgeAddress_top]
      simp only [List.append_assoc, List.singleton_append]

theorem chemicalTransfer_iterate_eq_weighted_actual_ae (rule : Rule) (classical : rule.Classical)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint,
      ∀ depth address,
        (chemicalTransfer rule)^[depth + 1] value (innovationTreeShift rule address marks) =
          (edgePathFamily (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth address true)).shortest
              (fun leaf => value (innovationTreeShift rule (address ++ generationEdgeAddress rule depth leaf) marks)) := by
  filter_upwards [independentInnovationLaw_crosses rule p positive lessOne fixedPoint] with marks crossing
  exact fun depth address => chemicalTransfer_iterate_eq_weighted_actual rule classical value marks crossing depth address

end IGSIII.Chemical.Substitution
