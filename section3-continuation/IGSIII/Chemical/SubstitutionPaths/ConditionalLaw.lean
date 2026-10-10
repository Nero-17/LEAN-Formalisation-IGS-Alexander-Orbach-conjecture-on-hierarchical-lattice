import IGSIII.Chemical.SubstitutionPaths.CoherentHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Conditional law of the actual chemical distance

These identities hold for every real-valued test function. They combine the
proved graph distance formula with IGS II's full conditional cell law. The
product on the right is the existing conditional configuration product, so
independence between different children is retained without assuming it as a
distance-recursion certificate.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open scoped BigOperators

/-- Full top-down disintegration of an actual generation, retaining the root
configuration and all child configurations, under either conditioning state. -/
theorem generation_root_children_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : Configuration rule.edges →
      (Fin rule.edges → Configuration (rule.generation depth).edges) → ℝ) :
    (∑ fine : Configuration (rule.generation (depth + 1)).edges,
      (rule.generation (depth + 1)).network.conditionalCellWeight p opened fine *
        response (generationRootConfiguration rule depth fine) (generationTopCells rule depth fine)) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p opened coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response coarse cells := by
  have law := rule.network.conditional_substitution_observable (rule.generation depth).network p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) opened response
  rw [← (generationTopCellsEquiv rule depth).sum_comp] at law
  change (∑ fine, (rule.network.substitute (rule.generation depth).network).conditionalCellWeight
    p opened (substitutionConfigurationEquiv (generationTopCells rule depth fine)) *
      response (generationRootConfiguration rule depth fine) (generationTopCells rule depth fine)) = _ at law
  simp_rw [configuration_of_topCells,
    NetworkEquivalence.conditionalCellWeight, rule.generation_fixed_point p fixedPoint] at law
  exact law

/-- The same disintegration for the actual complete history. It applies to
arbitrary joint observables, and therefore retains the conditional product
law of the children rather than only their one-dimensional distances. -/
theorem history_root_children_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) (depth : ℕ)
    (response : Configuration rule.edges →
      (Fin rule.edges → rule.ConfigurationHistory depth) → ℝ) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p opened (depth + 1) history *
        response (historyRootConfiguration rule depth history) (historyChildHistory rule depth history)) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p opened coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response coarse (fun edge => Rule.ConfigurationHistory.ofFine rule depth (cells edge)) := by
  rw [Rule.ConfigurationHistory.joint_observable_law rule p positive lessOne fixedPoint]
  change (∑ fine, (rule.generation (depth + 1)).network.conditionalCellWeight p opened fine *
    response (generationRootConfiguration rule depth fine)
      (fun edge => Rule.ConfigurationHistory.ofFine rule depth (generationTopCells rule depth fine edge))) = _
  exact
      generation_root_children_observable rule p positive lessOne fixedPoint opened depth
        (fun coarse cells => response coarse
          (fun edge => Rule.ConfigurationHistory.ofFine rule depth (cells edge)))

theorem conditional_substitution_distance_observable
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (p : ℝ) (positive : 0 < inner.reliability p) (lessOne : inner.reliability p < 1)
    (response : ℝ → ℝ) :
    (∑ fine : Configuration (outerEdges * innerEdges),
      (outer.substitute inner).conditionalCellWeight p true fine *
        response (((outer.substitute inner).openGraph fine).dist
          (outer.substitute inner).source (outer.substitute inner).target : ℝ)) =
      ∑ coarse : Configuration outerEdges,
        outer.conditionalCellWeight (inner.reliability p) true coarse *
          ∑ cells : Fin outerEdges → Configuration innerEdges,
            (∏ edge, inner.conditionalCellWeight p (coarse edge) (cells edge)) *
              response (cellMinPlus outer inner coarse cells) := by
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [substitute_distance_eq_cellMinPlus outer inner simple]
  exact outer.conditional_substitution_observable inner p positive lessOne true
    (fun coarse cells => response (cellMinPlus outer inner coarse cells))

/-- The actual conditioned distance at generation `depth + 1` has the
min-plus law with the actual child generation's conditional configuration law.
At a reliability fixed point the root innovation law is independent of depth. -/
theorem generation_conditioned_distance_observable (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (response : ℝ → ℝ) :
    (∑ fine : Configuration (rule.generation (depth + 1)).edges,
      (rule.generation (depth + 1)).network.conditionalCellWeight p true fine *
        response (((rule.generation (depth + 1)).network.openGraph fine).dist
          (rule.generation (depth + 1)).network.source
          (rule.generation (depth + 1)).network.target : ℝ)) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response (cellMinPlus rule.network (rule.generation depth).network coarse cells) := by
  have law := conditional_substitution_distance_observable rule.network
    (rule.generation depth).network simple p
    (by rwa [rule.generation_fixed_point p fixedPoint])
    (by rwa [rule.generation_fixed_point p fixedPoint]) response
  rw [← (rule.generationTopDecomposition depth).configuration.sum_comp] at law
  simpa only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_terminal_distance_all,
    rule.generation_fixed_point p fixedPoint] using law

/-- The same law for the finest distance in the real joint configuration
history, using IGS II's equality of the complete recursive and direct laws. -/
theorem history_conditioned_distance_observable (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth : ℕ) (response : ℝ → ℝ) :
    (∑ history : rule.ConfigurationHistory (depth + 1),
      Rule.ConfigurationHistory.recursiveWeight rule p true (depth + 1) history *
        response (((rule.generation (depth + 1)).network.openGraph
          (Rule.ConfigurationHistory.latest rule (depth + 1) history)).dist
            (rule.generation (depth + 1)).network.source
            (rule.generation (depth + 1)).network.target : ℝ)) =
      ∑ coarse : Configuration rule.edges, rule.network.conditionalCellWeight p true coarse *
        ∑ cells : Fin rule.edges → Configuration (rule.generation depth).edges,
          (∏ edge, (rule.generation depth).network.conditionalCellWeight p (coarse edge) (cells edge)) *
            response (cellMinPlus rule.network (rule.generation depth).network coarse cells) := by
  rw [Rule.ConfigurationHistory.joint_observable_law rule p positive lessOne fixedPoint]
  simp only [Rule.ConfigurationHistory.latest_ofFine]
  exact generation_conditioned_distance_observable rule simple p positive lessOne fixedPoint depth response

end IGSIII.Chemical.Substitution
