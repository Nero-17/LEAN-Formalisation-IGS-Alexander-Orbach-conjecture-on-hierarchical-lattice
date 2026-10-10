import IGSIII34.Percolation.ElectricalTransfer
import IGSIII.Chemical.SubstitutionPaths.BlockConditioning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution
open scoped BigOperators

theorem networkEquivalence_unit_resistance
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges) :
    unitConfigurationResistance second (equivalence.configuration configuration) =
      unitConfigurationResistance first configuration := by
  by_cases crosses : first.crosses configuration = true
  · exact networkEquivalence_resistance equivalence configuration crosses (fun _ => 1) (fun _ => zero_lt_one)
  · have secondDoesNotCross : second.crosses (equivalence.configuration configuration) ≠ true := by
      rw [equivalence.crosses]
      exact crosses
    exact (electricalCell_eq_zero_of_not_crosses second _ secondDoesNotCross _).trans
      (electricalCell_eq_zero_of_not_crosses first _ crosses _).symm

theorem unitResistance_substitution_all
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges) :
    unitConfigurationResistance (outer.substitute inner) (substitutionConfigurationEquiv cells) =
      electricalCell outer (inner.coarseConfiguration cells)
        (fun edge => unitConfigurationResistance inner (cells edge)) := by
  by_cases crosses : outer.crosses (inner.coarseConfiguration cells) = true
  · exact actual_substitution_resistance outer inner cells crosses (fun _ => 1) (fun _ => zero_lt_one)
  · have fineDoesNotCross : (outer.substitute inner).crosses (substitutionConfigurationEquiv cells) ≠ true := by
      rw [outer.substitute_crosses]
      exact crosses
    exact (electricalCell_eq_zero_of_not_crosses (outer.substitute inner) _ fineDoesNotCross _).trans
      (electricalCell_eq_zero_of_not_crosses outer _ crosses _).symm

theorem conditional_substitution_resistance_observable
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (parameter : ℝ) (positive : 0 < inner.reliability parameter) (belowOne : inner.reliability parameter < 1)
    (response : ℝ → ℝ) :
    (∑ configuration : Configuration (outerEdges * innerEdges),
      (outer.substitute inner).conditionalCellWeight parameter true configuration *
        response (unitConfigurationResistance (outer.substitute inner) configuration)) =
      ∑ coarse : Configuration outerEdges,
        outer.conditionalCellWeight (inner.reliability parameter) true coarse *
          ∑ cells : Fin outerEdges → Configuration innerEdges,
            (∏ edge, inner.conditionalCellWeight parameter (coarse edge) (cells edge)) *
              response (electricalCell outer coarse (fun edge => unitConfigurationResistance inner (cells edge))) := by
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [unitResistance_substitution_all]
  exact outer.conditional_substitution_observable inner parameter positive belowOne true
    (fun coarse cells => response (electricalCell outer coarse
      (fun edge => unitConfigurationResistance inner (cells edge))))

theorem generation_block_resistance_observable (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ)
    (response : ℝ → ℝ) :
    (∑ configuration : Configuration (rule.generation (coarse + fine + 1)).edges,
      (rule.generation (coarse + fine + 1)).network.conditionalCellWeight parameter true configuration *
        response (unitConfigurationResistance (rule.generation (coarse + fine + 1)).network configuration)) =
      ∑ outerConfiguration : Configuration (rule.generation coarse).edges,
        (rule.generation coarse).network.conditionalCellWeight parameter true outerConfiguration *
          ∑ cells : Fin (rule.generation coarse).edges → Configuration (rule.generation fine).edges,
            (∏ edge, (rule.generation fine).network.conditionalCellWeight parameter (outerConfiguration edge) (cells edge)) *
              response (electricalCell (rule.generation coarse).network outerConfiguration
                (fun edge => unitConfigurationResistance (rule.generation fine).network (cells edge))) := by
  have law := conditional_substitution_resistance_observable (rule.generation coarse).network
    (rule.generation fine).network parameter
    (by rwa [rule.generation_fixed_point parameter fixedPoint])
    (by rwa [rule.generation_fixed_point parameter fixedPoint]) response
  rw [← (rule.generationBlockDecomposition coarse fine).configuration.sum_comp] at law
  simpa only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_unit_resistance,
    rule.generation_fixed_point parameter fixedPoint] using law

end
end IGSIII34.Percolation
