import IGSIII34.Percolation.GenerationResistance
import IGSIII34.Percolation.ConnectedResistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped BigOperators

theorem electricalCell_normalized_children
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (parameter : ℝ) (meanPositive : 0 < conditionalMeanResistance inner parameter)
    (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) :
    electricalCell outer coarse (fun edge => normalizedConfigurationResistance inner parameter (cells edge)) =
      electricalCell outer coarse (fun edge => unitConfigurationResistance inner (cells edge)) /
        conditionalMeanResistance inner parameter := by
  have nonnegative (edge : Fin outerEdges) : 0 ≤ unitConfigurationResistance inner (cells edge) :=
    (network inner (cells edge)).effectiveResistance_nonnegative_all (fun _ => zero_le_one)
  have equality := electricalCell_scale outer coarse nonnegative (inv_nonneg.mpr meanPositive.le)
  simpa only [normalizedConfigurationResistance, div_eq_mul_inv, mul_comm] using equality

theorem normalized_substitution_resistance_observable
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (parameter : ℝ) (positive : 0 < inner.reliability parameter) (belowOne : inner.reliability parameter < 1)
    (meanPositive : 0 < conditionalMeanResistance inner parameter) (response : ℝ → ℝ) :
    finiteMean ((outer.substitute inner).conditionalCellWeight parameter true)
      (fun configuration => response (unitConfigurationResistance (outer.substitute inner) configuration /
        conditionalMeanResistance inner parameter)) =
      finiteMean (outer.conditionalCellWeight (inner.reliability parameter) true) (fun coarse =>
        finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight parameter true))
          (fun cells => response (electricalCell outer coarse
            (fun edge => positiveNormalizedResistance inner parameter (cells edge))))) := by
  have law := conditional_substitution_resistance_observable outer inner parameter positive belowOne
    (fun value => response (value / conditionalMeanResistance inner parameter))
  change _ = finiteMean (outer.conditionalCellWeight (inner.reliability parameter) true) (fun coarse =>
    finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight parameter (coarse edge)))
      (fun cells => response (electricalCell outer coarse (fun edge => unitConfigurationResistance inner (cells edge)) /
        conditionalMeanResistance inner parameter))) at law
  refine law.trans ?_
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro coarse _
  congr 1
  have transport := actual_child_electrical_connected_product outer inner parameter positive belowOne coarse response
  simp_rw [electricalCell_normalized_children outer inner parameter meanPositive] at transport
  exact transport

theorem normalized_generation_block_resistance_observable (rule : Rule)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ)
    (meanPositive : 0 < conditionalMeanResistance (rule.generation fine).network parameter)
    (response : ℝ → ℝ) :
    finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
      (fun configuration => response (unitConfigurationResistance (rule.generation (coarse+fine+1)).network configuration /
        conditionalMeanResistance (rule.generation fine).network parameter)) =
      finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            response (electricalCell (rule.generation coarse).network outerConfiguration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))))) := by
  have law := normalized_substitution_resistance_observable (rule.generation coarse).network
    (rule.generation fine).network parameter
    (by rwa [rule.generation_fixed_point parameter fixedPoint])
    (by rwa [rule.generation_fixed_point parameter fixedPoint]) meanPositive response
  unfold finiteMean at law ⊢
  rw [← (rule.generationBlockDecomposition coarse fine).configuration.sum_comp] at law
  simpa only [NetworkEquivalence.conditionalCellWeight, networkEquivalence_unit_resistance,
    rule.generation_fixed_point parameter fixedPoint] using law

end
end IGSIII34.Percolation
