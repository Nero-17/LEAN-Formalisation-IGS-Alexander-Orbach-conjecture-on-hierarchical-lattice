import IGSIII34.Percolation.EigenlawInterval
import IGSIII.Chemical.SubstitutionPaths.ConnectedProductLaw
import IGSIII34.Probability.FiniteProductTensorization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped BigOperators

def normalizedConfigurationResistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ)
    (configuration : Configuration edges) : ℝ :=
  unitConfigurationResistance network configuration / conditionalMeanResistance network parameter

def positiveNormalizedResistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ)
    (configuration : Configuration edges) : ℝ :=
  if network.crosses configuration then normalizedConfigurationResistance network parameter configuration else 1

theorem positiveNormalizedResistance_positive {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ)
    (meanPositive : 0 < conditionalMeanResistance network parameter) (configuration : Configuration edges) :
    0 < positiveNormalizedResistance network parameter configuration := by
  by_cases crossing : network.crosses configuration = true
  · simp only [positiveNormalizedResistance, crossing, ↓reduceIte, normalizedConfigurationResistance]
    exact div_pos ((IGSIII34.Percolation.network network configuration).effectiveResistance_pos_of_connected
      (connected_of_crosses network configuration crossing) (fun _ => zero_lt_one)) meanPositive
  · simp [positiveNormalizedResistance, crossing]

theorem positiveNormalizedResistance_observable {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (parameter : ℝ) (response : ℝ → ℝ) :
    finiteMean (network.conditionalCellWeight parameter true)
      (fun configuration => response (positiveNormalizedResistance network parameter configuration)) =
      finiteMean (network.conditionalCellWeight parameter true)
        (fun configuration => response (normalizedConfigurationResistance network parameter configuration)) := by
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases crossing : network.crosses configuration = true
  · simp [positiveNormalizedResistance, crossing]
  · simp [Universality.FiniteNetwork.conditionalCellWeight, crossing]

theorem electricalCell_congr_open {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (first second : Fin edges → ℝ)
    (same : ∀ edge, configuration edge = true → first edge = second edge) :
    electricalCell network configuration first = electricalCell network configuration second := by
  unfold electricalCell
  congr 1
  funext edge
  exact same edge.val edge.property

theorem actual_child_electrical_connected_product
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (parameter : ℝ) (positive : 0 < inner.reliability parameter) (belowOne : inner.reliability parameter < 1)
    (coarse : Configuration outerEdges) (response : ℝ → ℝ) :
    finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight parameter (coarse edge)))
      (fun cells => response (electricalCell outer coarse
        (fun edge => normalizedConfigurationResistance inner parameter (cells edge)))) =
      finiteMean (tupleWeight (fun _ : Fin outerEdges => inner.conditionalCellWeight parameter true))
        (fun cells => response (electricalCell outer coarse
          (fun edge => positiveNormalizedResistance inner parameter (cells edge)))) := by
  classical
  calc
    _ = finiteMean (tupleWeight (fun edge => inner.conditionalCellWeight parameter (coarse edge)))
        (fun cells => response (electricalCell outer coarse
          (fun edge => positiveNormalizedResistance inner parameter (cells edge)))) := by
      unfold finiteMean
      apply Finset.sum_congr rfl
      intro cells _
      by_cases zero : tupleWeight (fun edge => inner.conditionalCellWeight parameter (coarse edge)) cells = 0
      · simp [zero]
      · have resistanceEquality : electricalCell outer coarse
            (fun edge => normalizedConfigurationResistance inner parameter (cells edge)) =
            electricalCell outer coarse (fun edge => positiveNormalizedResistance inner parameter (cells edge)) := by
          apply electricalCell_congr_open
          intro edge opened
          have crossing : inner.crosses (cells edge) = true := by
            by_contra disconnected
            apply zero
            change (∏ edge, inner.conditionalCellWeight parameter (coarse edge) (cells edge)) = 0
            apply Finset.prod_eq_zero (Finset.mem_univ edge)
            simp [opened, Universality.FiniteNetwork.conditionalCellWeight, disconnected]
          simp [positiveNormalizedResistance, crossing]
        exact congrArg (fun value => tupleWeight
          (fun edge => inner.conditionalCellWeight parameter (coarse edge)) cells * response value) resistanceEquality
    _ = _ := finite_product_replace_unused (Outcome := Configuration innerEdges) (count := outerEdges)
      (fun edge => inner.conditionalCellWeight parameter (coarse edge))
      (fun _ : Fin outerEdges => inner.conditionalCellWeight parameter true)
      (fun edge => inner.sum_conditionalCellWeight parameter positive belowOne (coarse edge))
      (fun _ => inner.sum_conditionalCellWeight parameter positive belowOne true) coarse (fun _ => false)
      (fun edge opened => by rw [opened]) _ (by
        intro first second same
        apply congrArg response
        exact electricalCell_congr_open outer coarse _ _
          (fun edge opened => congrArg (positiveNormalizedResistance inner parameter) (same edge opened)))

end
end IGSIII34.Percolation
