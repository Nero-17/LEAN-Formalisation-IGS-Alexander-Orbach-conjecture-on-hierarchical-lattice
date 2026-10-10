import IGSIII34.AO.PerronRow
import Universality.Arithmetic.GraphAlgebraicity

/-!
# Strict mass-growth comparison for the actual classical IGS II matrix

The matrix, positive Perron vector and off-diagonal positivity are obtained
from the actual rule's graph geometry at an interior parameter. No abstract
positive eigenvector is required as an extra hypothesis of the result.
-/

set_option autoImplicit false

namespace Universality.Rule
noncomputable section

open FiniteNetwork Matrix

theorem Classical.mass_spectralRadius_strictly_gt_connected_entry
    {rule : Rule} (classicalRule : rule.Classical)
    {probability : ℝ} (positive : 0 < probability) (belowOne : probability < 1) :
    rule.network.massMatrix probability .connected .connected <
      (spectralRadius ℂ ((rule.network.massMatrix probability).map Complex.ofReal)).toReal := by
  obtain ⟨_, vector, positiveVector, eigenvector⟩ :=
    classicalRule.mass_spectralRadius_positive_eigenvector probability positive belowOne
  have rowEquation (state : LiveState) :
      ∑ child, rule.network.massMatrix probability state child * vector child =
        (spectralRadius ℂ ((rule.network.massMatrix probability).map Complex.ofReal)).toReal * vector state := by
    have equation := congrFun eigenvector state
    simpa only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using equation
  have blockPositive := (rule.network.massPlaneBlock_pos_of_geometry positive belowOne
    (classicalRule.connected _) classicalRule.scale classicalRule.cut).1
  have secondColumn : 0 < 2 * rule.network.massMatrix probability .connected .both +
      rule.network.massMatrix probability .connected .single := blockPositive 0 1
  by_cases bothPositive : 0 < rule.network.massMatrix probability .connected .both
  · exact IGSIII34.AO.perron_strictly_above_diagonal (rule.network.massMatrix probability)
      vector (rule.network.massMatrix_nonneg positive.le belowOne.le) positiveVector
      rowEquation (by decide : LiveState.both ≠ .connected) bothPositive
  · have singlePositive : 0 < rule.network.massMatrix probability .connected .single := by
      have bothNonpositive := le_of_not_gt bothPositive
      linarith
    exact IGSIII34.AO.perron_strictly_above_diagonal (rule.network.massMatrix probability)
      vector (rule.network.massMatrix_nonneg positive.le belowOne.le) positiveVector
      rowEquation (by decide : LiveState.single ≠ .connected) singlePositive

end
end Universality.Rule
