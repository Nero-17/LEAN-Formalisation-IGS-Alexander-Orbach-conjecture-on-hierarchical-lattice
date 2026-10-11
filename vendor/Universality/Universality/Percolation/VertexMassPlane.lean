import Universality.Percolation.VertexMassResponse
import Universality.Matrix.MassPlane

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem internalSelectedMass_disconnected (configuration : Configuration edges)
    (hdisconnected : R.crosses configuration = false) :
    R.internalSelectedMass true true configuration =
      R.internalSelectedMass true false configuration + R.internalSelectedMass false true configuration := by
  unfold internalSelectedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro vertex _
  have hnotboth : ¬ ((R.openGraph configuration).Reachable R.source vertex.val ∧
      (R.openGraph configuration).Reachable R.target vertex.val) := by
    rintro ⟨hs, ht⟩
    have hc := (R.crosses_eq_true configuration).mpr (hs.trans ht.symm)
    rw [hdisconnected] at hc
    contradiction
  cases hs : (R.openGraph configuration).reachableDecide R.source vertex.val <;>
    cases ht : (R.openGraph configuration).reachableDecide R.target vertex.val <;>
    simp only [selectedActive, hs, ht, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
  · exact False.elim (hnotboth ⟨(SimpleGraph.reachableDecide_eq_true _ _ _).mp hs,
      (SimpleGraph.reachableDecide_eq_true _ _ _).mp ht⟩)

theorem conditionalInternalMean_disconnected (p : ℝ) :
    R.conditionalInternalMean p false true true =
      R.conditionalInternalMean p false true false + R.conditionalInternalMean p false false true := by
  unfold conditionalInternalMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro configuration _
  by_cases hcross : R.crosses configuration = false
  · rw [R.internalSelectedMass_disconnected configuration hcross, Nat.cast_add, mul_add]
  · simp [conditionalCellWeight, hcross]

theorem conditionalVertexMass_both (p : ℝ) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    R.conditionalVertexMass p .both = 2 * R.conditionalVertexMass p .single := by
  change R.conditionalInternalMean p false true true = 2 * R.conditionalInternalMean p false true false
  rw [R.conditionalInternalMean_disconnected,
    symmetry.conditionalInternalMean_swap hs ht p false false true]
  ring

theorem conditionalVertexMass_in_massPlane (p : ℝ) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source) :
    R.conditionalVertexMass p = massPlaneLift
      ![R.conditionalVertexMass p .connected, R.conditionalVertexMass p .single] := by
  funext state
  cases state <;> simp only [massPlaneLift, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact R.conditionalVertexMass_both p symmetry hs ht

end
end Universality.FiniteNetwork
