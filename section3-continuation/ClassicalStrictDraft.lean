import IGSIII34.Percolation.ElectricalTransfer
import IGSIII34.Resistance.StrictPath
import Universality.Graph.ClassicalRule

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution

def indexedResistanceCost {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (input : Fin edges → ℝ) (bond : Sym2 (Fin vertices)) : ℝ :=
  ∑ edge, if s((rule.endpoint edge).1, (rule.endpoint edge).2) = bond then input edge else 0

theorem indexedResistanceCost_at_endpoint {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((rule.endpoint edge).1, (rule.endpoint edge).2)))
    (input : Fin edges → ℝ) (edge : Fin edges) :
    indexedResistanceCost rule input s((rule.endpoint edge).1, (rule.endpoint edge).2) = input edge := by
  classical
  unfold indexedResistanceCost
  rw [Finset.sum_eq_single edge]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (fun equality => different (simple equality))
  · simp

theorem indexedResistanceCost_nonnegative {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    {input : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge) (bond : Sym2 (Fin vertices)) :
    0 ≤ indexedResistanceCost rule input bond := by
  apply Finset.sum_nonneg
  intro edge _
  split_ifs
  · exact nonnegative edge
  · exact le_rfl

theorem electricalCell_le_chemical_cost {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((rule.endpoint edge).1, (rule.endpoint edge).2)))
    (configuration : Configuration edges) (crosses : rule.crosses configuration = true)
    (input : Fin edges → ℝ) (nonnegative : ∀ edge, 0 ≤ input edge) :
    electricalCell rule configuration input ≤ weightedDistance (rule.openGraph configuration)
      (indexedResistanceCost rule input) rule.source rule.target := by
  have bound := (network rule configuration).effectiveResistance_le_weightedDistance
    (connected_of_crosses _ _ crosses) (fun edge => input edge.val) (fun edge => nonnegative edge.val)
    (indexedResistanceCost rule input) (fun edge => (indexedResistanceCost_at_endpoint rule simple input edge.val).symm)
  rw [graph_eq_openGraph] at bound
  exact bound

theorem classical_allOpen_deletion_connected (rule : Rule) (classical : rule.Classical)
    (removed : {edge : Fin rule.edges // (fun _ => true) edge = true}) :
    ((network rule.network (fun _ => true)).graphWithoutEdge removed).Reachable
      rule.network.source rule.network.target := by
  rw [graphWithoutEdge_eq_updated_openGraph]
  have updateIdentity : Function.update (fun _ : Fin rule.edges => true) removed.val false = onlyClosed removed.val := by
    funext edge
    by_cases same : edge = removed.val
    · subst edge
      simp [onlyClosed]
    · simp [onlyClosed, Function.update_of_ne same, same]
  rw [updateIdentity]
  exact (rule.network.crosses_eq_true _).mp (classical.cut removed.val)

theorem classical_allOpen_resistance_strict (rule : Rule) (classical : rule.Classical)
    (input : Fin rule.edges → ℝ) (positive : ∀ edge, 0 < input edge) :
    electricalCell rule.network (fun _ => true) input <
      weightedDistance rule.network.fullGraph (indexedResistanceCost rule.network input)
        rule.network.source rule.network.target := by
  have connected : (network rule.network (fun _ => true)).graph.Reachable
      (network rule.network (fun _ => true)).source (network rule.network (fun _ => true)).target := by
    rw [graph_eq_openGraph]
    exact classical.connected _
  have bound := (network rule.network (fun _ => true)).effectiveResistance_lt_weightedDistance connected
    (classical_allOpen_deletion_connected rule classical) (fun edge => input edge.val)
    (fun edge => positive edge.val) (indexedResistanceCost rule.network input)
    (fun edge => (indexedResistanceCost_at_endpoint rule.network classical.simple input edge.val).symm)
  rw [graph_eq_openGraph] at bound
  exact bound

end
end IGSIII34.Percolation
