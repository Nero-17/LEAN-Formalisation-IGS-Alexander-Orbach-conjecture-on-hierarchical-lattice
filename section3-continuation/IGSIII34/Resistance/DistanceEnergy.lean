import IGSIII34.Resistance.Dirichlet
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.NormNum

/-!
# The finite distance–core-size–resistance inequality

For every connected terminal pair with unit edge resistances, the square of
graph distance is bounded by edge count times effective resistance. The proof
uses the actual graph distance as a test potential; no path-flow decomposition
or bound on its total absolute current is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem sourceDistance_edge_difference_le_one (network : FiniteNetwork Vertex Edge)
    (edge : Edge) :
    |(network.graph.dist network.source (network.endpoint edge).1 : ℝ) -
      (network.graph.dist network.source (network.endpoint edge).2 : ℝ)| ≤ 1 := by
  by_cases endpointsEqual : (network.endpoint edge).1 = (network.endpoint edge).2
  · simp [endpointsEqual]
  · have adjacent : network.graph.Adj (network.endpoint edge).1 (network.endpoint edge).2 :=
      ⟨endpointsEqual, edge, Or.inl rfl⟩
    have forward := adjacent.reachable.dist_triangle_right network.source
    have backward := adjacent.symm.reachable.dist_triangle_right network.source
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent] at forward
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr adjacent.symm] at backward
    have forwardReal : (network.graph.dist network.source (network.endpoint edge).2 : ℝ) ≤
        (network.graph.dist network.source (network.endpoint edge).1 : ℝ) + 1 := by
      exact_mod_cast forward
    have backwardReal : (network.graph.dist network.source (network.endpoint edge).1 : ℝ) ≤
        (network.graph.dist network.source (network.endpoint edge).2 : ℝ) + 1 := by
      exact_mod_cast backward
    rw [abs_le]
    constructor <;> linarith

theorem sourceDistance_potentialEnergy_le_edge_count (network : FiniteNetwork Vertex Edge) :
    network.potentialEnergy (fun _ => 1) (fun vertex => (network.graph.dist network.source vertex : ℝ)) ≤
      (Fintype.card Edge : ℝ) := by
  calc
    _ ≤ ∑ _ : Edge, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro edge _
      have bound := network.sourceDistance_edge_difference_le_one edge
      simp only [div_one]
      nlinarith [sq_abs ((network.graph.dist network.source (network.endpoint edge).1 : ℝ) -
        (network.graph.dist network.source (network.endpoint edge).2 : ℝ)),
        abs_nonneg ((network.graph.dist network.source (network.endpoint edge).1 : ℝ) -
          (network.graph.dist network.source (network.endpoint edge).2 : ℝ))]
    _ = _ := by simp

theorem distance_sq_le_edge_count_mul_unitResistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    (network.graph.dist network.source network.target : ℝ) ^ 2 ≤
      (Fintype.card Edge : ℝ) * network.effectiveResistance (fun _ => 1) := by
  obtain ⟨current, unitFlow, minimal⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected (fun _ => zero_lt_one)
  have cauchy := network.weighted_cauchy_schwarz (fun _ => zero_lt_one) current
    (fun vertex => (network.graph.dist network.source vertex : ℝ))
  rw [network.unitFlow_integrationByParts unitFlow
    (fun vertex => (network.graph.dist network.source vertex : ℝ))] at cauchy
  simp only [SimpleGraph.dist_self, Nat.cast_zero, zero_sub, neg_sq] at cauchy
  calc
    _ ≤ energy (fun _ => 1) current * network.potentialEnergy (fun _ => 1)
        (fun vertex => (network.graph.dist network.source vertex : ℝ)) := cauchy
    _ ≤ energy (fun _ => 1) current * (Fintype.card Edge : ℝ) :=
      mul_le_mul_of_nonneg_left network.sourceDistance_potentialEnergy_le_edge_count
        (energy_nonneg (fun _ => zero_le_one) current)
    _ = _ := by rw [minimal, mul_comm]

end
end IGSIII34.Resistance.FiniteNetwork
