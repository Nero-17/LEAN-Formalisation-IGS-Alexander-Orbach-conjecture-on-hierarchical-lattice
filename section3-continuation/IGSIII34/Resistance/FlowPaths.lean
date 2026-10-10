import IGSIII34.Resistance.FiniteNetwork
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Graph connectivity supplies genuine Kirchhoff unit flows. The proof builds a
signed edge current for each step of a graph walk and adds these currents;
there is no flow-existence certificate among the network fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork

noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def graph (network : FiniteNetwork Vertex Edge) : SimpleGraph Vertex where
  Adj first second := first ≠ second ∧ ∃ edge,
    network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first)
  symm := ⟨by
    rintro first second ⟨distinct, edge, orientation⟩
    exact ⟨distinct.symm, edge, orientation.symm⟩⟩
  loopless := ⟨by intro vertex adjacency; exact adjacency.1 rfl⟩

def flowBetween (network : FiniteNetwork Vertex Edge) (first second : Vertex)
    (current : Edge → ℝ) : Prop :=
  ∀ vertex, network.divergence current vertex =
    (if vertex = first then 1 else 0) - (if vertex = second then 1 else 0)

theorem divergence_add (network : FiniteNetwork Vertex Edge) (first second : Edge → ℝ)
    (vertex : Vertex) :
    network.divergence (fun edge => first edge + second edge) vertex =
      network.divergence first vertex + network.divergence second vertex := by
  simp only [divergence, add_mul, Finset.sum_add_distrib]

theorem divergence_neg (network : FiniteNetwork Vertex Edge) (current : Edge → ℝ)
    (vertex : Vertex) :
    network.divergence (fun edge => -current edge) vertex =
      -network.divergence current vertex := by
  simp only [divergence, neg_mul, Finset.sum_neg_distrib]

theorem divergence_scale (network : FiniteNetwork Vertex Edge) (current : Edge → ℝ)
    (scalar : ℝ) (vertex : Vertex) :
    network.divergence (fun edge => scalar * current edge) vertex =
      scalar * network.divergence current vertex := by
  simp only [divergence, mul_assoc, Finset.mul_sum]

theorem unitFlow_add_zero_divergence (network : FiniteNetwork Vertex Edge)
    {current perturbation : Edge → ℝ}
    (unitFlow : current ∈ network.unitFlows)
    (zeroDivergence : ∀ vertex, network.divergence perturbation vertex = 0)
    (scalar : ℝ) :
    (fun edge => current edge + scalar * perturbation edge) ∈ network.unitFlows := by
  intro vertex
  rw [network.divergence_add, network.divergence_scale, zeroDivergence, mul_zero, add_zero]
  exact unitFlow vertex

theorem divergence_single (network : FiniteNetwork Vertex Edge) (edge : Edge)
    (vertex : Vertex) :
    network.divergence (fun index => if index = edge then 1 else 0) vertex =
      (if vertex = (network.endpoint edge).1 then 1 else 0) -
        (if vertex = (network.endpoint edge).2 then 1 else 0) := by
  simp [divergence, eq_comm]

theorem flowBetween_add (network : FiniteNetwork Vertex Edge)
    {first middle last : Vertex} {firstCurrent secondCurrent : Edge → ℝ}
    (firstFlow : network.flowBetween first middle firstCurrent)
    (secondFlow : network.flowBetween middle last secondCurrent) :
    network.flowBetween first last (fun edge => firstCurrent edge + secondCurrent edge) := by
  intro vertex
  rw [network.divergence_add, firstFlow vertex, secondFlow vertex]
  ring

theorem exists_flowBetween_of_adjacent (network : FiniteNetwork Vertex Edge)
    {first second : Vertex} (adjacent : network.graph.Adj first second) :
    ∃ current, network.flowBetween first second current := by
  obtain ⟨_, edge, orientation⟩ := adjacent
  rcases orientation with forward | backward
  · refine ⟨fun index => if index = edge then 1 else 0, ?_⟩
    intro vertex
    rw [network.divergence_single, forward]
  · refine ⟨fun index => -(if index = edge then 1 else 0), ?_⟩
    intro vertex
    rw [network.divergence_neg, network.divergence_single, backward]
    dsimp
    ring

theorem exists_flowBetween_of_walk (network : FiniteNetwork Vertex Edge)
    {first second : Vertex} (walk : network.graph.Walk first second) :
    ∃ current, network.flowBetween first second current := by
  induction walk with
  | nil =>
      refine ⟨fun _ => 0, ?_⟩
      intro vertex
      simp [divergence]
  | @cons first middle last adjacency walk inductionHypothesis =>
      obtain ⟨firstCurrent, firstFlow⟩ := network.exists_flowBetween_of_adjacent adjacency
      obtain ⟨secondCurrent, secondFlow⟩ := inductionHypothesis
      exact ⟨_, network.flowBetween_add firstFlow secondFlow⟩

theorem unitFlows_nonempty_of_connected (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    network.unitFlows.Nonempty := by
  obtain ⟨walk⟩ := connected
  exact network.exists_flowBetween_of_walk walk

end
end IGSIII34.Resistance.FiniteNetwork
