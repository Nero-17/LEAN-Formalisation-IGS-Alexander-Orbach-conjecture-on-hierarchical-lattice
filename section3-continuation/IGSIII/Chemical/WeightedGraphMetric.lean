import IGSIII.Chemical.SubstitutionPaths.WeightedDistance
import IGSIII.Chemical.PathBounds
import Mathlib.Topology.MetricSpace.Basic

/-!
# The genuine metric of a finite positive weighted graph

The distance is the minimum cost of actual simple paths. Connectivity and
strict positivity of the edge costs are the only geometric assumptions.
The metric axioms are proved, rather than supplied as certificate fields.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

theorem weightedDistance_reverse_le (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    {source target : Vertex} (reachable : graph.Reachable source target) :
    weightedDistance graph cost target source ≤ weightedDistance graph cost source target := by
  obtain ⟨walk, _, minimizing⟩ := exists_weighted_geodesic graph cost reachable
  calc
    weightedDistance graph cost target source ≤ (walk.reverse.edges.map cost).sum :=
      weightedDistance_le_walkCost graph cost nonnegative walk.reverse
    _ = (walk.edges.map cost).sum := by
      rw [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
    _ = weightedDistance graph cost source target := minimizing

theorem weightedDistance_comm (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (source target : Vertex) :
    weightedDistance graph cost source target = weightedDistance graph cost target source := by
  classical
  by_cases reachable : graph.Reachable source target
  · exact le_antisymm
      (weightedDistance_reverse_le graph cost nonnegative reachable.symm)
      (weightedDistance_reverse_le graph cost nonnegative reachable)
  · have reverseUnreachable : ¬ graph.Reachable target source :=
      fun reverse => reachable reverse.symm
    simp [weightedDistance, reachable, reverseUnreachable]

theorem weightedDistance_triangle (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    {first middle last : Vertex} (firstReachable : graph.Reachable first middle)
    (lastReachable : graph.Reachable middle last) :
    weightedDistance graph cost first last ≤
      weightedDistance graph cost first middle + weightedDistance graph cost middle last := by
  obtain ⟨firstWalk, _, firstMinimizing⟩ := exists_weighted_geodesic graph cost firstReachable
  obtain ⟨lastWalk, _, lastMinimizing⟩ := exists_weighted_geodesic graph cost lastReachable
  calc
    weightedDistance graph cost first last ≤ ((firstWalk.append lastWalk).edges.map cost).sum :=
      weightedDistance_le_walkCost graph cost nonnegative (firstWalk.append lastWalk)
    _ = (firstWalk.edges.map cost).sum + (lastWalk.edges.map cost).sum := by
      rw [SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]
    _ = weightedDistance graph cost first middle + weightedDistance graph cost middle last := by
      rw [firstMinimizing, lastMinimizing]

theorem eq_of_weightedDistance_eq_zero_of_edge_positive (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (positive : ∀ edge ∈ graph.edgeSet, 0 < cost edge)
    {source target : Vertex} (reachable : graph.Reachable source target)
    (zeroDistance : weightedDistance graph cost source target = 0) : source = target := by
  rw [weightedDistance_of_reachable graph cost reachable] at zeroDistance
  obtain ⟨edges, membership, zeroEdges⟩ :=
    ((graphPathFamily graph source target reachable).shortest_eq_zero_iff
      nonnegative).mp zeroDistance
  obtain ⟨walk, simple, rfl⟩ :=
    (mem_graphPathFamily graph source target reachable edges).mp membership
  have empty : walk.edges.toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge edgeMembership
    exact (positive edge (walk.edges_subset_edgeSet (List.mem_toFinset.mp edgeMembership))).ne'
      (zeroEdges edge edgeMembership)
  have zeroLength : walk.length = 0 := by
    rw [← simplePath_edgeSet_card walk simple, empty]
    rfl
  exact (SimpleGraph.Walk.length_eq_zero_iff.mp zeroLength).eq

theorem eq_of_weightedDistance_eq_zero (graph : SimpleGraph Vertex)
    (cost : Sym2 Vertex → ℝ) (positive : ∀ edge, 0 < cost edge)
    {source target : Vertex} (reachable : graph.Reachable source target)
    (zeroDistance : weightedDistance graph cost source target = 0) : source = target :=
  eq_of_weightedDistance_eq_zero_of_edge_positive graph cost (fun edge => (positive edge).le)
    (fun edge _ => positive edge) reachable zeroDistance

@[reducible] noncomputable def positiveWeightedGraphMetricOnEdges (graph : SimpleGraph Vertex)
    (reachable : ∀ first second, graph.Reachable first second)
    (cost : Sym2 Vertex → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (positive : ∀ edge ∈ graph.edgeSet, 0 < cost edge) : MetricSpace Vertex where
  dist := weightedDistance graph cost
  dist_self source := weightedDistance_self graph cost nonnegative source
  dist_comm source target := weightedDistance_comm graph cost nonnegative source target
  dist_triangle first middle last := weightedDistance_triangle graph cost nonnegative
    (reachable first middle) (reachable middle last)
  eq_of_dist_eq_zero := fun {first second} zeroDistance =>
    eq_of_weightedDistance_eq_zero_of_edge_positive graph cost nonnegative positive
      (reachable first second) zeroDistance

@[reducible] noncomputable def positiveWeightedGraphMetric (graph : SimpleGraph Vertex)
    (reachable : ∀ first second, graph.Reachable first second)
    (cost : Sym2 Vertex → ℝ) (positive : ∀ edge, 0 < cost edge) : MetricSpace Vertex where
  dist := weightedDistance graph cost
  dist_self source := weightedDistance_self graph cost (fun edge => (positive edge).le) source
  dist_comm source target :=
    weightedDistance_comm graph cost (fun edge => (positive edge).le) source target
  dist_triangle first middle last := weightedDistance_triangle graph cost
    (fun edge => (positive edge).le) (reachable first middle) (reachable middle last)
  eq_of_dist_eq_zero := fun {first second} zeroDistance =>
    eq_of_weightedDistance_eq_zero graph cost positive (reachable first second) zeroDistance

end IGSIII.Chemical.Substitution
