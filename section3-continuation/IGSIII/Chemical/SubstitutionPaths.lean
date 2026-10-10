import Universality.Graph.Substitution
import IGSIII.Chemical.SubstitutionPaths.WeightedDistance

set_option autoImplicit false

/-!
# Paths in actual percolated edge substitutions

This module uses the actual glued graph of IGS II. Its cell interiors are
disjoint, and only the two terminals of a cell are identified with old vertices.
The configuration in each cell may be different. We first lift local terminal
geodesics and coarse walks, retaining explicit length bounds.

The reverse comparison is proved by extending a weighted coarse distance into
each actual child graph. No distance identity is a field of an assumed
certificate. Iteration of the one-step graph identity remains a separate bridge.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges)
variable (inner : FiniteNetwork innerVertices innerEdges)

/-- A crossing cell has a lifted terminal geodesic of exactly its intrinsic
terminal distance, even if other cells supply shortcuts outside it. -/
theorem cell_geodesic_lifts
    (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (crossing : inner.crosses (configuration edge) = true) :
    ∃ walk : (outer.substitutedGraph inner configuration).Walk
        (Sum.inl (outer.endpoint edge).1) (Sum.inl (outer.endpoint edge).2),
      walk.length = (inner.openGraph (configuration edge)).dist inner.source inner.target := by
  have reachable := (inner.crosses_eq_true (configuration edge)).mp crossing
  obtain ⟨localWalk, length⟩ := reachable.exists_walk_length_eq_dist
  let mapped := localWalk.map (outer.cellHom inner configuration edge)
  refine ⟨mapped.copy (outer.cellVertex_source inner edge)
    (outer.cellVertex_target inner edge), ?_⟩
  simpa only [SimpleGraph.Walk.length_copy, mapped, SimpleGraph.Walk.length_map] using length

/-- A weight on a coarse bond dominates the intrinsic distance of each crossing
cell with those endpoints. This condition refers only to the actual child graphs. -/
theorem coarse_adjacency_lifts
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (Fin outerVertices) → ℕ)
    (costBound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤
        cost s((outer.endpoint edge).1, (outer.endpoint edge).2))
    {source target : Fin outerVertices}
    (adjacent : (outer.openGraph (inner.coarseConfiguration configuration)).Adj source target) :
    ∃ walk : (outer.substitutedGraph inner configuration).Walk
        (Sum.inl source) (Sum.inl target),
      walk.length ≤ cost s(source, target) := by
  obtain ⟨_, edge, crossing, endpoints | endpoints⟩ := adjacent
  · obtain ⟨walk, length⟩ := cell_geodesic_lifts outer inner configuration edge crossing
    have first : (outer.endpoint edge).1 = source := congrArg Prod.fst endpoints
    have second : (outer.endpoint edge).2 = target := congrArg Prod.snd endpoints
    refine ⟨walk.copy (congrArg Sum.inl first) (congrArg Sum.inl second), ?_⟩
    rw [SimpleGraph.Walk.length_copy, length]
    simpa only [endpoints] using costBound edge crossing
  · obtain ⟨walk, length⟩ := cell_geodesic_lifts outer inner configuration edge crossing
    have first : (outer.endpoint edge).1 = target := congrArg Prod.fst endpoints
    have second : (outer.endpoint edge).2 = source := congrArg Prod.snd endpoints
    refine ⟨walk.reverse.copy (congrArg Sum.inl second) (congrArg Sum.inl first), ?_⟩
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_reverse, length]
    simpa only [endpoints, Sym2.eq_swap] using costBound edge crossing

/-- A genuine coarse walk lifts to a fine walk whose length is at most the sum
of its coarse bond costs, counted with multiplicity. -/
theorem coarse_walk_lifts
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (Fin outerVertices) → ℕ)
    (costBound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤
        cost s((outer.endpoint edge).1, (outer.endpoint edge).2))
    {source target : Fin outerVertices}
    (coarseWalk : (outer.openGraph (inner.coarseConfiguration configuration)).Walk source target) :
    ∃ walk : (outer.substitutedGraph inner configuration).Walk
        (Sum.inl source) (Sum.inl target),
      walk.length ≤ (coarseWalk.edges.map cost).sum := by
  induction coarseWalk with
  | nil => exact ⟨.nil, by simp⟩
  | cons adjacent rest inductionHypothesis =>
      obtain ⟨first, firstBound⟩ :=
        coarse_adjacency_lifts outer inner configuration cost costBound adjacent
      obtain ⟨last, lastBound⟩ := inductionHypothesis
      refine ⟨first.append last, ?_⟩
      simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.edges_cons,
        List.map_cons, List.sum_cons] using Nat.add_le_add firstBound lastBound

theorem substituted_distance_le_walk_cost
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (Fin outerVertices) → ℕ)
    (costBound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤
        cost s((outer.endpoint edge).1, (outer.endpoint edge).2))
    {source target : Fin outerVertices}
    (coarseWalk : (outer.openGraph (inner.coarseConfiguration configuration)).Walk source target) :
    (outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) ≤
      (coarseWalk.edges.map cost).sum := by
  obtain ⟨walk, lengthBound⟩ :=
    coarse_walk_lifts outer inner configuration cost costBound coarseWalk
  exact (SimpleGraph.dist_le walk).trans lengthBound

/-- The usual uniform upper bound is a consequence of the actual walk lift. -/
theorem substituted_distance_le_coarse_distance_mul
    (configuration : Fin outerEdges → Configuration innerEdges) (upper : ℕ)
    (cellBound : ∀ edge, inner.crosses (configuration edge) = true →
      (inner.openGraph (configuration edge)).dist inner.source inner.target ≤ upper)
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    (outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) ≤
      (outer.openGraph (inner.coarseConfiguration configuration)).dist source target * upper := by
  obtain ⟨walk, length⟩ := reachable.exists_walk_length_eq_dist
  have bound := substituted_distance_le_walk_cost outer inner configuration (fun _ => upper)
    cellBound walk
  simpa [List.sum_replicate, length, Nat.mul_comm] using bound

/-- Extend prescribed old-vertex values inside each individual child graph. -/
noncomputable def gluedPotential
    (configuration : Fin outerEdges → Configuration innerEdges)
    (potential : Fin outerVertices → ℝ) : outer.SubstitutionVertex inner → ℝ
  | .inl vertex => potential vertex
  | .inr (edge, vertex) =>
      terminalExtension (inner.openGraph (configuration edge)) inner.source inner.target
        (potential (outer.endpoint edge).1) (potential (outer.endpoint edge).2) vertex.val

theorem gluedPotential_cell
    (configuration : Fin outerEdges → Configuration innerEdges)
    (potential : Fin outerVertices → ℝ)
    (boundaryBound : ∀ edge, inner.crosses (configuration edge) = true →
      |potential (outer.endpoint edge).1 - potential (outer.endpoint edge).2| ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ))
    (edge : Fin outerEdges) (vertex : Fin innerVertices) :
    gluedPotential outer inner configuration potential (outer.cellVertex inner edge vertex) =
      terminalExtension (inner.openGraph (configuration edge)) inner.source inner.target
        (potential (outer.endpoint edge).1) (potential (outer.endpoint edge).2) vertex := by
  have bound : (inner.openGraph (configuration edge)).Reachable inner.source inner.target →
      |potential (outer.endpoint edge).1 - potential (outer.endpoint edge).2| ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ) :=
    fun reachable => boundaryBound edge ((inner.crosses_eq_true _).mpr reachable)
  by_cases source : vertex = inner.source
  · subst vertex
    rw [outer.cellVertex_source inner edge, terminalExtension_source _ _ _ _ _ bound]
    rfl
  · by_cases target : vertex = inner.target
    · subst vertex
      rw [outer.cellVertex_target inner edge, terminalExtension_target _ _ _ _ _ bound]
      rfl
    · simp only [FiniteNetwork.cellVertex, dif_neg source, dif_neg target, gluedPotential]

theorem gluedPotential_adj_bound
    (configuration : Fin outerEdges → Configuration innerEdges)
    (potential : Fin outerVertices → ℝ)
    (boundaryBound : ∀ edge, inner.crosses (configuration edge) = true →
      |potential (outer.endpoint edge).1 - potential (outer.endpoint edge).2| ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ))
    {first second : outer.SubstitutionVertex inner}
    (adjacent : (outer.substitutedGraph inner configuration).Adj first second) :
    |gluedPotential outer inner configuration potential first -
      gluedPotential outer inner configuration potential second| ≤ 1 := by
  obtain ⟨_, edge, source, target, localAdjacent, rfl, rfl⟩ := adjacent
  rw [gluedPotential_cell outer inner configuration potential boundaryBound,
    gluedPotential_cell outer inner configuration potential boundaryBound]
  exact terminalExtension_adj_bound _ _ _ _ _ localAdjacent

theorem potential_difference_le_substituted_distance
    (configuration : Fin outerEdges → Configuration innerEdges)
    (potential : Fin outerVertices → ℝ)
    (boundaryBound : ∀ edge, inner.crosses (configuration edge) = true →
      |potential (outer.endpoint edge).1 - potential (outer.endpoint edge).2| ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ))
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    |potential source - potential target| ≤
      ((outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) : ℝ) := by
  have fineReachable := outer.coarseReachable_lifts inner configuration reachable
  obtain ⟨walk, length⟩ := fineReachable.exists_walk_length_eq_dist
  have bound := potential_difference_le_walk_length _
    (gluedPotential outer inner configuration potential)
    (fun adjacent => gluedPotential_adj_bound outer inner configuration potential boundaryBound adjacent)
    walk
  simpa only [gluedPotential, length] using bound

/-- The reverse comparison comes from a concrete weighted-distance potential. -/
theorem weightedDistance_le_substituted_distance
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (Fin outerVertices) → ℝ) (nonnegative : ∀ edge, 0 ≤ cost edge)
    (costBound : ∀ edge, inner.crosses (configuration edge) = true →
      cost s((outer.endpoint edge).1, (outer.endpoint edge).2) ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ))
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    weightedDistance (outer.openGraph (inner.coarseConfiguration configuration)) cost source target ≤
      ((outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) : ℝ) := by
  let potential := weightedDistance (outer.openGraph (inner.coarseConfiguration configuration)) cost source
  have boundaryBound : ∀ edge, inner.crosses (configuration edge) = true →
      |potential (outer.endpoint edge).1 - potential (outer.endpoint edge).2| ≤
        ((inner.openGraph (configuration edge)).dist inner.source inner.target : ℝ) := by
    intro edge crossing
    have adjacent : (outer.openGraph (inner.coarseConfiguration configuration)).Adj
        (outer.endpoint edge).1 (outer.endpoint edge).2 :=
      ⟨outer.loopless edge, edge, crossing, Or.inl rfl⟩
    exact (weightedDistance_adj_bound _ cost nonnegative source adjacent).trans
      (costBound edge crossing)
  have bound := potential_difference_le_substituted_distance outer inner configuration potential
    boundaryBound reachable
  simpa only [potential, weightedDistance_self _ cost nonnegative source, zero_sub, abs_neg,
    abs_of_nonneg (weightedDistance_nonneg _ cost nonnegative source target)] using bound

theorem nat_walkCost_cast {Vertex : Type*} {graph : SimpleGraph Vertex}
    {source target : Vertex} (walk : graph.Walk source target) (cost : Sym2 Vertex → ℕ) :
    ((walk.edges.map cost).sum : ℝ) = (walk.edges.map (fun edge => (cost edge : ℝ))).sum := by
  induction walk with
  | nil => simp
  | cons adjacent rest inductionHypothesis =>
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, Nat.cast_add,
        inductionHypothesis]

/-- Exact one-step min-plus identity for the genuine glued graph. The only cost
assumption is equality to each actual crossing child's terminal distance. -/
theorem substituted_distance_eq_shortest_of_cost
    (configuration : Fin outerEdges → Configuration innerEdges)
    (cost : Sym2 (Fin outerVertices) → ℕ)
    (costExact : ∀ edge, inner.crosses (configuration edge) = true →
      cost s((outer.endpoint edge).1, (outer.endpoint edge).2) =
        (inner.openGraph (configuration edge)).dist inner.source inner.target)
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    ((outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) : ℝ) =
      (graphPathFamily (outer.openGraph (inner.coarseConfiguration configuration)) source target
        reachable).shortest (fun edge => (cost edge : ℝ)) := by
  apply le_antisymm
  · apply PathFamily.le_shortest
    intro edges membership
    obtain ⟨walk, simple, rfl⟩ :=
      (mem_graphPathFamily _ source target reachable edges).mp membership
    rw [simplePath_cost walk simple]
    have bound := substituted_distance_le_walk_cost outer inner configuration cost
      (fun edge crossing => (costExact edge crossing).ge) walk
    have castBound : ((outer.substitutedGraph inner configuration).dist
        (Sum.inl source) (Sum.inl target) : ℝ) ≤ ((walk.edges.map cost).sum : ℝ) := by
      exact_mod_cast bound
    rwa [nat_walkCost_cast] at castBound
  · rw [← weightedDistance_of_reachable _ _ reachable]
    apply weightedDistance_le_substituted_distance outer inner configuration _
      (fun _ => Nat.cast_nonneg _) _ reachable
    intro edge crossing
    exact_mod_cast (costExact edge crossing).le

/-- The cost of a coarse bond is selected from its indexed child graph. For a
simple outer network the selection is unique, as proved below. -/
noncomputable def childDistanceCost
    (configuration : Fin outerEdges → Configuration innerEdges)
    (bond : Sym2 (Fin outerVertices)) : ℕ := by
  classical
  exact if existsEdge : ∃ edge, s((outer.endpoint edge).1, (outer.endpoint edge).2) = bond then
    (inner.openGraph (configuration (Classical.choose existsEdge))).dist inner.source inner.target
  else 0

theorem childDistanceCost_endpoint
    (configuration : Fin outerEdges → Configuration innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (edge : Fin outerEdges) :
    childDistanceCost outer inner configuration s((outer.endpoint edge).1, (outer.endpoint edge).2) =
      (inner.openGraph (configuration edge)).dist inner.source inner.target := by
  classical
  have existsEdge : ∃ other, s((outer.endpoint other).1, (outer.endpoint other).2) =
      s((outer.endpoint edge).1, (outer.endpoint edge).2) := ⟨edge, rfl⟩
  simp only [childDistanceCost, dif_pos existsEdge]
  rw [simple (Classical.choose_spec existsEdge)]

/-- The exact finite substitution identity for a simple outer network and
arbitrary percolation configurations in its cells. -/
theorem substituted_distance_eq_shortest
    (configuration : Fin outerEdges → Configuration innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    {source target : Fin outerVertices}
    (reachable : (outer.openGraph (inner.coarseConfiguration configuration)).Reachable source target) :
    ((outer.substitutedGraph inner configuration).dist (Sum.inl source) (Sum.inl target) : ℝ) =
      (graphPathFamily (outer.openGraph (inner.coarseConfiguration configuration)) source target
        reachable).shortest (fun edge => (childDistanceCost outer inner configuration edge : ℝ)) :=
  substituted_distance_eq_shortest_of_cost outer inner configuration _
    (fun edge _ => childDistanceCost_endpoint outer inner configuration simple edge) reachable

end IGSIII.Chemical.Substitution
