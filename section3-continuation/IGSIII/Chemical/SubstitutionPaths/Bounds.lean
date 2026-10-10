import IGSIII.Chemical.SubstitutionPaths.Generation

set_option autoImplicit false

/-!
# Actual graph distance bounds from the finite rule

The lower length is the full rule's terminal graph distance. The upper length
is the maximum length of an actual simple terminal path in that full rule.
Both constants are extracted from the graph, with no path-bound certificates.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def longestTerminalPath {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) : ℕ :=
  (graphPathSets network.fullGraph network.source network.target).sup Finset.card

theorem openGraph_le_fullGraph {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) :
    network.openGraph configuration ≤ network.fullGraph := by
  intro first second adjacent
  obtain ⟨distinct, edge, _, endpoints⟩ := adjacent
  exact ⟨distinct, edge, rfl, endpoints⟩

set_option backward.isDefEq.respectTransparency false in
theorem actual_path_card_bounds {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (reachable : (network.openGraph configuration).Reachable network.source network.target)
    {path : Finset (Sym2 (Fin vertices))}
    (membership : path ∈ (graphPathFamily (network.openGraph configuration)
      network.source network.target reachable).paths) :
    network.fullGraph.dist network.source network.target ≤ path.card ∧
      path.card ≤ longestTerminalPath network := by
  obtain ⟨walk, simple, rfl⟩ :=
    (mem_graphPathFamily _ network.source network.target reachable path).mp membership
  have inclusion := openGraph_le_fullGraph network configuration
  have fullSimple : (walk.mapLe inclusion).IsPath := simple.mapLe inclusion
  have fullMembership : (walk.mapLe inclusion).edges.toFinset ∈
      graphPathSets network.fullGraph network.source network.target :=
    (mem_graphPathSets _ _ _ _).mpr ⟨walk.mapLe inclusion, fullSimple, rfl⟩
  rw [simplePath_edgeSet_card walk simple]
  constructor
  · simpa only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map] using
      network.fullGraph.dist_le (walk.mapLe inclusion)
  · have bound := Finset.le_sup (f := Finset.card) fullMembership
    simpa only [simplePath_edgeSet_card _ fullSimple, SimpleGraph.Walk.mapLe,
      SimpleGraph.Walk.length_map, longestTerminalPath]
      using bound

theorem innovation_path_card_bounds (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (address : List (Sym2 (Fin rule.vertices)))
    {path : Finset (Sym2 (Fin rule.vertices))}
    (membership : path ∈ (innovationPathFamily rule innovation crossing address).paths) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ (path.card : ℝ) ∧
      (path.card : ℝ) ≤ (longestTerminalPath rule.network : ℝ) := by
  have bounds := actual_path_card_bounds rule.network (innovation address)
    ((rule.network.crosses_eq_true _).mp (crossing address)) membership
  exact ⟨by exact_mod_cast bounds.1, by exact_mod_cast bounds.2⟩

/-- The manuscript's deterministic exponential distance bounds now apply to
the actual IGS II finite graphs, with the exact graph-derived constants. -/
theorem generation_distance_bounds (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (noncrossing : (depth : ℕ) → List (Sym2 (Fin rule.vertices)) →
      Fin rule.edges → Configuration (recursiveRule rule depth).edges)
    (doesNotCross : ∀ depth address edge, innovation address edge = false →
      (recursiveRule rule depth).network.crosses (noncrossing depth address edge) = false)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 1) ≤
      (((rule.generation depth).network.openGraph
        (fullGenerationConfiguration rule innovation noncrossing depth address)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) ∧
    (((rule.generation depth).network.openGraph
        (fullGenerationConfiguration rule innovation noncrossing depth address)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) ≤
      (longestTerminalPath rule.network : ℝ) ^ (depth + 1) := by
  rw [generation_distance_eq_terminalDistance rule simple innovation crossing noncrossing doesNotCross]
  exact terminalDistance_bounds (innovationPathFamily rule innovation crossing) (Nat.cast_nonneg _)
    (fun address path membership => innovation_path_card_bounds rule innovation crossing address membership)
    address (depth + 1)

end IGSIII.Chemical.Substitution
