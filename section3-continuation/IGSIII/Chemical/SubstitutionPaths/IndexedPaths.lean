import IGSIII.Chemical.SubstitutionPaths.History

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Actual terminal paths indexed by the original rule edges

The finite path family is pulled back from the actual simple graph paths.
Simplicity ensures that each graph bond has exactly one indexed edge. On a
noncrossing configuration the family is the singleton containing the empty
path, matching the zero convention for graph distance.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def indexedPath {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (path : Finset (Sym2 (Fin vertices))) : Finset (Fin edges) := by
  classical
  exact Finset.univ.filter (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2) ∈ path)

noncomputable def edgePathFamily {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : PathFamily (Fin edges) := by
  classical
  exact if reachable : (network.openGraph configuration).Reachable network.source network.target then
    { paths := (graphPathFamily (network.openGraph configuration) network.source network.target reachable).paths.image
        (indexedPath network)
      nonempty := (graphPathFamily (network.openGraph configuration)
        network.source network.target reachable).nonempty.image _ }
  else { paths := {∅}, nonempty := by simp }

theorem indexedPath_image {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (reachable : (network.openGraph configuration).Reachable network.source network.target)
    {path : Finset (Sym2 (Fin vertices))}
    (membership : path ∈ (graphPathFamily (network.openGraph configuration)
      network.source network.target reachable).paths) :
    (indexedPath network path).image (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)) = path := by
  classical
  ext bond
  constructor
  · intro imageMembership
    obtain ⟨edge, edgeMembership, rfl⟩ := Finset.mem_image.mp imageMembership
    exact (Finset.mem_filter.mp edgeMembership).2
  · intro bondMembership
    obtain ⟨edge, _, rfl⟩ := graphPathFamily_used_edge network configuration reachable membership bondMembership
    exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bondMembership⟩, rfl⟩

theorem indexedPath_cost {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges)
    (reachable : (network.openGraph configuration).Reachable network.source network.target)
    {path : Finset (Sym2 (Fin vertices))}
    (membership : path ∈ (graphPathFamily (network.openGraph configuration)
      network.source network.target reachable).paths) (cost : Sym2 (Fin vertices) → ℝ) :
    PathFamily.pathCost (indexedPath network path)
        (fun edge => cost s((network.endpoint edge).1, (network.endpoint edge).2)) =
      PathFamily.pathCost path cost := by
  classical
  calc
    _ = PathFamily.pathCost ((indexedPath network path).image
        (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2))) cost := by
      simp only [PathFamily.pathCost, Finset.sum_image (fun first _ second _ equality => simple equality)]
    _ = _ := by rw [indexedPath_image network configuration reachable membership]

theorem edgePathFamily_shortest_eq_weightedDistance {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (cost : Sym2 (Fin vertices) → ℝ) :
    (edgePathFamily network configuration).shortest
        (fun edge => cost s((network.endpoint edge).1, (network.endpoint edge).2)) =
      weightedDistance (network.openGraph configuration) cost network.source network.target := by
  classical
  by_cases reachable : (network.openGraph configuration).Reachable network.source network.target
  · rw [weightedDistance_of_reachable _ _ reachable]
    apply le_antisymm
    · obtain ⟨path, membership, minimal⟩ :=
        (graphPathFamily (network.openGraph configuration) network.source network.target reachable).exists_minimizer cost
      have indexedMembership : indexedPath network path ∈ (edgePathFamily network configuration).paths := by
        simp only [edgePathFamily, dif_pos reachable]
        exact Finset.mem_image.mpr ⟨path, membership, rfl⟩
      calc
        _ ≤ PathFamily.pathCost (indexedPath network path) _ :=
          (edgePathFamily network configuration).shortest_le_pathCost _ indexedMembership
        _ = PathFamily.pathCost path cost := indexedPath_cost network simple configuration reachable membership cost
        _ = _ := minimal.symm
    · obtain ⟨indexed, membership, minimal⟩ :=
        (edgePathFamily network configuration).exists_minimizer
          (fun edge => cost s((network.endpoint edge).1, (network.endpoint edge).2))
      simp only [edgePathFamily, dif_pos reachable] at membership
      obtain ⟨path, pathMembership, rfl⟩ := Finset.mem_image.mp membership
      rw [indexedPath_cost network simple configuration reachable pathMembership cost] at minimal
      exact (PathFamily.shortest_le_pathCost
        (graphPathFamily (network.openGraph configuration) network.source network.target reachable)
          cost pathMembership).trans_eq minimal.symm
  · simp [edgePathFamily, weightedDistance, reachable, PathFamily.shortest, PathFamily.pathCost]

/-- Exact min-plus identity on the original indexed edge set, so the actual
conditional child product law applies to each coordinate without relabelling. -/
theorem cellMinPlus_eq_edgePathFamily_shortest
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (simple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (coarse : Configuration outerEdges) (cells : Fin outerEdges → Configuration innerEdges) :
    cellMinPlus outer inner coarse cells = (edgePathFamily outer coarse).shortest
      (fun edge => ((inner.openGraph (cells edge)).dist inner.source inner.target : ℝ)) := by
  rw [cellMinPlus, ← edgePathFamily_shortest_eq_weightedDistance outer simple]
  congr 1
  funext edge
  rw [childDistanceCost_endpoint outer inner cells simple edge]

theorem edgePathFamily_used_edge {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) {path : Finset (Fin edges)}
    (membership : path ∈ (edgePathFamily network configuration).paths)
    {edge : Fin edges} (edgeMembership : edge ∈ path) : configuration edge = true := by
  classical
  by_cases reachable : (network.openGraph configuration).Reachable network.source network.target
  · simp only [edgePathFamily, dif_pos reachable] at membership
    obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
    have bondMembershipEdge := (Finset.mem_filter.mp edgeMembership).2
    obtain ⟨other, retained, equality⟩ :=
      graphPathFamily_used_edge network configuration reachable bondMembership bondMembershipEdge
    have same : edge = other := simple equality
    rwa [same]
  · simp only [edgePathFamily, dif_neg reachable, Finset.mem_singleton] at membership
    simp [membership] at edgeMembership

theorem edgePathFamily_card_bounds {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges)
    (crossing : network.crosses configuration = true) {path : Finset (Fin edges)}
    (membership : path ∈ (edgePathFamily network configuration).paths) :
    network.fullGraph.dist network.source network.target ≤ path.card ∧
      path.card ≤ longestTerminalPath network := by
  classical
  have reachable := (network.crosses_eq_true _).mp crossing
  simp only [edgePathFamily, dif_pos reachable] at membership
  obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
  have cardinality : (indexedPath network bondPath).card = bondPath.card := by
    calc
      _ = ((indexedPath network bondPath).image
          (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2))).card := by
        rw [Finset.card_image_of_injective _ simple]
      _ = _ := congrArg Finset.card (indexedPath_image network configuration reachable bondMembership)
  rw [cardinality]
  exact actual_path_card_bounds network configuration reachable bondMembership

end IGSIII.Chemical.Substitution
