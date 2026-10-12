import IGSIII34.ResistanceLimit.ActualPairCellAlternativeCompletion
import IGSIII34.ResistanceLimit.NetworkBounds
import Mathlib.Data.Finset.Max

/-! The finite-level modulus linking actual chemical distances to actual
electrical distances. Its inputs are finite chemical trace compatibility and
the microscopic resistance mesh, both proved separately for actual fields. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem finite_metric_separation_completion
    {Space : Type*} [MetricSpace Space] [Fintype Space] [Nonempty Space] :
    ∃ delta > 0, ∀ first last : Space, dist first last < delta → first = last := by
  classical
  let separation (pair : Space × Space) : ℝ := if pair.1 = pair.2 then 1 else dist pair.1 pair.2
  have positive : ∀ pair, 0 < separation pair := by
    intro pair
    dsimp only [separation]
    split_ifs with equal
    · norm_num
    · exact dist_pos.mpr equal
  obtain ⟨pair, _, minimal⟩ := Finset.exists_min_image Finset.univ separation Finset.univ_nonempty
  refine ⟨separation pair, positive pair, ?_⟩
  intro first last small
  by_contra distinct
  have lower := minimal (first,last) (Finset.mem_univ _)
  simp only [separation, if_neg distinct] at lower
  exact (not_lt_of_ge lower) small

theorem pairResistance_two_anchor_bounds_completion
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (anchor first last : Vertex)
    (firstReachable : network.graph.Reachable anchor first) (lastReachable : network.graph.Reachable anchor last)
    (radius : ℝ) (firstBound : pairResistance network resistance anchor first ≤ radius)
    (lastBound : pairResistance network resistance anchor last ≤ radius) :
    pairResistance network resistance first last ≤ 2 * radius := by
  have triangle := pairResistance_triangle network resistance positive first anchor last firstReachable.symm lastReachable
  rw [pairResistance_comm network resistance positive firstReachable.symm] at triangle
  linarith

theorem actual_generation_chemical_electrical_modulus_completion
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
    (lengthPositive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
    (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges //
      markedGenerationConfiguration rule marks depth [] true edge = true} → ℝ)
    (resistancePositive : ∀ depth edge, 0 < resistance depth edge)
    (coarse : ℕ) (radius : ℝ)
    (compatibility : ∀ fine (first last : Fin (rule.generation coarse).vertices),
      ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
        (rule.generation coarse).network.source first →
      ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true)).Reachable
        (rule.generation coarse).network.source last →
      weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
        (indexedBondCost (rule.generation (coarse + fine + 1)).network (lengths (coarse + fine + 1)))
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last) =
      weightedDistance ((rule.generation coarse).network.openGraph (markedGenerationConfiguration rule marks coarse [] true))
        (indexedBondCost (rule.generation coarse).network (lengths coarse)) first last)
    (mesh : ∀ fine (edge : Fin (rule.generation coarse).edges) side (point : Fin (rule.generation fine).vertices),
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
        (plantedVertex (rule.generation fine).network side) point →
      ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
        (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex point) →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) (resistance (coarse + fine + 1))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
        ((generationBlockCellEmbedding rule coarse fine edge).vertex point) ≤ radius) :
    ∃ delta > 0, ∀ fine (first last : RetainedSkeletonVertex (rule.generation (coarse + fine + 1)).network
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)),
      weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))
        (indexedBondCost (rule.generation (coarse + fine + 1)).network (lengths (coarse + fine + 1))) first.val last.val < delta →
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) (resistance (coarse + fine + 1)) first.val last.val ≤
        2 * radius := by
  classical
  letI := actualSkeletonMetric (rule.generation coarse).network (classicalRule.generation coarse).simple
    (markedGenerationConfiguration rule marks coarse [] true) (lengths coarse) (nonnegative coarse) (lengthPositive coarse)
  letI : Fintype (RetainedSkeletonVertex (rule.generation coarse).network
    (markedGenerationConfiguration rule marks coarse [] true)) := Fintype.ofFinite _
  letI : Nonempty (RetainedSkeletonVertex (rule.generation coarse).network
    (markedGenerationConfiguration rule marks coarse [] true)) := ⟨⟨_, SimpleGraph.Reachable.refl _⟩⟩
  obtain ⟨separation, separationPositive, separates⟩ := finite_metric_separation_completion
    (Space := RetainedSkeletonVertex (rule.generation coarse).network (markedGenerationConfiguration rule marks coarse [] true))
  refine ⟨separation / 2, div_pos separationPositive (by norm_num), ?_⟩
  intro fine first last small
  let cost := indexedBondCost (rule.generation (coarse + fine + 1)).network (lengths (coarse + fine + 1))
  have costNonnegative := indexedBondCost_nonnegative (rule.generation (coarse + fine + 1)).network
    (lengths (coarse + fine + 1)) (nonnegative (coarse + fine + 1))
  have terminalRetained (edge : Fin (rule.generation coarse).edges) (side : Bool) (point : Fin (rule.generation fine).vertices)
      (localReachable : ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
        (plantedVertex (rule.generation fine).network side) point)
      (retained : ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
        (rule.generation (coarse + fine + 1)).network.source ((generationBlockCellEmbedding rule coarse fine edge).vertex point)) :
      ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).Reachable
        (rule.generation (coarse + fine + 1)).network.source
        ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side)) := by
    exact retained.trans ((localReachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))).symm)
  rcases actual_retained_pair_cell_alternative_completion rule marks crossing coarse fine cost costNonnegative
    first.val last.val first.property last.property with
    ⟨edge, left, right, side, firstIdentity, lastIdentity, firstReachable, lastReachable, _⟩ |
    ⟨firstEdge, lastEdge, left, right, firstSide, lastSide, firstIdentity, lastIdentity,
      firstReachable, lastReachable, firstAnchorRetained, lastAnchorRetained, chemicalBound⟩
  · rw [firstIdentity, lastIdentity]
    exact pairResistance_two_anchor_bounds_completion _ _ (resistancePositive _) _ _ _
      (by rw [graph_eq_openGraph]; exact firstReachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)))
      (by rw [graph_eq_openGraph]; exact lastReachable.map ((generationBlockCellEmbedding rule coarse fine edge).openGraphHom (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true))) radius
      (mesh fine edge side left firstReachable (firstIdentity ▸ first.property))
      (mesh fine edge side right lastReachable (lastIdentity ▸ last.property))
  · have firstFineRetained := terminalRetained firstEdge firstSide left firstReachable (firstIdentity ▸ first.property)
    have lastFineRetained := terminalRetained lastEdge lastSide right lastReachable (lastIdentity ▸ last.property)
    have anchorBound := weightedDistance_triangle _ cost costNonnegative
      (firstFineRetained.symm.trans first.property) (first.property.symm.trans lastFineRetained)
    have lastTriangle := weightedDistance_triangle _ cost costNonnegative
      (first.property.symm.trans last.property) (last.property.symm.trans lastFineRetained)
    rw [weightedDistance_comm _ cost costNonnegative last.val _] at lastTriangle
    have anchorSmall : weightedDistance ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)) cost
        ((generationBlockCellEmbedding rule coarse fine firstEdge).vertex (plantedVertex (rule.generation fine).network firstSide))
        ((generationBlockCellEmbedding rule coarse fine lastEdge).vertex (plantedVertex (rule.generation fine).network lastSide)) < separation := by
      dsimp only [cost] at *
      linarith
    have firstAnchorIdentity : (generationBlockCellEmbedding rule coarse fine firstEdge).vertex
        (plantedVertex (rule.generation fine).network firstSide) = blockOldVertexEmbedding rule coarse fine
        (if firstSide then ((rule.generation coarse).network.endpoint firstEdge).1 else ((rule.generation coarse).network.endpoint firstEdge).2) := by
      cases firstSide <;> simp only [plantedVertex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        generationBlockCellEmbedding_source, generationBlockCellEmbedding_target]
    have lastAnchorIdentity : (generationBlockCellEmbedding rule coarse fine lastEdge).vertex
        (plantedVertex (rule.generation fine).network lastSide) = blockOldVertexEmbedding rule coarse fine
        (if lastSide then ((rule.generation coarse).network.endpoint lastEdge).1 else ((rule.generation coarse).network.endpoint lastEdge).2) := by
      cases lastSide <;> simp only [plantedVertex, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
        generationBlockCellEmbedding_source, generationBlockCellEmbedding_target]
    rw [firstAnchorIdentity, lastAnchorIdentity, compatibility fine _ _ firstAnchorRetained lastAnchorRetained] at anchorSmall
    have equal := congrArg Subtype.val (separates ⟨_,firstAnchorRetained⟩ ⟨_,lastAnchorRetained⟩ anchorSmall)
    have fineEqual := firstAnchorIdentity.trans ((congrArg (blockOldVertexEmbedding rule coarse fine) equal).trans lastAnchorIdentity.symm)
    have firstBound := mesh fine firstEdge firstSide left firstReachable (firstIdentity ▸ first.property)
    have lastBound := mesh fine lastEdge lastSide right lastReachable (lastIdentity ▸ last.property)
    rw [← fineEqual] at lastFineRetained lastBound
    rw [← firstIdentity] at firstBound
    rw [← lastIdentity] at lastBound
    exact pairResistance_two_anchor_bounds_completion _ _ (resistancePositive _) _ _ _
      (by rw [graph_eq_openGraph]; exact firstFineRetained.symm.trans first.property)
      (by rw [graph_eq_openGraph]; exact firstFineRetained.symm.trans last.property) radius firstBound lastBound

end
end IGSIII34.ResistanceLimit

