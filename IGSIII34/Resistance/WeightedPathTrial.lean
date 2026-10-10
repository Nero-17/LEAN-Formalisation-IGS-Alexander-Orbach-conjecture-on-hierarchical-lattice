import IGSIII34.Resistance.PathTrial
import IGSIII.Chemical.SubstitutionPaths.WeightedDistance

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open IGSIII.Chemical.Substitution

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem exists_weighted_path_flow (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (cost : Sym2 Vertex → ℝ)
    (consistent : ∀ edge, resistance edge = cost s((network.endpoint edge).1, (network.endpoint edge).2))
    {first second : Vertex} (walk : network.graph.Walk first second) (path : walk.IsPath) :
    ∃ current : Edge → ℝ, network.flowBetween first second current ∧
      (∀ edge, current edge ^ 2 = 0 ∨ current edge ^ 2 = 1) ∧
      (∀ edge, current edge ≠ 0 →
        (network.endpoint edge).1 ∈ walk.support ∧ (network.endpoint edge).2 ∈ walk.support) ∧
      energy resistance current = (walk.edges.map cost).sum := by
  revert path
  induction walk with
  | nil =>
      intro _
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro vertex
        simp [divergence]
      · intro edge
        exact Or.inl (by norm_num)
      · intro edge nonzero
        exact False.elim (nonzero rfl)
      · simp [energy]
  | @cons first middle last adjacent walk inductionHypothesis =>
      intro path
      have pathProperties := (SimpleGraph.Walk.cons_isPath_iff adjacent walk).mp path
      obtain ⟨tailCurrent, tailFlow, tailSquares, tailSupport, tailEnergy⟩ := inductionHypothesis pathProperties.1
      obtain ⟨edge, sign, signSquare, edgeFlow, orientation⟩ :=
        network.exists_signed_edge_flow_of_adjacent adjacent
      have firstEndpoint : (network.endpoint edge).1 = first ∨ (network.endpoint edge).2 = first := by
        rcases orientation with forward | backward
        · exact Or.inl (congrArg Prod.fst forward)
        · exact Or.inr (congrArg Prod.snd backward)
      have zeroTail : tailCurrent edge = 0 := by
        by_contra nonzero
        have endpoints := tailSupport edge nonzero
        rcases firstEndpoint with firstEquals | secondEquals
        · exact pathProperties.2 (firstEquals ▸ endpoints.1)
        · exact pathProperties.2 (secondEquals ▸ endpoints.2)
      refine ⟨fun index => (if index = edge then sign else 0) + tailCurrent index,
        network.flowBetween_add edgeFlow tailFlow, ?_, ?_, ?_⟩
      · intro index
        by_cases same : index = edge
        · subst index
          exact Or.inr (by simpa only [ite_true, zeroTail, add_zero] using signSquare)
        · simpa only [same, ↓reduceIte, zero_add] using tailSquares index
      · intro index nonzero
        by_cases same : index = edge
        · subst index
          rcases orientation with forward | backward
          · simp [forward, SimpleGraph.Walk.support_cons, walk.start_mem_support]
          · simp [backward, SimpleGraph.Walk.support_cons, walk.start_mem_support]
        · have tailNonzero : tailCurrent index ≠ 0 := by simpa [same] using nonzero
          obtain ⟨firstInside, secondInside⟩ := tailSupport index tailNonzero
          exact ⟨List.mem_cons_of_mem _ firstInside, List.mem_cons_of_mem _ secondInside⟩
      · have edgeCost : resistance edge = cost s(first, middle) := by
          rw [consistent edge]
          rcases orientation with forward | backward
          · rw [forward]
          · rw [backward, Sym2.eq_swap]
        rw [energy_add_single_of_zero _ _ _ _ zeroTail, signSquare, mul_one, tailEnergy, edgeCost]
        simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]

theorem effectiveResistance_le_weightedDistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (cost : Sym2 Vertex → ℝ)
    (consistent : ∀ edge, resistance edge = cost s((network.endpoint edge).1, (network.endpoint edge).2)) :
    network.effectiveResistance resistance ≤
      weightedDistance network.graph cost network.source network.target := by
  obtain ⟨walk, simple, minimizing⟩ := exists_weighted_geodesic network.graph cost connected
  obtain ⟨current, unitFlow, _, _, energyIdentity⟩ := network.exists_weighted_path_flow resistance cost consistent walk simple
  exact (network.effectiveResistance_le_energy nonnegative unitFlow).trans_eq
    (energyIdentity.trans minimizing)

end
end IGSIII34.Resistance.FiniteNetwork
