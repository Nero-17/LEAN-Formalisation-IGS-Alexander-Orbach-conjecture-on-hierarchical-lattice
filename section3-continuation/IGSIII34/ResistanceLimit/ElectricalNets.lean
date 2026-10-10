import IGSIII34.ResistanceLimit.ActualRayleigh
import IGSIII34.ResistanceLimit.RadiusMesh
import IGSIII.Geometry.ActualSkeletonNets

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem planted_pairResistance_le_radius {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (side : Bool) (vertex : Fin vertices) :
    pairResistance (IGSIII34.Percolation.network network configuration) (fun _ => 1)
      (plantedVertex network side) vertex ≤
      terminalResistanceRadius (IGSIII34.Percolation.network network configuration) (fun _ => 1) := by
  cases side
  · exact targetResistance_le_radius _ _ _
  · exact sourceResistance_le_radius _ _ _

/-- The actual finite birth skeletons are uniform electrical nets in every
later retained component. The proof follows each available child terminal;
one-terminal decorations and both noncrossing sides remain in the network. -/
theorem finite_skeleton_is_electrical_net_of_radius_bounds (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (scale eta coefficient : ℝ) (start : ℕ)
    (scalePositive : 0 < scale) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks depth address opened /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length) :
    ∀ depth age address opened sourceSide (vertex : Fin (rule.generation depth).vertices),
      start ≤ address.length + age + 1 →
      ((rule.generation depth).network.openGraph
        (markedGenerationConfiguration rule marks depth address opened)).Reachable
          (plantedVertex (rule.generation depth).network sourceSide) vertex →
      ∃ anchor ∈ finiteSkeletonVertices rule depth age,
        ((rule.generation depth).network.openGraph
          (markedGenerationConfiguration rule marks depth address opened)).Reachable
            (plantedVertex (rule.generation depth).network sourceSide) anchor ∧
        pairResistance (network (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address opened)) (fun _ => 1) anchor vertex /
            scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ (address.length + age + 1) := by
  intro depth
  induction depth with
  | zero =>
    intro age address opened sourceSide vertex _ reachable
    refine ⟨vertex, Finset.mem_univ _, reachable, ?_⟩
    rw [pairResistance_self, zero_div]
    exact mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _)
  | succ depth inductionHypothesis =>
    intro age address opened sourceSide vertex beyond reachable
    rcases retained_generation_point_old_or_child rule marks depth address opened sourceSide vertex reachable with
      ⟨old, vertexIdentity⟩ | ⟨edge, child, childSide, vertexIdentity, childReachable, terminalRetained⟩
    · refine ⟨vertex, ?_, reachable, ?_⟩
      · rw [vertexIdentity]
        exact oldVertex_mem_finiteSkeleton rule depth age old
      · rw [pairResistance_self, zero_div]
        exact mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _)
    · cases age with
      | zero =>
        refine ⟨(rule.generationCellEmbedding depth edge).vertex (plantedVertex (rule.generation depth).network childSide),
          generationCellEmbedding_planted_mem_finiteSkeleton rule depth 0 edge childSide, terminalRetained, ?_⟩
        rw [vertexIdentity]
        apply (normalized_markedChild_pairResistance_le rule marks depth address opened edge _ _ childReachable scale scalePositive).trans
        have childBeyond : start ≤ (address ++ [edge]).length := by simp; omega
        have localBound := (div_le_div_of_nonneg_right
          (planted_pairResistance_le_radius (rule.generation depth).network
            (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)) childSide child)
          (pow_pos scalePositive (depth + 1 + (address ++ [edge]).length)).le).trans
            (radiusBound (address ++ [edge]) (marks (address, opened) edge) depth childBeyond)
        simpa only [List.length_append, List.length_singleton, Nat.add_zero] using localBound
      | succ age =>
        have childBeyond : start ≤ (address ++ [edge]).length + age + 1 := by simp; omega
        obtain ⟨childAnchor, membership, childAnchorRetained, childClose⟩ := inductionHypothesis age (address ++ [edge])
          (marks (address, opened) edge) childSide child childBeyond childReachable
        refine ⟨(rule.generationCellEmbedding depth edge).vertex childAnchor,
          childVertex_mem_finiteSkeleton rule depth age edge childAnchor membership, ?_, ?_⟩
        · have mapped := childAnchorRetained.map (markedChildHom rule marks depth address opened edge)
          simp only [markedChildHom_vertex] at mapped
          exact terminalRetained.trans mapped
        · rw [vertexIdentity]
          have embeddedBound := normalized_markedChild_pairResistance_le rule marks depth address opened edge childAnchor child
            (childAnchorRetained.symm.trans childReachable) scale scalePositive
          apply embeddedBound.trans
          simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using childClose

end
end IGSIII34.ResistanceLimit
