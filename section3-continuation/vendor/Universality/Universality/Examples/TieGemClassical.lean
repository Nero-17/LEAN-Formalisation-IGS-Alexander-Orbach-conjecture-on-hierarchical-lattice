import Universality.Examples.TieGemData
import Universality.Graph.ClassicalSubstitution
import Universality.Graph.FiniteVolume

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem substitute_survives_single_deletion_of_outer
    {vR eR vS eS : ℕ} (R : FiniteNetwork vR eR) (S : FiniteNetwork vS eS)
    (hinner : S.fullGraph.Reachable S.source S.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    ∀ edge, (R.substitute S).crosses (onlyClosed edge) = true := by
  intro edge
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective edge
  have hconfig := (substitutionConfigurationEquiv (outerEdges := eR)
    (innerEdges := eS)).apply_symm_apply (onlyClosed (finProdFinEquiv (edge, child)))
  rw [← hconfig, substitute_crosses, substitution_onlyClosed_cells]
  apply R.crosses_mono (onlyClosed edge) _ _ (hcut edge)
  intro other hopen
  have hne : other ≠ edge := by
    intro heq
    subst other
    simp [onlyClosed] at hopen
  simp only [coarseConfiguration, if_neg hne]
  exact (S.crosses_eq_true _).mpr hinner

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def triangleCanonicalWalk (edge : Fin 3) : triangleNetwork.fullGraph.Walk triangleNetwork.source triangleNetwork.target :=
  if edge = 2 then .cons (by decide : triangleNetwork.fullGraph.Adj 0 1) .nil
  else .cons (by decide : triangleNetwork.fullGraph.Adj 0 2)
    (.cons (by decide : triangleNetwork.fullGraph.Adj 2 1) .nil)

theorem twoEdgePath_canonical : ∀ edge, ∃ walk : twoEdgePathNetwork.fullGraph.Walk
    twoEdgePathNetwork.source twoEdgePathNetwork.target,
    walk.IsPath ∧ s((twoEdgePathNetwork.endpoint edge).1, (twoEdgePathNetwork.endpoint edge).2) ∈ walk.edges := by
  intro edge
  refine ⟨twoEdgePathDistanceCertificate.walk, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'; decide
  · fin_cases edge <;> decide

theorem triangle_canonical : ∀ edge, ∃ walk : triangleNetwork.fullGraph.Walk
    triangleNetwork.source triangleNetwork.target,
    walk.IsPath ∧ s((triangleNetwork.endpoint edge).1, (triangleNetwork.endpoint edge).2) ∈ walk.edges := by
  intro edge
  refine ⟨triangleCanonicalWalk edge, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'; fin_cases edge <;> decide
  · fin_cases edge <;> decide

theorem tie_simple : Function.Injective (fun edge =>
    s((tieRule.network.endpoint edge).1, (tieRule.network.endpoint edge).2)) := by
  change Function.Injective (fun edge : Fin (2 * 3) =>
    s(((twoEdgePathNetwork.substitute triangleNetwork).endpoint edge).1,
      ((twoEdgePathNetwork.substitute triangleNetwork).endpoint edge).2))
  intro first second heq
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective first
  obtain ⟨⟨other, bond⟩, rfl⟩ := finProdFinEquiv.surjective second
  change s(((twoEdgePathNetwork.substitute triangleNetwork).endpoint (finProdFinEquiv (edge, child))).1,
    ((twoEdgePathNetwork.substitute triangleNetwork).endpoint (finProdFinEquiv (edge, child))).2) =
    s(((twoEdgePathNetwork.substitute triangleNetwork).endpoint (finProdFinEquiv (other, bond))).1,
    ((twoEdgePathNetwork.substitute triangleNetwork).endpoint (finProdFinEquiv (other, bond))).2) at heq
  simp only [substitute_endpoint] at heq
  rcases Sym2.eq_iff.mp heq with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  all_goals
    have firstCode := congrArg (fun vertex : twoEdgePathNetwork.SubstitutionVertex triangleNetwork =>
      match vertex with
      | .inl v => v.val
      | .inr pair => 3 + pair.1.val) ((Fintype.equivFin _).injective hfirst)
    have secondCode := congrArg (fun vertex : twoEdgePathNetwork.SubstitutionVertex triangleNetwork =>
      match vertex with
      | .inl v => v.val
      | .inr pair => 3 + pair.1.val) ((Fintype.equivFin _).injective hsecond)
    clear heq hfirst hsecond
    fin_cases edge <;> fin_cases child <;> fin_cases other <;> fin_cases bond <;>
      norm_num [cellVertex, twoEdgePathNetwork, triangleNetwork,
        show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide] at *

theorem tie_gem_vertices : tieRule.vertices = 5 ∧ gemRule.vertices = 6 := by
  simp [tieRule, gemRule, Rule.mul_vertices, twoEdgePathRule, triangleRule]

theorem tieRule_classical : tieRule.Classical where
  connected := twoEdgePathNetwork.substitute_all_vertices_connected triangleNetwork
    (by intro v; apply (twoEdgePathNetwork.fullGraph.reachableDecide_eq_true _ _).mp; fin_cases v <;> decide)
    (by intro v; apply (triangleNetwork.fullGraph.reachableDecide_eq_true _ _).mp; fin_cases v <;> decide)
  simple := tie_simple
  canonical := twoEdgePathNetwork.substitute_canonical triangleNetwork (by decide) (by decide)
    triangle_connected twoEdgePath_canonical triangle_canonical
  scale := by rw [tie_gem_distance.1]; norm_num
  cut := twoEdgePathNetwork.substitute_survives_single_deletion triangleNetwork
    twoEdgePath_connected triangle_connected (by decide)
  symmetric := by
    refine ⟨twoEdgePathTerminalSymmetry.substitute triangleTerminalSymmetry (by decide) (by decide), ?_, ?_⟩
    · apply NetworkSymmetry.substitute_vertex_involutive
      · intro v; fin_cases v <;> decide
      · intro v; fin_cases v <;> decide
      · intro e; fin_cases e <;> decide
    · exact NetworkSymmetry.substitute_source _ _ _ _ (by decide)

theorem gemRule_classical : gemRule.Classical where
  connected := triangleNetwork.substitute_all_vertices_connected twoEdgePathNetwork
    (by intro v; apply (triangleNetwork.fullGraph.reachableDecide_eq_true _ _).mp; fin_cases v <;> decide)
    (by intro v; apply (twoEdgePathNetwork.fullGraph.reachableDecide_eq_true _ _).mp; fin_cases v <;> decide)
  simple := triangleNetwork.substitute_simple twoEdgePathNetwork (by decide)
    (by rw [twoEdgePathDistanceCertificate.distance_eq]; decide)
  canonical := triangleNetwork.substitute_canonical twoEdgePathNetwork (by decide) (by decide)
    twoEdgePath_connected triangle_canonical twoEdgePath_canonical
  scale := by rw [tie_gem_distance.2]; norm_num
  cut := triangleNetwork.substitute_survives_single_deletion_of_outer twoEdgePathNetwork twoEdgePath_connected (by decide)
  symmetric := by
    refine ⟨triangleTerminalSymmetry.substitute twoEdgePathTerminalSymmetry (by decide) (by decide), ?_, ?_⟩
    · apply NetworkSymmetry.substitute_vertex_involutive
      · intro v; fin_cases v <;> decide
      · intro v; fin_cases v <;> decide
      · intro e; fin_cases e <;> decide
    · exact NetworkSymmetry.substitute_source _ _ _ _ (by decide)

end
end Universality
