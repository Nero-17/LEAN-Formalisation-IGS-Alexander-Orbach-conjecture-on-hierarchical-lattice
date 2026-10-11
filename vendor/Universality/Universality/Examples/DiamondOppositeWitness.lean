import Universality.Examples.DiamondBranchDistance
import Universality.Examples.DiamondOpenGeodesic

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem open_geodesic_has_every_layer (configuration : Configuration edges)
    (walk : (R.openGraph configuration).Walk R.source R.target)
    (hlength : walk.length = R.fullGraph.dist R.source R.target)
    (layer : ℕ) (hlayer : layer ≤ walk.length) :
    ∃ vertex ∈ walk.support, R.fullGraph.dist R.source vertex = layer := by
  have hle : R.openGraph configuration ≤ R.fullGraph := by
    intro u v hadj
    obtain ⟨hne, edge, _, hpair⟩ := hadj
    exact ⟨hne, edge, rfl, hpair⟩
  let ambient := walk.mapLe hle
  have hambientLength : ambient.length = R.fullGraph.dist R.source R.target := by
    simpa only [ambient, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map] using hlength
  refine ⟨ambient.getVert layer, ?_, R.shortest_walk_source_distance ambient hambientLength layer ?_⟩
  · have hmem := ambient.getVert_mem_support layer
    simpa only [ambient, SimpleGraph.Walk.support_mapLe_eq_support] using hmem
  · simpa only [ambient, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.length_map] using hlayer

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {innerVertices innerEdges : ℕ} (S : FiniteNetwork innerVertices innerEdges)

theorem diamondBranch_cell (edge : Fin 4) (vertex : Fin innerVertices)
    (hsource : diamondNetwork.cellEmbedding S edge vertex ≠ (diamondNetwork.substitute S).source)
    (htarget : diamondNetwork.cellEmbedding S edge vertex ≠ (diamondNetwork.substitute S).target) :
    diamondBranch S (diamondNetwork.cellEmbedding S edge vertex) = decide (2 ≤ edge.val) := by
  have hs : diamondNetwork.cellVertex S edge vertex ≠ Sum.inl diamondNetwork.source :=
    fun heq => hsource (congrArg (Fintype.equivFin (diamondNetwork.SubstitutionVertex S)) heq)
  have ht : diamondNetwork.cellVertex S edge vertex ≠ Sum.inl diamondNetwork.target :=
    fun heq => htarget (congrArg (Fintype.equivFin (diamondNetwork.SubstitutionVertex S)) heq)
  change diamondSubstitutionBranch S
    ((Fintype.equivFin (diamondNetwork.SubstitutionVertex S)).symm
      (Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S edge vertex))) = _
  rw [Equiv.symm_apply_apply]
  exact diamondSubstitutionBranch_cell S edge vertex hs ht

/-- If the two right-branch child cells have open terminal geodesics,
their concatenation is an open geodesic entirely in that parallel branch. -/
theorem diamond_right_branch_open_geodesic
    (cells : Fin 4 → Configuration innerEdges)
    (first : (S.openGraph (cells 2)).Walk S.source S.target)
    (second : (S.openGraph (cells 3)).Walk S.source S.target)
    (hfirst : first.length = S.fullGraph.dist S.source S.target)
    (hsecond : second.length = S.fullGraph.dist S.source S.target) :
    ∃ walk : ((diamondNetwork.substitute S).openGraph (substitutionConfigurationEquiv cells)).Walk
        (diamondNetwork.substitute S).source (diamondNetwork.substitute S).target,
      walk.length = 2 * S.fullGraph.dist S.source S.target ∧
      ∀ vertex ∈ walk.support, vertex ≠ (diamondNetwork.substitute S).source →
        vertex ≠ (diamondNetwork.substitute S).target → diamondBranch S vertex = true := by
  let cellMap (edge : Fin 4) : S.openGraph (cells edge) →g
      (diamondNetwork.substitute S).openGraph (substitutionConfigurationEquiv cells) :=
    (diamondNetwork.substitutionGraphIso S cells).toHom.comp (diamondNetwork.cellHom S cells edge)
  have hmap (edge : Fin 4) (vertex : Fin innerVertices) :
      cellMap edge vertex = diamondNetwork.cellEmbedding S edge vertex := rfl
  have hstart : cellMap 2 S.source = (diamondNetwork.substitute S).source := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 2 S.source) = _
    rw [diamondNetwork.cellVertex_source]
    rfl
  have hmiddle : cellMap 2 S.target = cellMap 3 S.source := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 2 S.target) =
      Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 3 S.source)
    rw [diamondNetwork.cellVertex_target, diamondNetwork.cellVertex_source]
    rfl
  have hend : cellMap 3 S.target = (diamondNetwork.substitute S).target := by
    change Fintype.equivFin (diamondNetwork.SubstitutionVertex S) (diamondNetwork.cellVertex S 3 S.target) = _
    rw [diamondNetwork.cellVertex_target]
    rfl
  let left := (first.map (cellMap 2)).copy hstart hmiddle
  let right := (second.map (cellMap 3)).copy rfl hend
  refine ⟨left.append right, ?_, ?_⟩
  · simp only [left, right, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_map, hfirst, hsecond]
    omega
  · intro vertex hvertex hs ht
    simp only [left, right, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hvertex
    rcases hvertex with ⟨inside, _, rfl⟩ | ⟨inside, _, rfl⟩
    · rw [hmap] at hs ht ⊢
      simpa using diamondBranch_cell S 2 inside hs ht
    · rw [hmap] at hs ht ⊢
      simpa using diamondBranch_cell S 3 inside hs ht

/-- A right-branch open geodesic provides every nonterminal ambient
layer on that branch, with actual open connectivity to the source. -/
theorem diamond_right_branch_has_every_layer
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (cells : Fin 4 → Configuration innerEdges)
    (first : (S.openGraph (cells 2)).Walk S.source S.target)
    (second : (S.openGraph (cells 3)).Walk S.source S.target)
    (hfirst : first.length = S.fullGraph.dist S.source S.target)
    (hsecond : second.length = S.fullGraph.dist S.source S.target)
    (layer : ℕ) (hpositive : 0 < layer) (hless : layer < 2 * S.fullGraph.dist S.source S.target) :
    ∃ vertex, ((diamondNetwork.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
        (diamondNetwork.substitute S).source vertex ∧ diamondBranch S vertex = true ∧
      (diamondNetwork.substitute S).fullGraph.dist (diamondNetwork.substitute S).source vertex = layer := by
  obtain ⟨walk, hlength, hbranch⟩ := diamond_right_branch_open_geodesic S cells first second hfirst hsecond
  have hterminal : (diamondNetwork.substitute S).fullGraph.dist
      (diamondNetwork.substitute S).source (diamondNetwork.substitute S).target =
      2 * S.fullGraph.dist S.source S.target := by
    rw [diamondNetwork.substitute_terminal_distance S (diamondRule_classical.connected _) (hinner _),
      diamond_terminal_distance]
  obtain ⟨vertex, hvertex, hdistance⟩ := (diamondNetwork.substitute S).open_geodesic_has_every_layer
    (substitutionConfigurationEquiv cells) walk (hlength.trans hterminal.symm) layer (by omega)
  refine ⟨vertex, ⟨walk.takeUntil vertex hvertex⟩, hbranch vertex hvertex ?_ ?_, hdistance⟩
  · intro heq
    rw [heq, SimpleGraph.dist_self] at hdistance
    omega
  · intro heq
    rw [heq, hterminal] at hdistance
    omega

end
end Universality



