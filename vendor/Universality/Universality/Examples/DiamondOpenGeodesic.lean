import Universality.Examples.DiamondRadiusGeometry
import Universality.Graph.SubstitutionConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem substituted_open_walk_length
    (cells : Fin outerEdges → Configuration innerEdges) (length : ℕ)
    (hchild : ∀ edge, S.crosses (cells edge) = true →
      ∃ walk : (S.openGraph (cells edge)).Walk S.source S.target, walk.length = length)
    {u v : Fin outerVertices} (walk : (R.openGraph (S.coarseConfiguration cells)).Walk u v) :
    ∃ lifted : (R.substitutedGraph S cells).Walk (Sum.inl u) (Sum.inl v),
      lifted.length = walk.length * length := by
  have hstep {first second : Fin outerVertices}
      (hadj : (R.openGraph (S.coarseConfiguration cells)).Adj first second) :
      ∃ lifted : (R.substitutedGraph S cells).Walk (Sum.inl first) (Sum.inl second),
        lifted.length = length := by
    obtain ⟨_, edge, hopen, hpair | hpair⟩ := hadj
    · obtain ⟨child, hlength⟩ := hchild edge hopen
      let mapped := child.map (R.cellHom S cells edge)
      have hs : R.cellVertex S edge S.source = Sum.inl first := by rw [R.cellVertex_source, hpair]
      have ht : R.cellVertex S edge S.target = Sum.inl second := by rw [R.cellVertex_target, hpair]
      exact ⟨mapped.copy hs ht, by simpa only [mapped, SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.length_map] using hlength⟩
    · obtain ⟨child, hlength⟩ := hchild edge hopen
      let mapped := child.reverse.map (R.cellHom S cells edge)
      have hs : R.cellVertex S edge S.target = Sum.inl first := by rw [R.cellVertex_target, hpair]
      have ht : R.cellVertex S edge S.source = Sum.inl second := by rw [R.cellVertex_source, hpair]
      exact ⟨mapped.copy hs ht, by simpa only [mapped, SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_reverse] using hlength⟩
  induction walk with
  | nil => exact ⟨.nil, by simp⟩
  | cons hadj walk ih =>
      obtain ⟨first, hfirst⟩ := hstep hadj
      obtain ⟨rest, hrest⟩ := ih
      refine ⟨first.append rest, ?_⟩
      rw [SimpleGraph.Walk.length_append, hfirst, hrest, SimpleGraph.Walk.length_cons]
      ring

theorem substitute_open_geodesic
    (houter : R.fullGraph.Reachable R.source R.target)
    (hinner : S.fullGraph.Reachable S.source S.target)
    (houterGeodesic : ∀ configuration, R.crosses configuration = true →
      ∃ walk : (R.openGraph configuration).Walk R.source R.target,
        walk.length = R.fullGraph.dist R.source R.target)
    (hinnerGeodesic : ∀ configuration, S.crosses configuration = true →
      ∃ walk : (S.openGraph configuration).Walk S.source S.target,
        walk.length = S.fullGraph.dist S.source S.target)
    (configuration : Configuration (outerEdges * innerEdges))
    (hcrossing : (R.substitute S).crosses configuration = true) :
    ∃ walk : ((R.substitute S).openGraph configuration).Walk (R.substitute S).source (R.substitute S).target,
      walk.length = (R.substitute S).fullGraph.dist (R.substitute S).source (R.substitute S).target := by
  obtain ⟨cells, rfl⟩ := substitutionConfigurationEquiv.surjective configuration
  rw [R.substitute_crosses S] at hcrossing
  obtain ⟨coarse, hcoarse⟩ := houterGeodesic _ hcrossing
  obtain ⟨lifted, hlifted⟩ := R.substituted_open_walk_length S cells
    (S.fullGraph.dist S.source S.target) (fun edge => hinnerGeodesic (cells edge)) coarse
  refine ⟨lifted.map (R.substitutionGraphIso S cells).toHom, ?_⟩
  rw [SimpleGraph.Walk.length_map, hlifted, hcoarse, R.substitute_terminal_distance S houter hinner]

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem diamond_crosses_branch (configuration : Configuration 4)
    (hcrossing : diamondNetwork.crosses configuration = true) :
    (configuration 0 = true ∧ configuration 1 = true) ∨
      (configuration 2 = true ∧ configuration 3 = true) := by
  have h : ∀ configuration : Configuration 4, diamondNetwork.crosses configuration = true →
      (configuration 0 = true ∧ configuration 1 = true) ∨
        (configuration 2 = true ∧ configuration 3 = true) := by decide
  exact h configuration hcrossing

theorem diamond_open_geodesic (configuration : Configuration 4)
    (hcrossing : diamondNetwork.crosses configuration = true) :
    ∃ walk : (diamondNetwork.openGraph configuration).Walk diamondNetwork.source diamondNetwork.target,
      walk.length = diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target := by
  rw [diamond_terminal_distance]
  rcases diamond_crosses_branch configuration hcrossing with hfirst | hsecond
  · have hleft : (diamondNetwork.openGraph configuration).Adj 0 2 :=
      ⟨by decide, 0, hfirst.1, Or.inl rfl⟩
    have hright : (diamondNetwork.openGraph configuration).Adj 2 1 :=
      ⟨by decide, 1, hfirst.2, Or.inl rfl⟩
    exact ⟨.cons hleft (.cons hright .nil), rfl⟩
  · have hleft : (diamondNetwork.openGraph configuration).Adj 0 3 :=
      ⟨by decide, 2, hsecond.1, Or.inl rfl⟩
    have hright : (diamondNetwork.openGraph configuration).Adj 3 1 :=
      ⟨by decide, 3, hsecond.2, Or.inl rfl⟩
    exact ⟨.cons hleft (.cons hright .nil), rfl⟩

/-- Every actual open crossing of a finite diamond generation contains
an open ambient terminal geodesic. -/
theorem diamond_generation_open_geodesic (n : ℕ)
    (configuration : Configuration (diamondRule.generation n).edges)
    (hcrossing : (diamondRule.generation n).network.crosses configuration = true) :
    ∃ walk : ((diamondRule.generation n).network.openGraph configuration).Walk
        (diamondRule.generation n).network.source (diamondRule.generation n).network.target,
      walk.length = 2 ^ (n + 1) := by
  induction n with
  | zero =>
      obtain ⟨walk, hwalk⟩ := diamond_open_geodesic configuration hcrossing
      exact ⟨walk, by simpa [diamond_terminal_distance] using hwalk⟩
  | succ n ih =>
      let equivalence := diamondRule.generationTopDecomposition n
      have hcross : (diamondNetwork.substitute (diamondRule.generation n).network).crosses
          (equivalence.configuration configuration) = true := by
        exact (equivalence.crosses configuration).trans hcrossing
      obtain ⟨walk, hwalk⟩ := diamondNetwork.substitute_open_geodesic (diamondRule.generation n).network
        (diamondRule_classical.connected _) ((diamondRule_classical.generation n).connected _)
        diamond_open_geodesic (fun cell hcell => by
          obtain ⟨child, hchild⟩ := ih cell hcell
          exact ⟨child, hchild.trans (diamond_generation_terminal_distance n).symm⟩)
        (equivalence.configuration configuration) hcross
      let mapped := walk.map (equivalence.openGraphIso configuration).symm.toHom
      have hs : equivalence.vertex.symm
          (diamondNetwork.substitute (diamondRule.generation n).network).source =
          (diamondRule.generation (n + 1)).network.source :=
        equivalence.vertex.symm_apply_eq.mpr equivalence.source.symm
      have ht : equivalence.vertex.symm
          (diamondNetwork.substitute (diamondRule.generation n).network).target =
          (diamondRule.generation (n + 1)).network.target :=
        equivalence.vertex.symm_apply_eq.mpr equivalence.target.symm
      refine ⟨mapped.copy hs ht, ?_⟩
      rw [SimpleGraph.Walk.length_copy]
      change (walk.map (equivalence.openGraphIso configuration).symm.toHom).length = _
      rw [SimpleGraph.Walk.length_map, hwalk]
      have hdistance := equivalence.fullGraph_distance
        (diamondRule_classical.generation (n + 1)).connected
        (diamondRule.generation (n + 1)).network.source (diamondRule.generation (n + 1)).network.target
      rw [equivalence.source, equivalence.target] at hdistance
      exact hdistance.trans (diamond_generation_terminal_distance (n + 1))

end
end Universality
