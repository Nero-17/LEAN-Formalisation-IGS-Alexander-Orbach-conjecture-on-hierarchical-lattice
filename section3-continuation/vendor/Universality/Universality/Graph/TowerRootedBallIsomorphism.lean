import Universality.Graph.FiniteStageSupport
namespace Universality
noncomputable section

def RootedGraphIsomorphic {Vertex OtherVertex : Type*} (graph : SimpleGraph Vertex)
    (root : Vertex) (otherGraph : SimpleGraph OtherVertex) (otherRoot : OtherVertex) : Prop :=
  ∃ isomorphism : graph ≃g otherGraph, isomorphism root = otherRoot

theorem rootedGraphIsomorphic_iff {First Second Target : Type*}
    {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second}
    (targetGraph : SimpleGraph Target) {firstRoot : First} {secondRoot : Second}
    (targetRoot : Target) (isomorphism : firstGraph ≃g secondGraph)
    (hroot : isomorphism firstRoot = secondRoot) :
    RootedGraphIsomorphic firstGraph firstRoot targetGraph targetRoot ↔
      RootedGraphIsomorphic secondGraph secondRoot targetGraph targetRoot := by
  constructor
  · rintro ⟨toTarget, htarget⟩
    refine ⟨isomorphism.symm.trans toTarget, ?_⟩
    change toTarget (isomorphism.symm secondRoot) = targetRoot
    rw [← hroot, isomorphism.symm_apply_apply]
    exact htarget
  · rintro ⟨toTarget, htarget⟩
    refine ⟨isomorphism.trans toTarget, ?_⟩
    change toTarget (isomorphism firstRoot) = targetRoot
    rw [hroot]
    exact htarget

end
end Universality

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

def ambientBall (tower : NetworkTower) (root : Fin (tower.stage 0).vertices)
    (radius : ℕ) : Set tower.Vertex :=
  {vertex | (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) vertex ≤ radius}

def stageAmbientBall (tower : NetworkTower) (root : Fin (tower.stage 0).vertices)
    (radius n : ℕ) : Set (Fin (tower.stage n).vertices) :=
  {vertex | (tower.stage n).network.fullGraph.dist
    (tower.vertexMap 0 n (Nat.zero_le n) root) vertex ≤ radius}

def ambientBallRoot (tower : NetworkTower) (root : Fin (tower.stage 0).vertices)
    (radius : ℕ) : tower.ambientBall root radius :=
  ⟨tower.vertex 0 root, by simp [ambientBall]⟩

def stageAmbientBallRoot (tower : NetworkTower) (root : Fin (tower.stage 0).vertices)
    (radius n : ℕ) : tower.stageAmbientBall root radius n :=
  ⟨tower.vertexMap 0 n (Nat.zero_le n) root, by simp [stageAmbientBall]⟩

theorem fullGraph_root_distance (tower : NetworkTower) (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (root : Fin (tower.stage 0).vertices) (n : ℕ) (vertex : Fin (tower.stage n).vertices) :
    (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root) (tower.vertex n vertex) =
      (tower.stage n).network.fullGraph.dist (tower.vertexMap 0 n (Nat.zero_le n) root) vertex := by
  rw [← tower.vertex_map 0 n (Nat.zero_le n) root]
  exact tower.fullGraph_distance hisometry n _ vertex
    ((hconnected n _).symm.trans (hconnected n vertex))

theorem ambientBall_finite (tower : NetworkTower)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (hfinite : ∀ vertex, ((tower.openGraph (fun _ => true)).neighborSet vertex).Finite)
    (root : Fin (tower.stage 0).vertices) (radius : ℕ) :
    (tower.ambientBall root radius).Finite := by
  have hball := boundedWalkBall_finite (tower.openGraph (fun _ => true)) hfinite
    (tower.vertex 0 root) radius
  rw [boundedWalkBall_eq_distBall _ _ (tower.fullGraph_reachable hconnected _) radius] at hball
  exact hball

/-- Every fixed-radius rooted induced ball, with its actual open-edge graph,
is eventually exactly the corresponding finite-stage rooted ball. -/
theorem eventually_rootedBall_isomorphism (tower : NetworkTower)
    (hisometry : tower.IsometricSteps)
    (hconnected : ∀ n, ∀ vertex, (tower.stage n).network.fullGraph.Reachable
      (tower.stage n).network.source vertex)
    (hfinite : ∀ vertex, ((tower.openGraph (fun _ => true)).neighborSet vertex).Finite)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (radius : ℕ) :
    ∀ᶠ n in atTop,
      ∃ isomorphism : (((tower.stage n).network.openGraph
          (tower.restrictConfiguration configuration n)).induce
            (tower.stageAmbientBall root radius n)) ≃g
          (tower.openGraph configuration).induce (tower.ambientBall root radius),
        isomorphism (tower.stageAmbientBallRoot root radius n) = tower.ambientBallRoot root radius := by
  classical
  have hball := tower.ambientBall_finite hconnected hfinite root radius
  obtain ⟨first, hfirst⟩ := tower.finite_set_in_every_later_stage hball
  filter_upwards [eventually_ge_atTop first, tower.finite_set_adjacency_stabilizes configuration hball]
    with n hn hadjacency
  let vertexMap : tower.stageAmbientBall root radius n → tower.ambientBall root radius :=
    fun vertex => ⟨tower.vertex n vertex.val, by
      change (tower.openGraph (fun _ => true)).dist (tower.vertex 0 root)
        (tower.vertex n vertex.val) ≤ radius
      rw [tower.fullGraph_root_distance hisometry hconnected]
      exact vertex.property⟩
  have hinjective : Function.Injective vertexMap := by
    intro first last heq
    apply Subtype.ext
    exact tower.vertex_injective n (congrArg Subtype.val heq)
  have hsurjective : Function.Surjective vertexMap := by
    intro vertex
    obtain ⟨inside, hinside⟩ := hfirst n hn vertex.val vertex.property
    have hballInside : inside ∈ tower.stageAmbientBall root radius n := by
      change (tower.stage n).network.fullGraph.dist
        (tower.vertexMap 0 n (Nat.zero_le n) root) inside ≤ radius
      rw [← tower.fullGraph_root_distance hisometry hconnected, hinside]
      exact vertex.property
    exact ⟨⟨inside, hballInside⟩, Subtype.ext hinside⟩
  let isomorphism : (((tower.stage n).network.openGraph
      (tower.restrictConfiguration configuration n)).induce
        (tower.stageAmbientBall root radius n)) ≃g
      (tower.openGraph configuration).induce (tower.ambientBall root radius) :=
    { toEquiv := Equiv.ofBijective vertexMap ⟨hinjective, hsurjective⟩
      map_rel_iff' := by
        intro first last
        change (tower.openGraph configuration).Adj (tower.vertex n first.val) (tower.vertex n last.val) ↔
          ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Adj first.val last.val
        exact hadjacency first.val last.val (vertexMap first).property (vertexMap last).property }
  refine ⟨isomorphism, ?_⟩
  apply Subtype.ext
  exact tower.vertex_map 0 n (Nat.zero_le n) root

end
end Universality.NetworkTower
